package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;

// Allocates a TypeStruct and produces a Tuple with the TypeStruct and a TypeMemPtr.
//
// During Parsing we construct closures whose field names are discovered as we
// parse.  Hence we support a type which represents some concrete fields, and a
// choice of all possible remaining fields.  The _any choice means we can add
// fields, although the closure remains impossibly high until the lexical scope
// ends and no more fields can appear.

public class NewObjNode extends NewNode<TypeStruct> {
  public final boolean _is_closure; // For error messages
  // NewNodes do not really need a ctrl; useful to bind the upward motion of
  // closures so variable stores can more easily fold into them.
  public NewObjNode( boolean is_closure, Node ctrl, Node clo ) {
    this(is_closure, BitsAlias.RECORD, TypeStruct.DISPLAY,ctrl,clo);
  }
  // Called by IntrinsicNode.convertTypeNameStruct
  public NewObjNode( boolean is_closure, int par_alias, TypeStruct ts, Node ctrl, Node clo ) {
    super(OP_NEWOBJ,par_alias,ts,ctrl,clo);
    _is_closure = is_closure;
  }
  public Node get(String name) { int idx = _ts.find(name);  assert idx >= 0; return fld(idx); }
  public boolean exists(String name) { return _ts.find(name)!=-1; }
  public boolean is_mutable(String name) { return _ts.fmod(_ts.find(name)) == TypeStruct.FRW; }

  // Create a field from parser for an inactive this
  public void create( String name, Node val, byte mutable, GVNGCM gvn  ) {
    assert !Util.eq(name,"^"); // Closure field created on init
    gvn.unreg(this);
    create_active(name,val,mutable,gvn);
    for( Node use : _uses )
      gvn.setype(use,use.value(gvn));
    assert gvn.touched(this);
  }

  // Create a field from parser for an active this
  public void create_active( String name, Node val, byte mutable, GVNGCM gvn  ) {
    assert !gvn.touched(this);
    assert def_idx(_ts._ts.length)== _defs._len;
    assert _ts.find(name) == -1; // No dups
    _ts = _ts.add_fld(name,Type.SCALAR,mutable);
    add_def(val);
  }
  public void update( String tok, byte mutable, Node val, GVNGCM gvn  ) { update(_ts.find(tok),mutable,val,gvn); }
  // Update the field & mod
  public void update( int fidx, byte mutable, Node val, GVNGCM gvn  ) {
    gvn.unreg(this);
    boolean can_update = update_active(fidx,mutable,val,gvn);
    gvn.rereg(this,value(gvn));
    // As part of the local xform rule, the memory & ptr outputs of the NewNode
    // need to update their types directly.  The NewNode mutable bit can be set
    // to final - which strictly runs downhill.  However, iter() calls must
    // strictly run uphill, so we have to expand the changed region to cover
    // all the "downhilled" parts and "downhill" them to match.  Outside of the
    // "downhilled" region, the types are unchanged.
    if( !can_update )
      for( Node use : _uses ) {
        gvn.setype(use,use.value(gvn)); // Record "downhill" type for OProj, DProj
        gvn.add_work_uses(use);         // Neighbors on worklist
      }
  }
  public boolean update_active( int fidx, byte mutable, Node val, GVNGCM gvn  ) {
    assert !gvn.touched(this);
    assert def_idx(_ts._ts.length)== _defs._len;
    boolean can_update = _ts.can_update(fidx);
    if( _ts.fmod(fidx) != mutable ) // Changed field modifier
      _ts = _ts.set_fld(fidx,_ts.at(fidx),mutable);
    set_def(def_idx(fidx),val,gvn);
    return can_update;
  }


  // Add a named FunPtr to a New.  Auto-inflates to a Unresolved as needed.
  public FunPtrNode add_fun( Parse bad, String name, FunPtrNode ptr, GVNGCM gvn ) {
    int fidx = _ts.find(name);
    if( fidx == -1 ) {
      create_active(name,ptr,TypeStruct.FFNL,gvn);
    } else {
      Node n = _defs.at(def_idx(fidx));
      if( n instanceof UnresolvedNode ) n.add_def(ptr);
      else n = new UnresolvedNode(bad,n,ptr);
      update_active(fidx,TypeStruct.FFNL,n,gvn);
    }
    return ptr;
  }

  // The current local scope ends, no more names will appear.  Forward refs
  // first found in this scope are assumed to be defined in some outer scope
  // and get promoted.  Other locals are no longer kept alive, but live or die
  // according to use.
  public void promote_forward(GVNGCM gvn, NewObjNode parent) {
    assert parent != null;
    boolean progress=false;
    TypeStruct ts = _ts;
    for( int i=0; i<ts._ts.length; i++ ) {
      Node n = fld(i);
      if( n != null && n.is_forward_ref() ) {
        if( !progress ) { progress=true; gvn.unreg(this); }
        parent.create(ts._flds[i],n,ts.flags(i),gvn);
        remove(def_idx(i),gvn);  // Hack edge
        ts = ts.del_fld(i);
        i--;
      }
    }
    // Promoted anything?
    if( progress ) {
      _ts = ts;
      // Reset types on this and children, so show the removed extra field
      gvn.rereg(this,value(gvn));
      for( Node use : _uses ) {
        gvn.setype(use,use.value(gvn)); // Record "downhill" type for OProj, DProj
        gvn.add_work_uses(use);         // Neighbors on worklist
      }
    }
  }

  @Override public Type value(GVNGCM gvn) {
    // If the address is not looked at then memory contents cannot be looked at
    // and is dead.  Since this can happen DURING opto (when a call resolves)
    // and during iter, "freeze" the value in-place.  It will DCE shortly.
    if( _captured )
      return gvn.self_type(this);

    // Gather args and produce a TypeStruct
    Type[] ts = TypeAry.get(_ts._ts.length);
    for( int i=0; i<ts.length; i++ )
      // Limit type bounds, since error returns can be out-of-bounds
      ts[i] = gvn.type(fld(i)).bound(_ts.at(i));
    TypeStruct newt = _ts.make_from(ts);

    // Check for TypeStructs with this same NewNode types occurring more than
    // CUTOFF deep, and fold the deepest ones onto themselves to limit the type
    // depth.  If this happens, the types become recursive with the
    // approximations happening at the deepest points.
    TypeStruct xs = newt.approx(CUTOFF,_alias);
    assert Util.eq(xs._name,_ts._name);
    return TypeTuple.make(xs,TypeMemPtr.make(_alias,xs));
  }
}
