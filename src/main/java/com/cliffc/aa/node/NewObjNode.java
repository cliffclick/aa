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
// fields, although the closure remains impossibly low until the lexical scope
// ends and no more fields can appear.

public class NewObjNode extends NewNode<TypeStruct> {
  public final boolean _is_closure; // For error messages
  public       Parse[] _fld_starts; // Start of each tuple member; 0 for the display
  // NewNodes do not really need a ctrl; useful to bind the upward motion of
  // closures so variable stores can more easily fold into them.
  public NewObjNode( boolean is_closure, TypeStruct disp, Node ctrl, Node clo ) {
    this(is_closure, BitsAlias.RECORD, disp, ctrl,clo);
  }
  // Called by IntrinsicNode.convertTypeNameStruct
  public NewObjNode( boolean is_closure, int par_alias, TypeStruct ts, Node ctrl, Node clo ) {
    super(OP_NEWOBJ,par_alias,ts,ctrl,clo);
    _is_closure = is_closure;
    assert ts._ts[0].is_display_ptr();
    for( int i=1; i<ts._ts.length; i++ )
      assert ts._ts[i]==Type.SCALAR || ts.fmod(i)==TypeStruct.FFNL; // Field contents not specified unless final
  }
  public Node get(String name) { int idx = _ts.find(name);  assert idx >= 0; return fld(idx); }
  public boolean exists(String name) { return _ts.find(name)!=-1; }
  public boolean is_mutable(String name) {
    byte fmod = _ts.fmod(_ts.find(name));
    return fmod == TypeStruct.FRW;
  }
  public TypeMemPtr tptr() { return TypeMemPtr.make(_alias,_ts); }

  // Create a field from parser for an inactive this
  public void create( String name, Node val, byte mutable, GVNGCM gvn  ) {
    assert !Util.eq(name,"^"); // Closure field created on init
    gvn.unreg(this);
    create_active(name,val,mutable,gvn);
    gvn.rereg(this,value(gvn)); // Re-insert with field added
    for( Node use : _uses ) {
      gvn.setype(use,use.value(gvn)); // Record "downhill" type for OProj, DProj
      gvn.add_work_uses(use);         // Neighbors on worklist
    }
    assert gvn.touched(this);
  }

  // Create a field from parser for an active this
  public void create_active( String name, Node val, byte mutable, GVNGCM gvn  ) {
    assert !gvn.touched(this);
    assert def_idx(_ts._ts.length)== _defs._len;
    assert _ts.find(name) == -1; // No dups
    sets(_ts.add_fld(name,mutable,mutable==TypeStruct.FFNL ? gvn.type(val) : Type.SCALAR),gvn);
    add_def(val);
  }
  public void update( String tok, byte mutable, Node val, GVNGCM gvn  ) { update(_ts.find(tok),mutable,val,gvn); }
  // Update the field & mod
  public void update( int fidx, byte mutable, Node val, GVNGCM gvn  ) {
    Type oldt = gvn.unreg(this);
    update_active(fidx,mutable,val,gvn);
    Type newt = value(gvn);
    gvn.rereg(this,newt);
    // As part of the local xform rule, the memory & ptr outputs of the NewNode
    // need to update their types directly.  This is a sideways (or perhaps
    // downhill) move of the NewNode type - which must run strictly uphill
    // during iter().  Calling update() here assumes that the type being
    // replaced has not "escaped" past the immediate OProj/Proj.  Hence it is
    // safe to "move them sideways" without blowing the always-uphill
    // invariant.  This is generally only true in the Parser, making this a
    // small parse-time optimization.
    if( newt!=oldt )
      for( Node use : _uses )
        gvn.setype(use,use.value(gvn)); // Record "downhill" type for OProj, DProj
  }
  // Update default value.  Used by StoreNode folding into a NewObj initial
  // state.  Used by the Parser when updating local variables... basically
  // another store.
  public void update_active( int fidx, byte mutable, Node val, GVNGCM gvn  ) {
    assert !gvn.touched(this);
    assert def_idx(_ts._ts.length)== _defs._len;
    sets(_ts.set_fld(fidx,mutable==TypeStruct.FFNL ? gvn.type(val) : Type.SCALAR,mutable),gvn);
    set_def(def_idx(fidx),val,gvn);
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
      gvn.setype(n,n.value(gvn)); // Update the input type, so the _ts field updates
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
    TypeStruct ts = _ts;
    for( int i=0; i<ts._ts.length; i++ ) {
      Node n = fld(i);
      if( n != null && n.is_forward_ref() ) {
        // Make field in the parent
        parent.create(ts._flds[i],n,ts.fmod(i),gvn);
        // Stomp field locally to XSCALAR
        sets(_ts.set_fld(i,Type.XSCALAR,TypeStruct.FFNL),gvn);
        gvn.set_def_reg(this,def_idx(i),gvn.con(Type.XSCALAR));
      }
    }
  }

  @Override public Type value(GVNGCM gvn) {
    if( DefMemNode.CAPTURED.get(_alias) ) // Captured/dead
      return TypeTuple.make(TypeObj.UNUSED,TypeMemPtr.make(_alias,TypeObj.OBJ));
    // Gather args and produce a TypeStruct
    Type[] ts = TypeAry.get(_ts._ts.length);
    for( int i=0; i<ts.length; i++ )
      ts[i] = gvn.type(fld(i)).join(_ts._ts[i]);
    TypeStruct newt = _ts.make_from(ts);
    return TypeTuple.make(newt,TypeMemPtr.make(_alias,TypeObj.OBJ)); // Complex obj, simple ptr.
  }
  @Override public Type all_type() {
    if( DefMemNode.CAPTURED.get(_alias) ) // Captured/dead
      return TypeTuple.make(TypeObj.UNUSED,TypeMemPtr.make(_alias,TypeObj.OBJ));
    return TypeTuple.NEWOBJ;
  }
}
