package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

// Allocates a TypeStruct and produces a Tuple with the TypeStruct and a TypeMemPtr.
//
// During Parsing we construct closures whose field names are discovered as we
// parse.  Hence we support a type which represents some concrete fields, and a
// choice of all possible remaining fields.  The _any choice means we can add
// fields, although the closure remains impossibly high until the lexical scope
// ends and no more fields can appear.

public class NewObjNode extends NewNode<TypeStruct> {
  boolean _is_closure;        // For error messages
  // NewNodes do not really need a ctrl; useful to bind the upward motion of
  // closures so variable stores can more easily fold into them.
  public NewObjNode( boolean is_closure, Node ctrl ) {
    super(OP_NEWOBJ,BitsAlias.REC,TypeStruct.ALLSTRUCT,ctrl);
    _is_closure = is_closure;
  }
  public Node get(String name) { return fld(_ts.find(name)); }
  public boolean exists(String name) { return _ts.find(name)!=-1; }
  public boolean is_mutable(String name) { return _ts._finals[_ts.find(name)] == TypeStruct.frw(); }
  public boolean is_final(int idx) { return _ts._finals[idx] == TypeStruct.ffinal(); }

  // Called when folding a Named Constructor into this allocation site
  void set_name( GVNGCM gvn, TypeName name ) {
    assert !name.above_center();
    // Name is a wrapper over _ts, except for alias because Name is probably a generic type.
    TypeName n2 = name.make(xs());
    assert n2._t == xs();       // wrapping exactly once
    if( gvn.touched(this) ) {
      gvn.unreg(this);
      _name = n2;
      gvn.rereg(this,value(gvn));
    } else {
      _name = n2;
    }
  }

  // Create a field from parser for an inactive this
  public void create( String name, Node val, byte mutable, GVNGCM gvn  ) {
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
    _ts = _ts.add_fld(name,gvn.type(val),mutable);
    if( _name != null ) _name = _name.make(_ts); // Re-attach name as needed
    add_def(val);
  }
  // Update/modify a field, by field number
  public Node update( int fidx , Node val, byte mutable, GVNGCM gvn  ) {
    Type oldt = gvn.unreg(this);
    update_active(fidx,val,mutable,gvn);
    gvn.rereg(this,oldt);
    return val;
  }
  // Update/modify a field, by field number for an active this
  private void update_active( int fidx , Node val, byte mutable, GVNGCM gvn  ) {
    assert def_idx(_ts._ts.length)== _defs._len;
    assert fidx != -1;
    _ts = _ts.set_fld(fidx,gvn.type(val),mutable);
    if( _name != null ) _name = _name.make(_ts); // Re-attach name as needed
    set_def(def_idx(fidx),val,gvn);
  }

  // Add a named FunPtr to a New.  Auto-inflates to a Unresolved as needed.
  public FunPtrNode add_fun( Parse bad, String name, FunPtrNode ptr, GVNGCM gvn ) {
    int fidx = _ts.find(name);
    if( fidx == -1 ) {
      create_active(name,ptr,TypeStruct.ffinal(),gvn);
    } else {
      Node n = _defs.at(def_idx(fidx));
      if( n instanceof UnresolvedNode ) n.add_def(ptr);
      else n = new UnresolvedNode(bad,n,ptr);
      update_active(fidx,n,TypeStruct.ffinal(),gvn);
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
        parent.create(ts._flds[i],n,ts._finals[i],gvn);
        gvn.remove_reg(this,def_idx(i));
        ts = ts.del_fld(i);
        i--;
      }
    }
    if( ts != _ts && _name != null ) _name = _name.make(ts); // Re-attach name as needed
    _ts = ts;
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
    TypeStruct newt = TypeStruct.make(_ts._flds,ts,_ts._finals);

    TypeObj xs = _name == null ? newt : _name.make(newt); // Re-attach name as needed
    return TypeTuple.make(xs,TypeMemPtr.make(_alias));
  }
}
