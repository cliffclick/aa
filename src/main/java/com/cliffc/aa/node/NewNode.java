package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Make a new object of given type.  Returns both the pointer and the TypeObj
// but NOT the memory state.
public class NewNode extends Node {
  // Unique alias class, one class per unique memory allocation site.
  // Only effectively-final, because the copy/clone sets a new alias value.
  private int _alias;           // Alias class
  private TypeStruct _ts;       // Result struct (may be named)
  private TypeObj _obj;         // Optional named struct
  TypeMemPtr _ptr;              // Cached pointer-to-_obj

  public NewNode( Node[] flds, TypeObj obj ) {
    super(OP_NEW,flds);
    assert flds[0]==null;       // no ctrl field
    _alias = BitsAlias.new_alias(BitsAlias.REC);
    _ts = (TypeStruct)obj.base();
    _obj = obj;
    _ptr = TypeMemPtr.make(_alias,_obj);
  }
  private int def_idx(int fld) { return fld+1; }
  private Node fld(int fld) { return in(def_idx(fld)); }
  // Called when folding a Named Constructor into this allocation site
  void set_name( GVNGCM gvn, TypeName to ) {
    assert to.base().isa(_ts); // Cannot change the target fields, just the name
    Type oldt = gvn.type(this);
    gvn.unreg(this);
    _ts = (TypeStruct)to.base();
    _obj = to;
    _ptr = TypeMemPtr.make(_alias,to);
    if( !(oldt instanceof TypeMemPtr) )  throw com.cliffc.aa.AA.unimpl();
    TypeMemPtr nameptr = _ptr.make(to.make(((TypeMemPtr)oldt)._obj));
    gvn.rereg(this,nameptr);
  }
  String xstr() { return "New*"+_alias; } // Self short name
  String  str() { return "New"+_ptr; } // Inline less-short name
  @Override public Node ideal(GVNGCM gvn) { return null; }
  // Produces a TypeMemPtr
  @Override public Type value(GVNGCM gvn) {
    // Gather args and produce a TypeStruct
    Type[] ts = new Type[_ts._ts.length];
    for( int i=0; i<_ts._ts.length; i++ )
      ts[i] = gvn.type(fld(i)).bound(_ts._ts[i]); // Limit to Scalar results
    TypeStruct newt = TypeStruct.make(_ts._flds,ts,_ts._finals);

    // Get the existing type, without installing if missing because blows the
    // "new NewNode" assert if this node gets replaced during parsing.
    Type oldnnn = gvn.self_type(this);
    TypeObj oldt = oldnnn ==null ? newt : ((TypeMemPtr)oldnnn)._obj;
    TypeStruct apxt= approx(newt,oldt); // Approximate infinite types
    TypeObj res = _obj instanceof TypeName ? ((TypeName)_obj).make(apxt) : apxt;
    return TypeMemPtr.make(_alias,res);
  }

  // NewNodes can participate in cycles, where the same structure is appended
  // to in a loop until the size grows without bound.  If we detect this we
  // need to approximate a new cyclic type.
  private final static int CUTOFF=5; // Depth of types before we start forcing approximations
  public static TypeStruct approx( TypeStruct newt, TypeObj oldt ) {
    if( !(oldt instanceof TypeStruct) ) return newt;
    if( newt == oldt ) return newt;
    if( !newt.contains(oldt) ) return newt;
    if( oldt.depth() <= CUTOFF ) return newt;
    TypeStruct tsa = newt.approx((TypeStruct)oldt);
    return (TypeStruct)(tsa.meet(oldt));
  }

  @Override public Type all_type() { return _ptr; }

  // Clones during inlining all become unique new sites
  @Override NewNode copy(GVNGCM gvn) {
    NewNode nnn = (NewNode)super.copy(gvn);
    nnn._alias = BitsAlias.new_alias(_alias); // Children alias classes, split from parent
    nnn._ptr = TypeMemPtr.make(nnn._alias,_obj);
    return nnn;
  }

  @Override public int hashCode() { return super.hashCode()+ _ptr._hash; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof NewNode) ) return false;
    NewNode nnn = (NewNode)o;
    return _ptr==nnn._ptr;
  }
}
