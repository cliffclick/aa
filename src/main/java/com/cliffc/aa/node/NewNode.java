package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Make a new object of given type.  Returns both the pointer and the TypeObj
// but NOT the memory state.
public class NewNode extends Node {
  // Unique alias class, one class per unique memory allocation site.
  // Only effectively-final, because the copy/clone sets a new alias value.
  private int _alias;           // Alias class
  private TypeMemPtr _ptr;      // Cache of TypeMemPtr(_alias)
  private TypeObj _obj;         // Result type - same as _ts except can be named
  private TypeStruct _ts;       // Allocate a struct
  
  public NewNode( Node[] flds, TypeObj obj ) {
    super(OP_NEW,flds);
    assert flds[0]==null;       // no ctrl field
    _obj = obj;
    _ts = (TypeStruct)obj.base();
    _alias = BitsAlias.new_alias(BitsAlias.REC,obj);
    _ptr = TypeMemPtr.make(_alias);
  }
  private int def_idx(int fld) { return fld+1; }
  private Node fld(int fld) { return in(def_idx(fld)); }
  // Called when folding a Named Constructor into this allocation site
  void set_name( TypeName to ) {
    assert to.base().isa(_ts);
    _obj = to;
    _ts = (TypeStruct)to.base();
  }
  String xstr() { return "New#"+_alias; } // Self short name
  String  str() { return xstr(); } // Inline short name
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) {
    Type[] ts = new Type[_ts._ts.length];
    for( int i=0; i<_ts._ts.length; i++ )
      ts[i] = gvn.type(fld(i)).bound(_ts._ts[i]); // Limit to Scalar results
    TypeStruct newt = TypeStruct.make(_ts._flds,ts,_ts._finals);
    // Get the existing type, without installing if missing because blows the
    // "new newnode" assert if this node gets replaced during parsing.
    Type oldnnn = gvn.self_type(this);
    Type oldt= oldnnn instanceof TypeTuple ? ((TypeTuple)oldnnn).at(0) : newt;
    TypeStruct apxt= approx(newt,oldt); // Approximate infinite types
    if( _obj instanceof TypeName )      // Re-wrap in a name
      return TypeTuple.make(((TypeName)_obj).make(apxt),_ptr);
    return TypeTuple.make(apxt,_ptr);
  }
  
  // NewNodes can participate in cycles, where the same structure is appended
  // to in a loop until the size grows without bound.  If we detect this we
  // need to approximate a new cyclic type.
  private final static int CUTOFF=5; // Depth of types before we start forcing approximations
  private static TypeStruct approx( TypeStruct newt, Type oldt ) {
    if( !(oldt instanceof TypeStruct) ) return newt;
    if( newt == oldt ) return newt;
    if( !newt.contains(oldt) ) return newt;
    if( oldt.depth() <= CUTOFF ) return newt;
    TypeStruct tsa = newt.approx((TypeStruct)oldt);
    return (TypeStruct)(tsa.meet(oldt));
  }

  @Override public Type all_type() { return TypeTuple.make(_obj,_ptr); }
  
  // Clones during inlining all become unique new sites
  @Override NewNode copy(GVNGCM gvn) {
    NewNode nnn = (NewNode)super.copy(gvn);
    nnn._alias = BitsAlias.new_alias(_alias,_ts); // Children alias classes, split from parent
    nnn._ptr = TypeMemPtr.make(nnn._alias);
    return nnn;
  }

  @Override public int hashCode() { return super.hashCode()+ _ts._hash + _alias; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof NewNode) ) return false;
    NewNode nnn = (NewNode)o;
    return _alias==nnn._alias && _ts==nnn._ts;
  }
}
