package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

// Store a value into a named struct field.  Does it's own nil-check and value
// testing; also checks final field updates.
public class StoreNode extends Node {
  private final String _fld;
  private final int _fld_num;
  private final String _badfld;
  private final String _badnil;
  private final String _badfin;
  private StoreNode( Node ctrl, Node st, String fld, int fld_num, Parse bad ) {
    super(OP_STORE,ctrl,st);
    _fld = fld;
    _fld_num = fld_num;
    // Tests can pass a null, but nobody else does
    _badfld = bad==null ? null : bad.errMsg("Unknown field '."+fld+"'");
    _badnil = bad==null ? null : bad.errMsg("Struct might be nil when writing field '."+fld+"'");
    _badfin = bad==null ? null : bad.errMsg("Cannot re-assign final field '."+fld+"'");
  }
  public StoreNode( Node ctrl, Node st, String fld , Parse bad ) { this(ctrl,st,fld,-1,bad); }
  public StoreNode( Node ctrl, Node st, int fld_num, Parse bad ) { this(ctrl,st,null,fld_num,bad); }
  String xstr() { return "."+(_fld==null ? ""+_fld_num : _fld); } // Self short name
  String  str() { return xstr(); }      // Inline short name
  
  @Override public Node ideal(GVNGCM gvn) {
    return null;
  }

  @Override public Type value(GVNGCM gvn) {
    Type t = gvn.type(in(1)).base();
    if( t.isa(TypeNil.XOOP) ) return TypeMem.MEM.dual(); // Very high address; might fall to any valid value
    if( t.isa(TypeOop.XOOP) ) return TypeMem.MEM.dual(); // Very high address; might fall to any valid value
    if( t instanceof TypeNil ) {
      if( !t.above_center() )     // NIL or below?
        return TypeMem.MEM;       // Fails - might be nil at runtime
      t = ((TypeNil)t)._t.base(); // Assume guarded by test
    }

    if( t instanceof TypeStruct ) {
      TypeStruct ts = (TypeStruct)t;
      int idx = find(ts);       // Find the named field
      if( idx != -1 ) {
        // return ts.at(idx); // Field type
        return TypeMem.MEM;
      }
    }

    return TypeMem.MEM;
  }

  private int find(TypeStruct ts) {
    if( _fld == null ) { // No fields, i.e. a tuple?
      if( _fld_num < ts._ts.length ) // Range-check tuple
        return _fld_num; // Return nth tuple field
      else
        throw AA.unimpl();
    } else return ts.find(_fld);  // Find the named field
  }

  @Override public String err(GVNGCM gvn) {
    Type t = gvn.type(in(1));
    while( t instanceof TypeName ) t = ((TypeName)t)._t;
    if( t instanceof TypeNil && !t.above_center() ) return _badnil;
    if( TypeOop.OOP.isa(t) ) return _badfld; // Too low, might not have any fields
    if( !(t instanceof TypeStruct) ) return _badfld;
    TypeStruct ts = (TypeStruct)t;
    int fnum = find(ts);
    if( fnum == -1 )
      return _badfld;
    if( ts._finals[fnum] == 1 ) return _badfin; // Trying to over-write a final
    return null;
  }
  @Override public Type all_type() { return TypeMem.MEM; }
  @Override public int hashCode() { return super.hashCode()+(_fld==null ? _fld_num : _fld.hashCode()); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof StoreNode) ) return false;
    StoreNode st = (StoreNode)o;
    return _fld_num == st._fld_num && (_fld==null ? st._fld==null : _fld.equals(st._fld));
  }
}
