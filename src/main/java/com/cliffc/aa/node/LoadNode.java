package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

// Load a named field from a struct
public class LoadNode extends Node {
  private final String _fld;
  private final String _badfld;
  private final String _badnul;
  public LoadNode( Node st, String fld, Parse badfld ) {
    super(OP_LOAD,null,st);
    _fld = fld;
    _badfld = badfld.errMsg("Unknown field '."+fld+"'");
    _badnul = badfld.errMsg("Struct might be null when reading field '."+fld+"'");
  }
  String xstr() { return "."+_fld; }    // Self short name
  String  str() { return xstr(); }      // Inline short name
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) {
    Type t = gvn.type(at(1));
    while( t instanceof TypeName ) t = ((TypeName)t)._t;
    if( t instanceof TypeStruct ) {
      TypeStruct ts = (TypeStruct)t;
      int idx = ts.find(_fld);
      if( idx == -1 )
        return TypeErr.make(_badfld);
      return ts._tt.at(idx);             // Field type
    }

    if( t==TypeErr.ALL ) { // t is 'below' any struct with fld name, then error type
      return TypeErr.make(_badfld);
    } else if( t==TypeErr.ANY ) { // t is 'above' any struct with fld name, then ANY type
      return TypeErr.ANY;
    } else if( t instanceof TypeErr ) {
      return t;
    } else if( t==TypeInt.NULL || (t instanceof TypeUnion && ((TypeUnion)t).has_null()) ) {
      return TypeErr.make(_badnul);
    }
    throw AA.unimpl();
  }
  @Override public int hashCode() { return super.hashCode()+_fld.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof LoadNode) ) return false;
    LoadNode ld = (LoadNode)o;
    return _fld.equals(ld._fld);
  }
}
