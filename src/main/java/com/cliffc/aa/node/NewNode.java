package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeStruct;

// Make a new object of given type
public class NewNode extends Node {
  private final TypeStruct _ts;
  public NewNode( TypeStruct ts, Node[] flds ) {
    super(OP_NEW,flds);
    assert flds[0]==null;       // no ctrl field
    _ts=ts;
  }
  String xstr() { return "New#"+_ts; }  // Self short name
  String  str() { return xstr(); }      // Inline short name
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) {
    for( int i=0; i<_ts._args.length; i++ )
      if( _ts._tt.at(i) != gvn.type(at(i+1)) )
        throw AA.unimpl();
    return _ts;
  }
  @Override public int hashCode() { return super.hashCode()+_ts.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof NewNode) ) return false;
    NewNode nnn = (NewNode)o;
    return _ts==nnn._ts;
  }
}
