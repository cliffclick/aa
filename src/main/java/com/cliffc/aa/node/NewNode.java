package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeStruct;
import com.cliffc.aa.type.TypeTuple;

// Make a new object of given type
public class NewNode extends Node {
  private final TypeTuple _ts;
  public NewNode( TypeTuple ts, Node[] flds ) {
    super(OP_NEW,flds);
    assert flds[0]==null;       // no ctrl field
    _ts=ts;
  }
  String xstr() { return "New#"+_ts; }  // Self short name
  String  str() { return xstr(); }      // Inline short name
  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value_ne(GVNGCM gvn) {
    TypeStruct tstr = _ts instanceof TypeStruct ? (TypeStruct)_ts : null;
    assert tstr==null || tstr._args.length+1 == _defs._len;
    boolean eq=true;
    for( int i=1; i<_defs._len; i++ )
      eq &= _ts.at(i-1) == gvn.type_ne(in(i));
    if( eq ) return _ts;
    Type[] ts = new Type[_defs._len-1];
    for( int i=0; i<ts.length; i++ ) {
      ts[i] = gvn.type_ne(in(i+1));
      assert ts[i].isa(_ts.at(i)); // Type correct
    }
    return tstr==null ? TypeTuple.make_all(ts) : TypeStruct.makeA(tstr._args,ts);
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
