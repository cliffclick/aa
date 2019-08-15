package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.BitsFun;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFunPtr;

public class UnresolvedNode extends Node {
  UnresolvedNode( Node... funs ) { super(OP_UNR,funs); }
  @Override String xstr() {
    if( in(0) instanceof EpilogNode ) {
      EpilogNode epi = (EpilogNode)in(0);
      if( epi.in(0) instanceof FunNode )
        return "Unr:"+epi.fun()._name;
    }
    return "Unr???";
  }
  @Override public Node ideal(GVNGCM gvn) {
    if( _defs._len < 2 )
      //throw AA.unimpl(); // Should collapse
      System.out.println("Should collapse");
    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    Type t = TypeFunPtr.GENERIC_FUNPTR;
    for( Node def : _defs )
      t = t.join(gvn.type(def)); // Join of incoming functions
    return t.meet(TypeFunPtr.GENERIC_FUNPTR.dual());
  }
  BitsFun fidxs() {
    int[] bits = new int[_defs._len];
    for( int i=0; i<_defs._len; i++ )
      bits[i] = ((EpilogNode)in(i)).fidx();
    return BitsFun.make0(bits).dual();
  }
  // Filter out all the wrong-arg-count functions
  public Node filter( GVNGCM gvn, int nargs ) {
    Node x = null;
    for( Node epi : _defs ) {
      FunNode fun =  ((EpilogNode)epi).fun();
      if( fun.nargs() != nargs ) continue;
      if( x == null ) x = epi;
      else if( x instanceof UnresolvedNode ) x.add_def(epi);
      else x = new UnresolvedNode(x,epi);
    }
    return x instanceof UnresolvedNode ? gvn.xform(x) : x;
  }
  
  @Override public TypeFunPtr all_type() { return TypeFunPtr.GENERIC_FUNPTR; }
  
  // Return the op_prec of the returned value.  Not sensible except when called
  // on primitives.  Should be the same across all defs.
  @Override public byte op_prec() {
    byte prec = _defs.at(0).op_prec();
    assert _defs._len < 2 || _defs.at(1).op_prec() == prec;
    return prec;
  }
  // Return the op_prec of the returned value.  Not sensible except when called
  // on primitives.  Should be the same across all defs.
  @Override public byte may_prec() {
    byte prec = -1;
    for( Node f : _defs ) if( (prec=f.op_prec()) >= 0 ) return prec;
    return prec;
  }
}
