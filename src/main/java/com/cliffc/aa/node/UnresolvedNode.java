package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFunPtr;

import java.util.Arrays;

public class UnresolvedNode extends Node {
  private Parse _bad;
  UnresolvedNode( Parse bad, Node... funs ) { super(OP_UNR,funs); _bad = bad;}
  @Override String xstr() {
    if( is_dead() ) return "DEAD";
    if( in(0) instanceof FunPtrNode ) {
      FunPtrNode fptr = (FunPtrNode)in(0);
      return "Unr:"+fptr.fun().xstr();
    }
    return "Unr???";
  }
  @Override public Node ideal(GVNGCM gvn) {
    if( _defs._len < 2 )               // One function, consumer should treat as a copy
      throw com.cliffc.aa.AA.unimpl(); // Should collapse
    // Back-to-back Unresolved collapse (happens due to inlining)
    boolean progress=false;
    for( int i=0; i<_defs._len; i++ ) {
      if( in(i) instanceof UnresolvedNode ) {
        progress = true;
        Node u = in(i);
        for( int j=0; j<u._defs._len; j++ )
          add_def(u.in(j));
        set_def(i,pop(),gvn);
      }
    }
    return progress ? this : null;
  }
  @Override public Type value(GVNGCM gvn) {
    // Unresolved is a *choice* and thus a *join* until resolved.
    Type t = TypeFunPtr.GENERIC_FUNPTR;
    for( Node def : _defs )
      t = t.join(gvn.type(def));
    return t;
  }
  // Filter out all the wrong-arg-count functions
  public Node filter( GVNGCM gvn, int nargs ) {
    Node x = null;
    for( Node epi : _defs ) {
      FunNode fun =  ((FunPtrNode)epi).fun();
      if( fun.nargs() != nargs ) continue;
      if( x == null ) x = epi;
      else if( x instanceof UnresolvedNode ) x.add_def(epi);
      else x = new UnresolvedNode(_bad,x,epi);
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
  @Override public int hashCode() { return super.hashCode()+(_bad==null ? 0 : _bad.hashCode()); }
  @Override public boolean equals(Object o) {
    if( !super.equals(o) ) return false;
    return _bad==((UnresolvedNode)o)._bad;
  }
  // Make a copy with an error message
  public UnresolvedNode copy(Parse bad) {
    return new UnresolvedNode(bad,Arrays.copyOf(_defs._es,_defs._len));
  }
  // True if unresolved is uncalled (but possibly returned or stored as a
  // constant).  Such code is not searched for errors.  Here we just check for
  // being ONLY used by the initial environment; if this value is loaded from,
  // it will have other uses.
  @Override boolean is_uncalled(GVNGCM gvn) {
    return _uses._len==0 || (_uses._len==1 && _uses.at(0)== Env.STK_0);
  }
  @Override public String err(GVNGCM gvn) {
    String name = ((FunPtrNode)in(0)).fun().xstr();
    return _bad==null ? null : _bad.errMsg("Unable to resolve "+name);
  }
}
