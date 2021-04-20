package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Env;
import com.cliffc.aa.type.Type;

// "fresh" the incoming TVar: make a fresh instance.
public class FreshNode extends Node {
  Env.VStack _vs;
  FreshNode( Env.VStack vs, Node ld ) { super(OP_FRESH, ld); _vs=vs; assert vs!=null; }

  @Override public Node ideal_reduce() { return null; }
  
  @Override public Type value(GVNGCM.Mode opt_mode) { return val(0); }  

  @Override public boolean unify( boolean test ) {  return tvar(0).fresh_unify(tvar(),_vs,test); }
  
}
