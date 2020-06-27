package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeTuple;

// Split a set of aliases into a SESE region, to be joined by a later MemJoin.
// This allows more precision in the SESE that may otherwise merge many paths
// in and out, and is especially targeting non-inlined calls.
public class MemSplitNode extends Node {

  public MemSplitNode( CallNode call ) {
    super(OP_SPLIT,call.mem());
    copy_call_args(call,null);
  }
  Node mem() { return in(0); }
  @Override public Node ideal(GVNGCM gvn, int level) {
    // Match call args.  Call args change for a bunch of reasons (constants,
    // dead) and instead of directly using them (and having the non-local
    // curse), nor being "inside" a Call/CEPI pair and depending on a Call (and
    // thus the Join has to do the CEPIs job of merging returns), just replicate
    // the Call args here.
    CallNode call = call();
    if( call != null )
      for( int i=0; i<call.nargs(); i++ )
        if( in(i+1)!=call.arg(i) )
          return copy_call_args(call,gvn);

    return null;
  }

  @Override public Type value(GVNGCM gvn) {
    Type t0 = gvn.type(in(0));
    if( !(t0 instanceof TypeMem) ) return t0.oob();
    return TypeTuple.make( lhs_mem(gvn), rhs_mem(gvn) );
  }
  @Override public boolean basic_liveness() { return false; }
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) { return def==mem() ? _live : TypeMem.ALIVE; }
  
  TypeMem lhs_mem(GVNGCM gvn) { return TypeMem.ANYMEM; }
  TypeMem rhs_mem(GVNGCM gvn) {
    Type t0 = gvn.type(in(0));
    return t0 instanceof TypeMem ? (TypeMem)t0 : null;
  }

  CallNode call() {
    ProjNode p1 = ProjNode.proj(this,1);
    if( p1==null ) return null;
    int idx = p1._uses.find(e->e instanceof CallNode);
    if( idx==-1 ) return null;
    return (CallNode)(p1._uses.at(idx));
  }
  private Node copy_call_args(CallNode call, GVNGCM gvn) {
    while( _defs._len > 1 )
      pop(gvn);
    // Add all call args, needed to split escaping aliases
    for( int i=0; i<call.nargs(); i++ )
      add_def(call.arg(i));
    return this;
  }

  @Override public Node is_copy(GVNGCM gvn, int idx) {
    return _keep==0 && _uses._len==1 && ((MProjNode)_uses.at(0))._idx==idx ? mem() : null;
  }
}
