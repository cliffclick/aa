package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeTuple;

// Thret: a limited function return
// See Thunk (Fun), Thrall (Call).

// Expected 1 callepi only, determined after Parse.expr().
// Takes in Control & Memory & Value.
// Produces Control & Memory & Value.
public class ThretNode extends Node {
  public ThretNode( Node ctrl, Node mem, Node val, ThunkNode thunk ) { super(OP_THRET,ctrl,mem,val,thunk); }
  public Node ctrl() { return in(0); }
  public Node mem () { return in(1); }
  public Node rez () { return in(2); }
  public ThunkNode thunk() { return (ThunkNode)in(3); }
  @Override public Node ideal(GVNGCM gvn, int level) {
    return null;
  }
  @Override public Type value(GVNGCM.Mode opt_mode) {
    return TypeTuple.RET;
  }
  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    return def==in(1) || def==in(3) ? _live : TypeMem.ALIVE; // Basic aliveness for ctrl,rez full live for memory & thunk
  }
}
