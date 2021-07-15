package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeTuple;

// Thret: a limited function return
// See Thunk (Fun)

// Expected 1 callepi only, determined after Parse.expr().
// Takes in Control & Memory & Value.
// Produces Control & Memory & Value.
public class ThretNode extends Node {
  public ThretNode( Node ctrl, Node mem, Node val, ThunkNode thunk ) { super(OP_THRET,ctrl,mem,val,thunk); _live = TypeMem.ALLMEM; }
  public Node ctrl() { return in(0); }
  public Node mem () { return in(1); }
  public Node rez () { return in(2); }
  public ThunkNode thunk() { return (ThunkNode)in(3); }
  @Override public Type value(GVNGCM.Mode opt_mode) {
    return TypeTuple.RET;
  }
  @Override public TypeMem live(GVNGCM.Mode opt_mode ) { return TypeMem.ALLMEM; }
  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    if( def==ctrl() ) return TypeMem.ALIVE;
    if( def==mem () ) return _live;
    if( def==rez () ) return TypeMem.ESCAPE;
    if( def==thunk()) return TypeMem.ALIVE;
    throw com.cliffc.aa.AA.unimpl();
  }
  //@Override public TV2 new_tvar(String alloc_site) {
  //  return TV2.make("Ret",this,alloc_site,in(0),in(1),in(2));
  //}
}
