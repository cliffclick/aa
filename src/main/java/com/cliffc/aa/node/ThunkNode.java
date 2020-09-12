package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeTuple;
import java.util.function.Predicate;

// Thunk: a limited function.
// See Thret (Return), Thrall (Call).

// Expected 1 caller only, determined after Parse.expr(), so the single input
// is just a constant hook: StartNode.
// No arguments, not even a display (uses the existing display, no scope implied).
// Produces a Control & Memory.
public class ThunkNode extends Node {
  public ThunkNode( Node mem ) { super(OP_THUNK,null,mem); }
  @Override public Node ideal(GVNGCM gvn, int level) {
    return null;
  }
  @Override public Type value(GVNGCM.Mode opt_mode) {
    return TypeTuple.make(in(0)==null ? Type.CTRL : val(0),
                          ((TypeMem)val(1)).crush()); // Just keep enough for parsing
  }
  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    return def==in(1) ? _live : TypeMem.ALIVE; // Basic aliveness, except for memory
  }
  public void inline(GVNGCM gvn, Node ctrl, Node mem) {
    gvn.set_def_reg(this,0,ctrl);
    gvn.set_def_reg(this,1,mem );
  }
  @Override public Node is_copy(GVNGCM gvn, int idx) { return in(0)==null ? null : in(idx); }
  @Override Node walk_dom_last(Predicate<Node> P) { return in(0)==null ? null : super.walk_dom_last(P); }
  // Never equal, since will be editted during parsing & then removed.
  @Override public boolean equals(Object o) { return this==o; } // 
}
