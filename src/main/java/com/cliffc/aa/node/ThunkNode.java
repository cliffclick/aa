package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;

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
    if( _keep==0 &&         // If keep, then during construction and no Thret built yet (but coming)
        is_copy(0)==null && // If copy, then alive and collapsing as a copy
        thret()==null )     // If not-copy & not-keep AND no Thret, then dead from below
      return Type.XCTRL;
    return Type.CTRL;
  }
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    return def==in(1) ? TypeMem.ALLMEM : TypeMem.ALIVE; // Basic aliveness, except for memory
  }
  @Override public Node is_copy(int idx) {
    if( _defs._len==2 ) return null;
    if( idx==0 ) return in(2);  // Wired thunk added a def
    if( idx==1 ) return in(1);
    throw com.cliffc.aa.AA.unimpl();
  }
  @Override Node walk_dom_last(Predicate<Node> P) { return in(0)==null ? null : super.walk_dom_last(P); }
  // Never equal, since will be editted during parsing & then removed.
  @Override public boolean equals(Object o) { return this==o; } //
  ThretNode thret() {
    for( Node use : _uses )
      if( use instanceof ThretNode && ((ThretNode)use).thunk()==this )
        return (ThretNode)use;
    return null;
  }
}
