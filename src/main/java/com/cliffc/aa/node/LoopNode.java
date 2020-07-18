package com.cliffc.aa.node;

import java.util.function.Predicate;

// Merge backedge results; exactly a 2-input Region.
public class LoopNode extends RegionNode {
  public LoopNode() { super(OP_LOOP); }

  @Override Node walk_dom_last(Predicate<Node> P) {
    Node n = in(1).walk_dom_last(P); // Only walk loop fall-in
    if( n != null ) return n;        // Take last answer first
    return P.test(this) ? this : null;
  }
  
}
