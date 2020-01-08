package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;

import java.util.function.Predicate;

// Merge results
public class RegionNode extends Node {
  public RegionNode( Node... ctrls) { super(OP_REGION,ctrls); }
  RegionNode( byte op ) { super(op); add_def(null); } // For FunNodes
  @Override public Node ideal(GVNGCM gvn) {
    // TODO: The unzip xform, especially for funnodes doing type-specialization
    // TODO: Check for dead-diamond merges
    // TODO: treat _cidx like U/F and skip_dead it also

    // Look for dead paths.  If found, cut dead path out of all Phis and this
    // Node, and return-for-progress.
    int dlen = _defs.len();
    for( int i=1; i<dlen; i++ )
      if( gvn.type(in(i))==Type.XCTRL ) { // Found dead path; cut out
        for( Node phi : _uses )
          if( phi instanceof PhiNode ) {
            assert !phi.is_dead();
            Type oldt = gvn.unreg(phi);
            phi.remove(i,gvn);
            if( !phi.is_dead() ) gvn.rereg(phi,oldt);
          }
        if( !is_dead() ) remove(i,gvn);
        return this; // Progress
      }

    if( dlen>2 ) return null; // Multiple live paths
    if( dlen == 1 ) return null; // No live inputs; dead in value() call
    if( in(1) == Env.ALL_CTRL ) return null; // Alive from unknown caller
    // If only 1 live path and no Phis then return 1 live path.
    for( Node phi : _uses ) if( phi instanceof PhiNode ) return null;
    // Single input FunNodes can NOT inline to their one caller,
    // unless the one caller only also calls the one FunNode.
    if( this instanceof FunNode )
      return null;
    // Self-dead-cycle is dead in value() call
    return in(1)==this ? null : in(1);
  }

  @Override public Type value(GVNGCM gvn) {
    if( _defs._len==2 && in(1)==this ) return Type.XCTRL; // Dead self-loop
    for( int i=1; i<_defs._len; i++ ) {
      Type c = gvn.type(in(i));
      if( c == Type.CTRL || c == Type.ALL )
        return Type.CTRL;
    }
    return Type.XCTRL;
  }

  @Override public Type all_type() { return Type.CTRL; }
  // Complex dominator tree.  Ok to subset, attempt the easy walk
  @Override Node walk_dom_last(Predicate<Node> P) {
    // Allow moving up simple diamonds
    if( _defs._len==3 && in(1) instanceof ProjNode && in(1).in(0) instanceof IfNode &&
        in(1).in(0) == in(2).in(0) ) {
      Node n = in(1).in(0).walk_dom_last(P);
      if( n != null ) return n;
    }
    // Experimental stronger version
    if( _defs._len==3 && !(this instanceof FunNode) ) {
      Node n1 = in(1).walk_dom_last(P);
      Node n2 = in(2).walk_dom_last(P);
      if( n1 != null && n1==n2 ) return n1;
    }
    return P.test(this) ? this : null;
  }
}
