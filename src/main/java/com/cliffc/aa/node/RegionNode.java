package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;

import java.util.function.Predicate;

// Merge results
public class RegionNode extends Node {
  public RegionNode( Node... ctrls) { super(OP_REGION,ctrls); }
  RegionNode( byte op ) { super(op,(Node)null); } // For FunNodes
  @Override public Node ideal(GVNGCM gvn, int level) {
    // TODO: The unzip xform, especially for funnodes doing type-specialization
    // TODO: treat _cidx like U/F and skip_dead it also

    // Look for dead paths.  If found, cut dead path out of all Phis and this
    // Node, and return-for-progress.
    int dlen = _defs.len();
    for( int i=1; i<dlen; i++ )
      if( gvn.type(in(i))==Type.XCTRL && !in(i).is_prim() ) { // Found dead path; cut out
        for( Node phi : _uses )
          if( phi instanceof PhiNode ) {
            assert !phi.is_dead();
            Type oldt = gvn.unreg(phi);
            phi.remove(i,gvn);
            if( !phi.is_dead() ) gvn.rereg(phi,oldt);
          }
        if( !is_dead() ) { unwire(gvn,i);  remove(i,gvn); }
        return this; // Progress
      }

    if( dlen == 1 ) return null; // No live inputs; dead in value() call
    if( in(1) == Env.ALL_CTRL ) return null; // Alive from unknown caller
    if( dlen==2 ) {                          // Exactly 1 live path
      // If only 1 live path and no Phis then return 1 live path.
      for( Node phi : _uses ) if( phi instanceof PhiNode ) return null;
      // Single input FunNodes can NOT inline to their one caller,
      // unless the one caller only also calls the one FunNode.
      // Wait for the FunNode to be declared dead.
      if( in(0)==null && this instanceof FunNode )
        return null;            // I am not yet dead
      // Self-dead-cycle is dead in value() call
      return in(1)==this ? null : in(1);
    }
    // Check for empty diamond
    if( dlen==3 ) {             // Exactly 2 live paths
      Node nif = in(1).in(0);
      if( in(1) instanceof CProjNode && nif==in(2).in(0) ) {
        assert nif instanceof IfNode;
        // Must have no phi uses
        for( Node phi : _uses ) if( phi instanceof PhiNode ) return null;
        return nif.in(0);
      }
    }

    return null;
  }

  void unwire(GVNGCM gvn, int idx) { }

  @Override public Type value(GVNGCM gvn) {
    if( _defs._len==2 && in(1)==this ) return Type.XCTRL; // Dead self-loop
    for( int i=1; i<_defs._len; i++ ) {
      Type c = gvn.type(in(i));
      if( c == Type.CTRL || c == Type.ALL )
        return Type.CTRL;
    }
    return Type.XCTRL;
  }
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) { return TypeMem.ALIVE; }

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
