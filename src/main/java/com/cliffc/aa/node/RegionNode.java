package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;

import java.util.function.Predicate;

// Merge results
public class RegionNode extends Node {
  public RegionNode( Node... ctrls) { super(OP_REGION,ctrls); }
  RegionNode( byte op ) { super(op); add_def(null); } // For FunNodes
  @Override public Node ideal(GVNGCM gvn) { return ideal(gvn,false); }
  // Ideal call, but FunNodes keep index#1 for future parsed call sites
  Node ideal(GVNGCM gvn, boolean keepslot1) {
    // TODO: The unzip xform, especially for funnodes doing type-specialization
    // TODO: Check for dead-diamond merges
    // TODO: treat _cidx like U/F and skip_dead it also

    // Look for dead paths.  If found, cut dead path out of all Phis and this
    // Node, and return-for-progress.
    int dlen = _defs.len();
    for( int i=keepslot1 ? 2 : 1; i<dlen; i++ )
      if( gvn.type(in(i))==Type.XCTRL ) { // Found dead path; cut out
        for( Node phi : _uses )
          if( phi instanceof PhiNode ) {
            Type ot = gvn.type(phi); gvn.unreg(phi); phi.remove(i,gvn); gvn.rereg(phi,ot);
          }
        remove(i,gvn);
        return this; // Progress
      }

    // If only 1 live path and no Phis then return 1 live path.
    if( dlen>2 || keepslot1 ) return null; // Multiple live paths
    for( Node phi : _uses ) if( phi instanceof PhiNode ) return null;
    return in(1)==this ? null : in(1);
  }

  @Override public Type value(GVNGCM gvn) {
    if( _defs._len==2 && in(1)==this ) return Type.XCTRL; // Dead self-loop
    Type t = Type.XCTRL;
    for( int i=1; i<_defs._len; i++ )
      t = t.meet(gvn.type(in(i)));
    return t;
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
    return P.test(this) ? this : null;
  }
}
