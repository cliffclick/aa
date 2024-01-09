package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.type.Type;

import java.util.function.Predicate;

// Merge results.  Supports many merging paths; used by FunNode and LoopNode.
public class RegionNode extends Node {
  public RegionNode( Node... ctrls) { super(ctrls); }
  @Override public String label() { return "Region"; }
  @Override public boolean isCFG() { return true; }
  @Override public boolean isMultiHead() { return true; }
  @Override public Node isCopy(int idx) { return len()==2 ? in(1) : null; }

  @Override public Node ideal_reduce() {
    if( isPrim() ) return null;
    // TODO: The unzip xform, especially for FunNodes doing type-specialization
    // TODO: treat _cidx like U/F and skip_dead it also

    // Fold control-folded paths
    for( int i=1; i<len(); i++ ) {
      Node cc = in(i).isCopy(0);
      if( cc!=null && cc != this ) return Env.GVN.add_reduce(setDef(i,cc));
    }

    // Look for dead paths.  If found, cut dead path out of all Phis and this
    // Node, and return-for-progress.
    for( int i=1; i<len(); i++ ) {
      Node cin = in(i);
      if( cin._val==Type.XCTRL ) { // Dead control flow input
        for( Node phi : uses() )
          if( phi instanceof PhiNode ) {
            Env.GVN.add_flow(phi.in(i));
            phi.del(i);
          }
        del(i);
        return Env.GVN.add_reduce(this); // Progress
      } else
        cin.deps_add(this);   // Revisit if becomes XCTRL
    }

    if( len() == 1 ) return null; // No live inputs; dead in value() call
    if( len() == 2 ) {            // Exactly 1 live path
      // If only 1 live path and no Phis then return 1 live path.
      for( Node phi : uses() ) if( phi instanceof PhiNode ) return null;
      // Self-dead-cycle is dead in value() call
      return in(1)==this ? null : in(1);
    }
    // Check for empty diamond
    if( len()==3 ) {            // Exactly 2 live paths
      Node nif = in(1).in(0);
      if( in(1) instanceof CProjNode && nif==in(2).in(0) && nif instanceof IfNode ) {
        // Must have no phi uses
        for( Node phi : uses() ) if( phi instanceof PhiNode ) return null;
        return nif.in(0);
      }
    }

    // Check for stacked Region (not Fun) and collapse.
    Node stack = stacked_region();
    if( stack != null ) return stack;

    return null;
  }

  // Collapse stacked regions.
  Node stacked_region() {
    int idx = -1;
    for( int i=1; i<len(); i++ )
      if( in(i) instanceof RegionNode )
        { idx = i; break; }
    if( idx== -1 ) return null; // No stacked region
    Node r = in(idx);
    if( r == this ) return null; // Dying code
    int cfgs=0;
    for( Node use : r.uses() ) cfgs += use.isCFG() ? 1 : 0;
    if( cfgs != 1 ) return null;
    // Every 'r' Phi is pointed *at* by exactly a 'this' Phi
    for( Node rphi : r.uses() )
      if( rphi instanceof PhiNode ) {
        if( rphi.nUses() != 1 ) return null; // Busy rphi
        Node phi = rphi.use0();              // Exactly a this.phi
        if( !(phi instanceof PhiNode) ||     // Not a Phi
            phi.in(0) != this ||             // Control to this
            phi.in(idx) != rphi )            // Matching along idx
          return null;                       // Not exact shape
      }

    // Collapse stacked Phis
    for( Node phi : uses() )
      if( phi instanceof PhiNode ) {
        Node rphi = phi.in(idx);
        boolean stacked_phi = rphi instanceof PhiNode && rphi.in(0)==r;
        for( int i = 1; i<r.len(); i++ )
          phi.addDef(stacked_phi ? rphi.in(i) : rphi);
        phi.del(idx);
        assert !stacked_phi || rphi.len()==0;
      }

    // Collapse stacked Region
    for( int i = 1; i<r.len(); i++ )
      addDef(r.in(i));
    del(idx);
    return this;
  }

  @Override public Type value() {
    if( in(0)==this )           // is_copy
      return len()>=2 ? val(1) : Type.XCTRL;
    for( int i=1; i<len(); i++ ) {
      Node n = in(i), x;
      if( n==this ) continue; // Ignore self-loop
      while( (x=n.isCopy(0))!=null )
        n=x;
      Type c = n._val;
      if( c == Type.CTRL || c == Type.ALL )
        return Type.CTRL;
    }
    return Type.XCTRL;
  }

  @Override public Type live_use( int i ) { return Type.ALL; }

  @Override public boolean has_tvar() { return false; }

  //// Complex dominator tree.  Ok to subset, attempt the easy walk
  //@Override Node walk_dom_last(Predicate<Node> P) {
  //  // Allow moving up simple diamonds
  //  if( _defs._len==3 && in(1) instanceof ProjNode && in(1).in(0) instanceof IfNode &&
  //      in(1).in(0) == in(2).in(0) ) {
  //    Node n = in(1).in(0).walk_dom_last(P);
  //    if( n != null ) return n;
  //  }
  //  // Experimental stronger version
  //  if( _defs._len==3 ) {
  //    Node n1 = in(1).walk_dom_last(P);
  //    Node n2 = in(2).walk_dom_last(P);
  //    if( n1 != null && n1==n2 ) return n1;
  //  }
  //  return P.test(this) ? this : null;
  //}
}
