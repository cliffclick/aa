package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.type.Type;

import java.util.function.Predicate;

// Merge results.  Supports many merging paths; used by FunNode and LoopNode.
public class RegionNode extends Node {
  public RegionNode( Node... ctrls) { super(OP_REGION,ctrls); }
  @Override boolean is_CFG() { return is_copy(0)==null; }

  @Override public Node ideal_reduce() {
    // TODO: The unzip xform, especially for FunNodes doing type-specialization
    // TODO: treat _cidx like U/F and skip_dead it also

    // Fold control-folded paths
    for( int i=1; i<_defs._len; i++ ) {
      Node cc = in(i).is_copy(0);
      if( cc!=null && cc != this ) return Env.GVN.add_reduce(set_def(i,cc));
    }

    // Look for dead paths.  If found, cut dead path out of all Phis and this
    // Node, and return-for-progress.
    for( int i=1; i<_defs._len; i++ ) {
      Node cin = in(i);
      if( cin._val==Type.XCTRL ) { // Dead control flow input
        for( Node phi : _uses )
          if( phi instanceof PhiNode )
            Env.GVN.add_flow(phi.remove(i));
        remove(i);
        return Env.GVN.add_reduce(this); // Progress
      } else
        cin.deps_add(this);   // Revisit if becomes XCTRL
    }

    if( _defs._len == 1 ) return null; // No live inputs; dead in value() call
    if( _defs._len==2 ) {              // Exactly 1 live path
      // If only 1 live path and no Phis then return 1 live path.
      for( Node phi : _uses ) if( phi instanceof PhiNode ) return null;
      // Self-dead-cycle is dead in value() call
      return in(1)==this ? null : in(1);
    }
    // Check for empty diamond
    if( _defs._len==3 ) {             // Exactly 2 live paths
      Node nif = in(1).in(0);
      if( in(1) instanceof CProjNode && nif==in(2).in(0) && nif instanceof IfNode ) {
        // Must have no phi uses
        for( Node phi : _uses ) if( phi instanceof PhiNode ) return null;
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
    if( _op != OP_REGION ) return null; // Does not apply to e.g. functions & loops
    int idx = _defs.find( e -> e !=null && e._op==OP_REGION );
    if( idx== -1 ) return null; // No stacked region
    Node r = in(idx);
    if( r == this ) return null; // Dying code
    int cfgs=0;
    for( Node use : r._uses ) cfgs += use.is_CFG() ? 1 : 0;
    if( cfgs != 1 ) return null;
    // Every 'r' Phi is pointed *at* by exactly a 'this' Phi
    for( Node rphi : r._uses )
      if( rphi._op == OP_PHI ) {
        if( rphi._uses._len != 1 ) return null; // Busy rphi
        Node phi = rphi._uses.at(0);            // Exactly a this.phi
        if( phi._op != OP_PHI ||                // Not a Phi
            phi.in(0) != this ||                // Control to this
            phi.in(idx) != rphi )               // Matching along idx
          return null;                          // Not exact shape
      }

    // Collapse stacked Phis
    for( Node phi : _uses )
      if( phi._op == OP_PHI ) {
        Node rphi = phi.in(idx);
        boolean stacked_phi = rphi._op == OP_PHI && rphi.in(0)==r;
        for( int i = 1; i<r._defs._len; i++ )
          phi.add_def(stacked_phi ? rphi.in(i) : rphi);
        phi.remove(idx);
        assert !stacked_phi || rphi._uses._len==0;
      }

    // Collapse stacked Region
    for( int i = 1; i<r._defs._len; i++ )
      add_def(r.in(i));
    remove(idx);
    return this;
  }

  @Override public Type value() {
    if( in(0)==this )           // is_copy
      return _defs._len>=2 ? val(1) : Type.XCTRL;
    for( int i=1; i<_defs._len; i++ ) {
      Node n = in(i), x;
      if( n==this ) continue; // Ignore self-loop
      while( (x=n.is_copy(0))!=null )
        n=x;
      Type c = n._val;
      if( c == Type.CTRL || c == Type.ALL )
        return Type.CTRL;
    }
    return Type.XCTRL;
  }

  @Override public Type live_use( int i ) { return Type.ALL; }

  @Override public boolean has_tvar() { return false; }

  // Complex dominator tree.  Ok to subset, attempt the easy walk
  @Override Node walk_dom_last(Predicate<Node> P) {
    // Allow moving up simple diamonds
    if( _defs._len==3 && in(1) instanceof ProjNode && in(1).in(0) instanceof IfNode &&
        in(1).in(0) == in(2).in(0) ) {
      Node n = in(1).in(0).walk_dom_last(P);
      if( n != null ) return n;
    }
    // Experimental stronger version
    if( _defs._len==3 ) {
      Node n1 = in(1).walk_dom_last(P);
      Node n2 = in(2).walk_dom_last(P);
      if( n1 != null && n1==n2 ) return n1;
    }
    return P.test(this) ? this : null;
  }
  @Override public Node is_copy(int idx) { return _defs._len==2 ? in(1) : null; }
}
