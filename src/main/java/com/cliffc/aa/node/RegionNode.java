package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;

import java.util.function.Predicate;

// Merge results.  Supports many merging paths; used by FunNode and LoopNode.
public class RegionNode extends Node {
  public RegionNode( Node... ctrls) { super(OP_REGION,ctrls); }
  RegionNode( byte op ) { super(op,(Node)null); } // For FunNodes

  @Override public Node ideal_reduce() {
    // TODO: The unzip xform, especially for funnodes doing type-specialization
    // TODO: treat _cidx like U/F and skip_dead it also
    int dlen = _defs.len();
    for( int i=1; i<dlen; i++ ) {
      Node cc = in(i).is_copy(0);
      if( cc!=null && cc != this ) return set_def(i,cc);
    }

    // Look for dead paths.  If found, cut dead path out of all Phis and this
    // Node, and return-for-progress.
    for( int i=1; i<dlen; i++ )
      if( val(i)==Type.XCTRL && !(i==1 && is_prim()) ) { // Found dead path; cut out
        for( Node phi : _uses )
          if( phi instanceof PhiNode )
            phi.remove(i);
        unwire(i);
        remove(i);
        if( this instanceof FunNode && _defs._len==2 && in(1).in(0) instanceof CallNode ) {
          Node cepi = ((CallNode)in(1).in(0)).cepi();
          if( cepi!=null ) Env.GVN.add_reduce(cepi);
        }
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
  @Override public void add_flow_def_extra(Node chg) {
    if( chg.is_CFG() ) {           // If losing an extra CFG user
      for( Node use : _uses )
        if( use._op == OP_REGION ) // Then stacked regions can fold
          Env.GVN.add_reduce(use); // Put lower region of stack on worklist
      if( this instanceof FunNode && ((FunNode)this).ret()==null )
        Env.GVN.add_reduce(this);
    }
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
    Env.GVN.iter(null, Env.GVN._reduce_works);
    assert r.is_dead();
    return this;
  }

  void unwire(int idx) { }

  @Override public Type value(GVNGCM.Mode opt_mode) {
    if( _defs._len==2 && in(1)==this ) return Type.XCTRL; // Dead self-loop
    for( int i=1; i<_defs._len; i++ ) {
      Type c = val(i);
      if( c == Type.CTRL || c == Type.ALL )
        return Type.CTRL;
    }
    return Type.XCTRL;
  }
  // Control into a Region allows Phis to make progress
  @Override public void add_flow_use_extra(Node chg) {
    Env.GVN.add_reduce(this);
    for( Node phi : _uses )
      if( phi instanceof PhiNode ) {
        Env.GVN.add_flow(phi);
        Env.GVN.add_flow_defs(phi); // Inputs to Phi change liveness
      }
  }

  @Override public TypeMem all_live() { return TypeMem.ALIVE; }
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) { return TypeMem.ALIVE; }

  //@Override public TV2 new_tvar(String alloc_site) { return TV2.make_base(this,Type.CTRL,alloc_site); }
  //
  //// All (Base:Ctrl) inputs unify
  //@Override public boolean unify( boolean test ) {
  //  boolean progress = false;
  //  for( int i=1; i<_defs._len; i++ )
  //    if( val(i)!=Type.XCTRL && val(i)!=Type.ANY ) { // Only unify alive paths
  //      progress |= tvar().unify(tvar(i),test);
  //      if( progress && test ) return true;
  //    }
  //  return progress;
  //}

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
  @Override public Node is_copy(int idx) { return _defs._len==2 ? in(1) : null; }
}
