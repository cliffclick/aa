package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Env;
import com.cliffc.aa.Combo;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.VBitSet;

import java.lang.Iterable;
import java.util.Iterator;

import static com.cliffc.aa.AA.TODO;
import static com.cliffc.aa.Env.GVN;

// Sea-of-Nodes
public abstract class NodeUtil {

  // Non-allocating iterator; pulls iterators from a pool.  The hard part is
  // telling when an iterator ends early, to avoid leaking.  This is not
  // exactly asserted for, so some leaks may happen.  The general rule is:
  // only use these iterators if they run to the end; early exits leak.
  
  public static class Iter implements Iterator<Node>, Iterable<Node> {
    private static final Ary<Iter> POOL = new Ary<>(Iter.class);
    private static int CNT=0; // Number of Iters made, helps to track leaks
    Node[] _ns;               // Nodes
    int _len;                 // Number of Nodes actually in ns
    int _i;                   // Iterator index, 0 <= i < len, or -99
    static Iter get(Node[] ns, int len) {
      if( POOL.isEmpty() ) {
        assert CNT<100; CNT++; new Iter().end(); }
      return POOL.pop().init(ns,len);
    }
    @Override public Iter iterator() { return this; }
    boolean end() { _i=-99; _ns=null; _len=-1; POOL.push(this); return false; }
    private Iter init(Node[] ns, int len) { assert _i==-99; _i=0; _ns=ns; _len=len; return this; }
    @Override public boolean hasNext() {  assert _i>=0; return _i < _len || end(); }
    @Override public Node next() { return _ns[_i++]; }
    @Override public void remove() { throw TODO(); }
  }
  public static boolean leak() { return Iter.POOL._len<Iter.CNT; }

  
  // Fold control copies
  public static Node fold_ccopy(Node x) {
    Node cc = x.in(0).isCopy(0);
    if( cc == null ) return null;
    if( cc == x ) return Env.ANY; // Dead self-cycle
    GVN.add_reduce_uses(x);
    return GVN.add_reduce(x.setDef(0,cc));
  }

  
  // --------------------------------------------------------------------------
  // Assert all value and liveness calls only go forwards, and if they can
  // progress they are on the worklist.
  private static boolean MORE_WORK_ASSERT;
  public static int more_work(Node root) {
    assert !MORE_WORK_ASSERT;
    MORE_WORK_ASSERT = true;
    int rez = root.walk( Node::more_work );
    MORE_WORK_ASSERT = false;
    return rez;
  }
  public static boolean mid_work_assert() { return MORE_WORK_ASSERT; }
  static int more_work( int errs, Node n ) {
    if( GVN.on_dead(n) ) return -1; // Do not check dying nodes or reachable from dying
    if( n.isPrim() ) return errs;        // Do not check primitives
    int old = Iter.POOL._len;
    // Check for GCP progress
    Type oval= n._val, nval = n.value(); // Forwards flow
    Type oliv=n._live, nliv = n.live (); // Backwards flow
    assert Iter.POOL._len==old;          // No leaks
    if( oval!=nval || oliv!=nliv ) {
      if( !(AA.LIFTING
            ? nval.isa(oval) && nliv.isa(oliv)
            : oval.isa(nval) && oliv.isa(nliv)) )
        errs += _report_bug(n,"Monotonicity bug");
      if( !GVN.on_flow(n) && (AA.LIFTING || AA.DO_GCP) )
        errs += _report_bug(n,"Progress bug");
    }
    // Check for HMT progress
    if( !AA.LIFTING &&                      // Falling, in Combo, so HM is running
        oliv!=Type.ANY && oval!=Type.ANY && // Alive in any way
        n.has_tvar() &&                       // Doing TVar things
        (!GVN.on_flow(n) || Combo.HM_FREEZE) ) { // Not already on worklist, or past freezing
      if( n.unify(true) )
        errs += _report_bug(n,Combo.HM_FREEZE ? "Progress after freezing" : "Progress bug");
    }
    return errs;
  }
  private static int _report_bug(Node n, String msg) {
    Node.WVISIT.clear(n._uid); // Pop-frame & re-run in debugger
    System.err.println(msg);
    System.err.println(NodePrinter.prettyPrint(n,0,n.isPrim()));
    // BREAKPOINT HERE
    Node.WVISIT.set(n._uid); // Reset if progressing past breakpoint
    return 1;
  }

  // Assert all ideal, value and liveness calls are done
  private static final VBitSet IDEAL_VISIT = new VBitSet();
  public static boolean no_more_ideal(Node root) {
    assert !MORE_WORK_ASSERT;
    MORE_WORK_ASSERT = true;
    IDEAL_VISIT.clear();
    boolean no_more = !_more_ideal(root);
    MORE_WORK_ASSERT = false;
    return no_more;
  }
  private static boolean _more_ideal(Node n) {
    if( n==null || n.isPrim() ) return false;
    if( IDEAL_VISIT.tset(n._uid) ) return false; // Been there, done that
    if( !n.isKeep() && !GVN.on_dead(n)) { // Only non-keeps, which is just top-level scope and prims
      assert !NodeUtil.leak();
      Node x;
      if( !GVN.on_reduce(n) ) { x = n.do_reduce(); if( x != null )
                                                         return true; } // Found an ideal call
      if( !GVN.on_mono  (n) ) { x = n.do_mono  (); if( x != null )
                                                         return true; } // Found an ideal call
      if( !GVN.on_grow  (n) ) { x = n.do_grow  (); if( x != null )
                                                         return true; } // Found an ideal call
      if( n instanceof FunNode fun && !GVN.on_inline(fun) && FunNode._must_inline==0 ) fun.ideal_inline(true);
      assert !NodeUtil.leak();
    }
    for( int i=0; i<n.len  (); i++ ) if( _more_ideal(n.in (i)) ) return true;
    for( int i=0; i<n.nUses(); i++ ) if( _more_ideal(n.use(i)) ) return true;
    return false;
  }

}
