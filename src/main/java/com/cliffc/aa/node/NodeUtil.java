package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.util.Ary;

import java.lang.Iterable;
import java.util.Iterator;

import static com.cliffc.aa.AA.TODO;

// Sea-of-Nodes
public abstract class NodeUtil {

  // Non-allocating iterator; pulls iterators from a pool.  The hard part is
  // telling when an iterator ends early, to avoid leaking.  This is not
  // exactly asserted for, so some leaks may happen.
  
  public static class Iter implements Iterator<Node>, Iterable<Node> {
    private static final Ary<Iter> POOL = new Ary<>(Iter.class);
    private static int CNT=0; // Number of Iters made, helps to track leaks
    Node[] _ns;               // Nodes
    int _len;                 // Number of Nodes actually in ns
    int _i;                   // Iterator index, 0 <= i < len, or -99
    static Iter get(Node[] ns, int len) {
      if( POOL.isEmpty() ) { assert CNT<100; CNT++; new Iter().end(); }
      return POOL.pop().init(ns,len);
    }
    @Override public Iter iterator() { return this; }
    boolean end() { _i=-99; _ns=null; _len=-1; POOL.push(this); return false; }
    private Iter init(Node[] ns, int len) { assert _i==-99; _i=0; _ns=ns; _len=len; return this; }
    @Override public boolean hasNext() {  assert _i>=0; return _i < _len || end(); }
    @Override public Node next() { return _ns[_i++]; }
    @Override public void remove() { throw TODO(); }
  }

  
  // Fold control copies
  public static Node fold_ccopy(Node x) {
    Node cc = x.in(0).isCopy(0);
    if( cc == null ) return null;
    if( cc == x ) return Env.ANY; // Dead self-cycle
    Env.GVN.add_reduce_uses(x);
    return Env.GVN.add_reduce(x.setDef(0,cc));
  }

}
