package com.cliffc.aa.node;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.VBitSet;

import java.util.function.Consumer;

public abstract class Work implements Consumer<Node> {
  final Ary<Node> _work = new Ary<>(new Node[1],0);
  final VBitSet _on = new VBitSet();
  public Node add(Node n) {
    if( !_on.tset(n._uid) ) _work.push(n);
    return n;
  }
  // True if apply() called, false if worklist is empty
  public boolean do1() {
    while(true) {
      Node n=pop();
      if( n==null ) return false;
      if( !n.is_dead() ) { accept(n); return true; }
    }
  }
  public abstract void accept(Node n);

  public Node pop() {
    if( _work._len==0 ) return null;
    Node n = _work.pop();
    _on.clear(n._uid);
    return n;
  }

  public boolean isEmpty() { return _work._len==0; }
  public boolean on(Node n) { return _on.test(n._uid); }
  public void clear() { _work.clear(); _on.clear(); }
  @Override public String toString() { return _on.toString(); }
}
