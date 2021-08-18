package com.cliffc.aa.node;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.VBitSet;

import java.util.function.Function;

public abstract class Work implements Function<Node,Node> {
  public final Ary<Node> _work = new Ary<>(new Node[1],0);
  final VBitSet _on = new VBitSet();
  public final String _name;
  public final boolean _replacing;
  public Work(String name, boolean replacing) { _name=name; _replacing = replacing; }
  public int len() { return _work._len; }
  public <N extends Node> N add(N n) {
    if( n!=null && !_on.tset(n._uid) ) _work.push(n);
    return n;
  }
  public abstract Node apply(Node n);

  public Node pop() {
    if( _work._len==0 ) return null;
    Node n = _work.pop();
    _on.clear(n._uid);
    return n;
  }
  public Node at(int i) { return _work.at(i); }
  public void del(int i) { _on.clear(at(i)._uid); _work.del(i); }
  public void del(Node n) {
    if( !_on.get(n._uid) ) return;
    _on.clear(n._uid);
    _work.del(n);
  }

  public boolean isEmpty() { return _work._len==0; }
  public boolean on(Node n) { return _on.test(n._uid); }
  public void clear() { _work.clear(); _on.clear(); }
  @Override public String toString() { return _name+_on.toString(); }
}
