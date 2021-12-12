package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.*;
import com.cliffc.aa.tvar.UQNodes;

public class WorkNode extends Work<Node> {
  public final String _name;
  public WorkNode(String name) { super(AA.RSEED); _name=name; }
  public void add(Ary<Node> ns) { for( Node n : ns )  add(n); }
  public void add(UQNodes uq) {  if( uq!=null ) for( Node n : uq.values() )  add(n); }
  @Override public String toString() { return _name+super.toString(); }

  // Pull from worklist (order depends on AA.RSEED), until finding something not-dead.
  @Override public Node pop() {
    while( true ) {
      Node n = super.pop();
      if( n==null || !n.is_dead() ) return n;
    }
  }
}
