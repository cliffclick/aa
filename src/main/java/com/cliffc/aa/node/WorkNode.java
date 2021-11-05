package com.cliffc.aa.node;

import com.cliffc.aa.util.*;
import com.cliffc.aa.tvar.UQNodes;

import java.util.function.Function;

public abstract class WorkNode extends Work<Node> implements Function<Node,Node> {
  public final String _name;
  public final boolean _replacing;
  public WorkNode(String name, boolean replacing) { _name=name; _replacing = replacing; }
  public void add(Ary<Node> ns) { for( Node n : ns )  add(n); }
  public void add(UQNodes uq) {  if( uq!=null ) for( Node n : uq.values() )  add(n); }
  public abstract Node apply(Node n);
  @Override public String toString() { return _name+keySet().toString(); }
}
