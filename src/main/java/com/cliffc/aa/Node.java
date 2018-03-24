package com.cliffc.aa;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;

/** an implementation of language AA
 */

// Sea-of-Nodes
public abstract class Node {
  static private int CNT=0;
  final int _uid=CNT++; // Unique ID, will have gaps, used to give a dense numbering to nodes

  // Defs.  Generally fixed length, ordered, nulls allowed, no unused trailing space
  Ary<Node> _defs;
  
  // Uses.  Generally variable length; unordered, no nulls, compressed, unused trailing space
  Ary<Node> _uses = new Ary<>(new Node[1],0);

  Node() { this(new Node[0]); }
  Node( Node... defs ) {
    _defs = new Ary<>(defs);
    for( Node def : defs ) def.add_use(this);
  }

  
  // Short string name
  abstract String str();
  private SB xstr(SB sb) { return sb.p(_uid).p("=").p(str()); }
  @Override public String toString() {
    SB sb = xstr(new SB()).p("(");
    boolean first=true;
    for( Node n : _defs ) { n.xstr(sb.p(first?"":",")); first=false; }
    return sb.p(")").toString();
  }
  
  // graph rewriting
  abstract Node ideal();

  // Compute the current best Type for this Node, based on the types of its inputs
  abstract Type value(GVNGCP gvn);
  
  Node add_def(Node n) {
    throw AA.unimpl();
  }
  // Strictly add uses (no defs)
  void add_use(Node n) { _uses.add(n); }
}

class RootNode extends Node {
  @Override String str() { return "root"; }
  @Override Node ideal() { return null; }
  @Override Type value(GVNGCP gvn) { throw AA.unimpl(); }
}

class ConNode extends Node {
  final Type _t;
  ConNode( Type t ) { _t=t; }
  @Override String str() { return _t.toString(); }
  @Override Node ideal() { return null; }
  @Override Type value(GVNGCP gvn) { return _t; }
  @Override public String toString() { return str(); }
}

class ApplyNode extends Node {
  ApplyNode( Node fun, Node arg0 ) { super(fun,arg0); }
  ApplyNode( Node fun, Node arg0, Node arg1 ) { super(fun,arg0,arg1); }
  @Override String str() { return "apply"; }
  @Override Node ideal() { return null; }
  @Override Type value(GVNGCP gvn) {
    Type fun = gvn.type(_defs.at(0));
    // if function is pure and all args are constant, eval immediately
    if( fun.is_pure() ) {
      
      throw AA.unimpl();
    }
    
    Type ret = fun.ret();
    if( ret==null ) throw AA.unimpl();
    return ret;
  }
}
