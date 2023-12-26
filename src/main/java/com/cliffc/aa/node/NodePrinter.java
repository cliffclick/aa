package com.cliffc.aa.node;

import com.cliffc.aa.util.*;
import static com.cliffc.aa.AA.TODO;

// Sea-of-Nodes
public abstract class NodePrinter {

  // Another bulk pretty-printer.  Makes more effort at basic-block grouping.
  public static String prettyPrint(Node node, int depth) {
    throw TODO();
  }
  public static String prettyPrint(Ary<Node> roots) {
    throw TODO();
  }
  
  //// Short string name
  //public String xstr() { return STRS[_op]; } // Self short name
  //String  str() { return xstr(); }    // Inline longer name
  //@Override public String toString() { return dump(0,new SB(),null, null, null, null, false,false).toString(); }
  //// Dump
  //public String dump( int max ) { return dump(max,is_prim(),false,false); }
  //// Dump including primitives
  //public String dump( int max, boolean prims, boolean plive, boolean ptvar ) { return dump(0,max,new VBitSet(), new SB(),null, null, null, null,prims,plive,ptvar).toString();  }
  //// Dump one node, no recursion
  //private SB dump( int d, SB sb, VBitSet typebs, NonBlockingHashMapLong dups, VBitSet hmt_bs, VBitSet hmt_dups, boolean plive, boolean ptvar ) {
  //  String xs = String.format("%s%4d: %-7.7s ",plive ? _live : "",_uid,xstr());
  //  sb.i(d).p(xs);
  //  if( is_dead() ) return sb.p("DEAD");
  //  for( Node n : _defs ) sb.p(n == null ? "____ " : String.format("%4d ",n._uid));
  //  sb.p(" [[");
  //  for( Node n : _uses ) sb.p(String.format("%4d ",n._uid));
  //  sb.p("]]  ");
  //  sb.p(str()).s();
  //  if( _val==null ) sb.p("----");
  //  else _val.str(sb, typebs, dups, true, false); // Print a type using the shared dups printer
  //  if( ptvar && _tvar!=null ) _tvar.str(sb.p(" - "), hmt_bs, hmt_dups, true, false);
  //
  //  return sb;
  //}
  //// Dump one node IF not already dumped, no recursion
  //private void dump(int d, VBitSet bs, SB sb, VBitSet typebs, NonBlockingHashMapLong dups, VBitSet hmt_bs, VBitSet hmt_dups, boolean plive, boolean ptvar ) {
  //  if( bs.tset(_uid) ) return;
  //  dump(d,sb,typebs,dups,hmt_bs,hmt_dups,plive,ptvar).nl();
  //}
  //// Recursively print, up to depth
  //private SB dump( int d, int max, VBitSet bs, SB sb, VBitSet typebs, NonBlockingHashMapLong<String> dups, VBitSet hmt_bs, VBitSet hmt_dups, boolean prims, boolean plive, boolean ptvar ) {
  //  if( bs.tset(_uid) ) return sb;
  //  if( d < max ) {    // Limit at depth
  //    // Print parser scopes first (deepest)
  //    for( Node n : _defs ) if( n instanceof ScopeNode ) n.dump(d+1,max,bs,sb,typebs,dups,hmt_bs,hmt_dups,prims,plive,ptvar);
  //    // Print constants early
  //    for( Node n : _defs ) if( n instanceof ConNode ) n.dump(d+1,max,bs,sb,typebs,dups,hmt_bs,hmt_dups,prims,plive,ptvar);
  //    // Do not recursively print root Scope, nor primitives.
  //    // These are too common, and uninteresting.
  //    for( Node n : _defs ) if( n != null && (!prims && n.is_prim() && n._defs._len > 3) ) bs.set(n._uid);
  //    // Recursively print most of the rest, just not the multi-node combos and
  //    // Unresolve & FunPtrs.
  //    for( Node n : _defs )
  //      if( n != null && !n.isMultiHead() && !n.is_multi_tail() && !(n instanceof FunPtrNode) )
  //        n.dump(d+1,max,bs,sb,typebs,dups,hmt_bs,hmt_dups,prims,plive,ptvar);
  //    // Print FunPtrs, which typically catch whole functions.
  //    for( Node n : _defs )
  //      if( n instanceof FunPtrNode )
  //        n.dump(d+1,max,bs,sb,typebs,dups,hmt_bs,hmt_dups,prims,plive,ptvar);
  //    // Print anything not yet printed, including multi-node combos
  //    for( Node n : _defs ) if( n != null && !n.isMultiHead() ) n.dump(d+1,max,bs,sb,typebs,dups,hmt_bs,hmt_dups,prims,plive,ptvar);
  //    for( Node n : _defs ) if( n != null ) n.dump(d+1,max,bs,sb,typebs,dups,hmt_bs,hmt_dups,prims,plive,ptvar);
  //  }
  //  // Print multi-node combos all-at-once, including all tails even if they
  //  // exceed the depth limit by 1.
  //  Node x = is_multi_tail() ? in(0) : this;
  //  if( x != null && x.isMultiHead() ) {
  //    int dx = d+(x==this?0:1);
  //    // Print all tails paths, all at once - nothing recursively below the tail
  //    for( Node n : x._uses )
  //      if( n.is_multi_tail() )
  //        for( Node m : n._defs )
  //          if( dx<max) m.dump(dx+1,max,bs,sb,typebs,dups,hmt_bs,hmt_dups,prims,plive,ptvar);
  //    if( x==this ) bs.clear(_uid); // Reset for self, so prints right now
  //    x.dump(dx,bs,sb,typebs,dups,hmt_bs,hmt_dups,plive,ptvar); // Conditionally print head of combo
  //    // Print all combo tails, if not already printed
  //    if( x!=this ) bs.clear(_uid); // Reset for self, so prints in the mix below
  //    for( Node n : x._uses ) if( n.is_multi_tail() ) n.dump(dx-1,bs,sb,typebs,dups,hmt_bs,hmt_dups,plive,ptvar);
  //    return sb;
  //  } else { // Neither combo head nor tail, just print
  //    return dump(d,sb,typebs,dups,hmt_bs,hmt_dups,plive,ptvar).nl();
  //  }
  //}
  //private boolean is_multi_tail() { return _op==OP_PARM || _op==OP_PHI || _op==OP_PROJ || _op==OP_CPROJ; }
  //boolean is_CFG() { return false; }
  //
  //public String dumprpo( boolean prims, boolean plive, boolean ptvar ) {
  //  Ary<Node> nodes = new Ary<>(new Node[1],0);
  //  postorder(nodes,new VBitSet());
  //  // Walk the node list and count Type duplicates.  This means the same types
  //  // use the same Dup name on every node in the entire print.
  //  NonBlockingHashMapLong<String> dups = new NonBlockingHashMapLong<>();
  //  VBitSet typebs = new VBitSet();
  //  Type.UCnt ucnt = new Type.UCnt();
  //  VBitSet hmt_bs   = new VBitSet();
  //  VBitSet hmt_dups = new VBitSet();
  //  for( Node n : nodes ) {
  //    n._val ._str_dups(typebs, dups, ucnt, false);
  //    n._live._str_dups(typebs, dups, ucnt, false);
  //    if( n._tvar!=null ) n._tvar._get_dups(hmt_bs,hmt_dups,true,prims);
  //  }
  //  typebs.clr();
  //  hmt_bs.clr();
  //
  //  // Dump in reverse post order
  //  SB sb = new SB();
  //  Node prior = null;
  //  for( int i=nodes._len-1; i>=0; i-- ) {
  //    Node n = nodes.at(i);
  //    if( n.is_prim() && !prims )
  //      continue;               // Visited, but do not print
  //    // Add a nl after the last of a multi-tail sequence.
  //    if( (prior != null && prior.is_multi_tail() && !n.is_multi_tail()) ||
  //        // Add a nl before the start of a multi-head sequence.
  //        n.isMultiHead() )
  //      sb.nl();
  //    if( n._op==OP_FUN ) _header((FunNode)n,sb);
  //    n.dump(0,sb,typebs,dups,hmt_bs,hmt_dups,plive,ptvar).nl();
  //    if( n._op==OP_RET && n.in(4) instanceof FunNode ) _header((FunNode)n.in(4),sb);
  //    prior = n;
  //  }
  //  return sb.toString();
  //}
  //private static void _header(FunNode fun, SB sb) {
  //  sb.p("============ ").p(fun==null?"null":fun.name()).p(" ============").nl();
  //}
  //private void postorder( Ary<Node> nodes, VBitSet bs ) {
  //  if( bs.tset(_uid) ) return;
  //  // If CFG, walk the CFG first.  Do not walk thru Returns (into Calls) as
  //  // this breaks up the whole- functions-at-once.
  //  if( is_CFG() && _op!=OP_RET && is_copy(0)==null ) {
  //    // Walk any CProj first.
  //    for( Node use : _uses )
  //      if( use._op == OP_CPROJ )
  //        use.postorder(nodes,bs);
  //    // Walk the CFG, walking CallEpis last
  //    for( Node use : _uses )
  //      if( !(use instanceof CallEpiNode) && use.is_CFG() )
  //        use.postorder(nodes,bs);
  //    for( Node use : _uses )
  //      if(  (use instanceof CallEpiNode) && use.is_CFG() )
  //        use.postorder(nodes,bs);
  //  }
  //
  //  // Walk the rest (especially data).  Since visit bits are set on the CFGs
  //  // its OK to walk them also.  Calls are special, since their Proj's feed
  //  // into a Fun's Parms.  We want the Fun to walk its own Parms, in order so
  //  // ignore these edges.  Since the Parms are all reachable from the Fun they
  //  // get walked eventually.
  //  if( (_op != OP_CALL || is_copy(0)!=null ) && _op!=OP_RET ) {
  //    if( _op!=OP_SPLIT || _uses._len!=2 ) {
  //      for( Node use : _uses )
  //        use.postorder(nodes,bs);
  //    }  else {                 // For MemSplit, walk the "busy" side first
  //      Node p0 = _uses.at(0), p1 = _uses.at(1);
  //      if( ((ProjNode)p0)._idx==1 ) { p0=p1; p1=_uses.at(0); } // Swap
  //      p1.postorder(nodes,bs);
  //      p0.postorder(nodes,bs);
  //    }
  //  }
  //
  //  // Slight PO tweak: heads and tails together.
  //  if( isMultiHead() )
  //    for( Node use : _uses )
  //      if( use.is_multi_tail() )
  //        nodes.push(use);
  //  if( !is_multi_tail() ) nodes.push(this);
  //}


}
