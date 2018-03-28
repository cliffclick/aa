package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.node.UnresolvedNode;

import java.util.concurrent.ConcurrentHashMap;

class Env {
  final Env _par;
  final ConcurrentHashMap<String, UnresolvedNode> _refs;
  private Env( Env par ) { _par=par; _refs = new ConcurrentHashMap<>(); }

  private final static Env TOP = new Env(null);
  static {
    TOP.add("pi",new ConNode<>(TypeFlt.Pi)); // TODO: Needs to be under Math.pi
    for( PrimNode prim : PrimNode.PRIMS ) TOP.add(prim._name,prim);
  }
  static Env top() { return new Env(TOP); }

  void add( String name, Node prim ) {
    _refs.computeIfAbsent(name, key -> new UnresolvedNode()).add_def(prim);
  }
  
  // Name lookup is the same for all variables, including function defs (which
  // are literally assigning a lambda to a ref).  Refs and Vars have a fixed
  // type (so can, for instance, assign a new function to a var as long as the
  // type signatures match).  Cannot re-assign to a ref, only var; vars only
  // available in loops.
  UnresolvedNode lookup( String token ) {
    if( token == null ) return null; // Handle null here, easier on parser
    // Lookup
    UnresolvedNode unr = _refs.get(token);
    // Lookups stop at 1st hit - because shadowing is rare, and so will be
    // handled when it happens and not on every lookup.  Shadowing is supported
    // at name-insertion time, where all shadowed Nodes are inserted into the
    // local UnresolvedNode first, and then new shadowing Nodes will replace
    // shadowed nodes on a case-by-case basis.
    if( unr != null ) return unr;
    return _par == null ? null : _par.lookup(token);
  }
  
  Node lookup_filter( String token, GVNGCP gvn, Type t ) {
    UnresolvedNode unr = lookup(token);
    return unr == null ? null : unr.filter(gvn,t);
  }
}
