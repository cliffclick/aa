package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.node.UnresolvedNode;

import java.util.concurrent.ConcurrentHashMap;

public class Env {
  final Env _par;
  final ConcurrentHashMap<String, Node> _refs;
  Env( Env par ) { _par=par; _refs = new ConcurrentHashMap<>(); }

  public final static GVNGCP _gvn = new GVNGCP(false); // Pessimistic GVN, defaults to ALL, lifts towards ANY
  public final static Node ROOT = new RootNode();      // The permanent graph anchor
  private final static Env TOP = new Env(null);        // Top-most lexical Environment
  static {
    TOP.add0(" control ",_gvn.xform(ROOT));
    TOP.add0("pi",_gvn.con(TypeFlt.Pi)); // TODO: Needs to be under Math.pi
    for( PrimNode prim : PrimNode.PRIMS ) TOP.add0(prim._name,as_fun(prim));
    // Now that all the UnresolvedNodes have all possible hits for a name,
    // register them with GVN.
    for( String k : TOP._refs.keySet() ) {
      Node n = TOP._refs.get(k);
      if( n instanceof UnresolvedNode )
        TOP._refs.put(k,_gvn.xform(n));
    }
  }
  static Env top() { return new Env(TOP); }

  private void add0( String name, Node prim ) { _refs.computeIfAbsent(name, key -> new UnresolvedNode()).add_def(prim); }
  void add( String name, Node ref ) {
    assert _refs.get(name)==null;
    _refs.put(name, ref );
  }

  // Called during basic Env creation, this wraps a PrimNode as a full
  // 1st-class function to be passed about or assigned to variables.
  static RetNode as_fun(PrimNode prim) {
    Type[] targs = prim._tf._ts._ts;
    String[] args = prim._args;
    FunNode fun = (FunNode)_gvn.init(new FunNode(prim._tf)); // Points to RootNode only
    prim.add_def(null);         // Control for the primitive
    for( int i=0; i<args.length; i++ )
      prim.add_def(_gvn.init(new ParmNode(i,args[i],fun,_gvn.con(targs[i]))));
    Node x = _gvn.init(prim);
    assert x==prim;
    Node rpc = _gvn.init(new ParmNode(args.length,"$rpc",fun,_gvn.con(TypeInt.TRUE)));
    return (RetNode)_gvn.init(new RetNode(fun,prim,rpc,1));
  }
  
  // Name lookup is the same for all variables, including function defs (which
  // are literally assigning a lambda to a ref).  Refs and Vars have a fixed
  // type (so can, for instance, assign a new function to a var as long as the
  // type signatures match).  Cannot re-assign to a ref, only var; vars only
  // available in loops.
  Node lookup( String token ) {
    if( token == null ) return null; // Handle null here, easier on parser
    // Lookup
    Node n = _refs.get(token);
    // Lookups stop at 1st hit - because shadowing is rare, and so will be
    // handled when it happens and not on every lookup.  Shadowing is supported
    // at name-insertion time, where all shadowed Nodes are inserted into the
    // local UnresolvedNode first, and then new shadowing Nodes will replace
    // shadowed nodes on a case-by-case basis.
    if( n != null ) return n;
    return _par == null ? null : _par.lookup(token);
  }

  // Lookup the name.  If the result is an Unresolved, filter out all the
  // wrong-arg-count functions.
  Node lookup_filter( String token, int nargs ) {
    Node unr = lookup(token);
    if( unr == null ) return null;
    if( !(unr instanceof UnresolvedNode) ) return unr;
    return ((UnresolvedNode)unr).filter(nargs);
  }
}
