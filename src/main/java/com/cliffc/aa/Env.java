package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.node.UnresolvedNode;

import java.lang.AutoCloseable;
import java.util.BitSet;

public class Env implements AutoCloseable {
  final Env _par;
  final ScopeNode _scope; // Lexical anchor; goes when this environment leaves scope
  Node _ret;   // Return result
  Env( Env par ) {
    _par=par;
    _scope = new ScopeNode();
    // Copy control thru from parent
    if( par != null ) add(" control ",par._scope.get(" control "));
  }

  public final static GVNGCM _gvn = new GVNGCM(false); // Pessimistic GVN, defaults to ALL, lifts towards ANY
  private final static Env TOP = new Env(null);        // Top-most lexical Environment
  public static ScopeNode top_scope() { return TOP._scope; }
  static { TOP.init(); }
  private void init() {
    _scope.add(" control ",_scope); // Self-add
    _scope.add("math_pi",new ConNode<>(TypeFlt.Pi));
    for( PrimNode prim : PrimNode.PRIMS )
      _scope.add_fun(prim._name,as_fun(prim));
    // Now that all the UnresolvedNodes have all possible hits for a name,
    // register them with GVN.
    for( Node val : _scope._defs )  _gvn.init0(val);
  }
  
  // Called during basic Env creation, this wraps a PrimNode as a full
  // 1st-class function to be passed about or assigned to variables.
  private static RetNode as_fun( PrimNode prim ) {
    Type[] targs = prim._tf._ts._ts;
    String[] args = prim._args;
    FunNode fun = (FunNode)_gvn.init(new FunNode(prim._tf)); // Points to ScopeNode only
    prim.add_def(null);         // Control for the primitive
    for( int i=0; i<args.length; i++ )
      prim.add_def(_gvn.init(new ParmNode(i+1,args[i],fun,_gvn.con(targs[i]))));
    Node x = _gvn.init(prim);
    assert x==prim;
    Node rpc = _gvn.init(new ParmNode(args.length+1,"$rpc",fun,_gvn.con(TypeInt.TRUE)));
    return (RetNode)_gvn.init(new RetNode(fun,prim,rpc,1));
  }

  public Node add( String name, Node val ) { return _scope.add(name,val); }

  // A new top-level Env, above this is the basic public Env with all the primitives
  static Env top() { return new Env(TOP); }

  // Close the current Env, making its lexical scope dead (and making dead
  // anything only pointed at by this scope).
  @Override public void close() {
    assert check_live(_gvn._live);
    _gvn.kill_new(_scope);
  }

  // Check all reachable via graph-walk equals recorded live bits
  private boolean check_live(BitSet live) {
    BitSet rech = check_live0(new BitSet());
    if( rech.equals(live) ) return true;
    BitSet bs0 = (BitSet)live.clone();  bs0.andNot(rech);
    BitSet bs1 = (BitSet)rech.clone();  bs1.andNot(live);
    System.out.println("Reported live but not reachable: "+bs0);
    System.out.println("Reachable but not reported live: "+bs1);
    return false;
  }
    
  private BitSet check_live0(BitSet bs) {
    _scope.walk(bs);
    if( _ret != null ) _ret.walk(bs); // Also walk return value
    return _par == null ? bs : _par.check_live0(bs);
  }

  // Test support, return top-level token type
  static Type lookup_type( String token ) { return _gvn.type(TOP.lookup(token)); }
  
  // Name lookup is the same for all variables, including function defs (which
  // are literally assigning a lambda to a ref).  Refs and Vars have a fixed
  // type (so can, for instance, assign a new function to a var as long as the
  // type signatures match).  Cannot re-assign to a ref, only var; vars only

  // available in loops.  Only returns nodes registered with GVN.
  Node lookup( String token ) {
    if( token == null ) return null; // Handle null here, easier on parser
    // Lookup
    Node n = _scope.get(token);
    // Lookups stop at 1st hit - because shadowing is rare, and so will be
    // handled when it happens and not on every lookup.  Shadowing is supported
    // at name-insertion time, where all shadowed Nodes are inserted into the
    // local UnresolvedNode first, and then new shadowing Nodes will replace
    // shadowed nodes on a case-by-case basis.
    if( n != null ) return n;
    return _par == null ? null : _par.lookup(token);
  }

  // Lookup the name.  If the result is an Unresolved, filter out all the
  // wrong-arg-count functions.  Only returns nodes registered with GVN.
  Node lookup_filter( String token, int nargs ) {
    Node unr = lookup(token);
    if( unr == null ) return null;
    if( !(unr instanceof UnresolvedNode) ) return unr;
    return ((UnresolvedNode)unr).filter(nargs);
  }
}
