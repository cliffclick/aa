package com.cliffc.aa;

import com.cliffc.aa.node.*;

import java.util.HashMap;

public class Env implements AutoCloseable {
  final Env _par;
  ScopeNode _scope; // Lexical anchor; goes when this environment leaves scope
  private final HashMap<String,Type> _types; // user-typing type names
  Env( Env par ) {
    _par=par;
    _scope = new ScopeNode();
    _types = new HashMap<>();
    add(" control ",_scope);
  }

  public final static GVNGCM _gvn = new GVNGCM(false); // Pessimistic GVN, defaults to ALL, lifts towards ANY
  private final static Env TOP = new Env(null);        // Top-most lexical Environment
  public static ScopeNode top_scope() { return TOP._scope; }
  static { TOP.init(); }
  private void init() {
    _scope.add("math_pi",new ConNode<>(TypeFlt.PI));
    for( PrimNode prim : PrimNode.PRIMS )
      _scope.add_fun(prim._name,as_fun(prim));
    // Now that all the UnresolvedNodes have all possible hits for a name,
    // register them with GVN.
    for( Node val : _scope._defs )  _gvn.init0(val);
    _gvn.iter();
    Type.init0(_types);
    CallNode.init0(); // Done with adding primitives
    FunNode .init0(); // Done with adding primitives
    _gvn    .init0(); // Done with adding primitives
  }
  
  // Called during basic Env creation, this wraps a PrimNode as a full
  // 1st-class function to be passed about or assigned to variables.
  private EpilogNode as_fun( PrimNode prim ) {
    Type[] targs = prim._targs._ts;
    String[] args = prim._args;
    FunNode  fun = _gvn.init(new  FunNode(_scope, prim)); // Points to ScopeNode only
    ParmNode rpc = _gvn.init(new ParmNode(-1,"rpc",fun,_gvn.con(TypeRPC.ALL_CALL)));
    prim.add_def(null);         // Control for the primitive
    for( int i=0; i<args.length; i++ )
      prim.add_def(_gvn.init(new ParmNode(i,args[i],fun,_gvn.con(targs[i]))));
    PrimNode x = _gvn.init(prim);
    assert x==prim;
    return _gvn.init(new EpilogNode(fun,prim,rpc,fun));
  }

  public Node add( String name, Node val ) { return _scope.add(name,val); }

  // A new top-level Env, above this is the basic public Env with all the primitives
  static Env top() { return new Env(TOP); }

  // Close the current Env, making its lexical scope dead (and making dead
  // anything only pointed at by this scope).
  @Override public void close() {
    _scope.promote_forward_del_locals(_gvn,_par._par == null ? null : _par._scope);
    if( _scope.is_dead() ) return;
    if( _par._par == null ) {
      CallNode.reset_to_init0();
      FunNode .reset_to_init0();
      _gvn    .reset_to_init0();
      return;
    }
    // Whats left is function-ref generic entry points; promote to next outer scope
    while( _scope._uses._len > 0 ) {
      Node use = _scope._uses.at(0);
      int idx = use._defs.find(_scope);
      use.set_def(idx, _par._scope, _gvn); // Move it upscope
      if( use instanceof FunNode )
        //_par._scope.add(((FunNode)use)._name, _gvn.con(((FunNode)use)._tf));
        throw AA.unimpl();
    }
    _gvn.kill0(_scope);
  }

  // Test support, return top-level token type
  static Type lookup_valtype( String token ) { return lookup_valtype(TOP.lookup(token)); }
  static Type lookup_valtype( Node n ) {
    Type t = _gvn.type(n);
    if( t != TypeErr.CONTROL ) return t;
    if( n instanceof ProjNode ) // Get function type when returning a function
      return ((FunNode)(n.at(0).at(2)))._tf;
    throw AA.unimpl();
  }
  
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
    // local ScopeNode first, and then new shadowing Nodes will replace
    // shadowed nodes on a case-by-case basis.
    if( n != null ) return n;
    return _par == null ? null : _par.lookup(token);
  }

  // Lookup the name.  If the result is an UnresolvedNode of functions, filter out all
  // the wrong-arg-count functions.  Only returns nodes registered with GVN.
  Node lookup_filter( String token, GVNGCM gvn, int nargs ) {
    Node n = lookup(token);
    return n == null ? null : (n instanceof UnresolvedNode ? ((UnresolvedNode)n).filter(gvn,nargs) : n);
  }

  // Type lookup
  Type lookup_type( String token ) {
    Type t = _types.get(token);
    if( t != null ) return t;
    return _par == null ? null : _par.lookup_type(token);
  }
}
