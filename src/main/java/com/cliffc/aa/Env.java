package com.cliffc.aa;

import com.cliffc.aa.node.*;

import java.lang.AutoCloseable;
import java.util.BitSet;
import java.util.HashMap;

public class Env implements AutoCloseable {
  final Env _par;
  ScopeNode _scope; // Lexical anchor; goes when this environment leaves scope
  Node _ret;   // Return result
  private final HashMap<String,Type> _types;
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
  }
  
  // Called during basic Env creation, this wraps a PrimNode as a full
  // 1st-class function to be passed about or assigned to variables.
  private TypeFun as_fun( PrimNode prim ) {
    Type[] targs = prim._targs._ts;
    String[] args = prim._args;
    FunNode fun = _gvn.init(new FunNode(_scope, prim)); // Points to ScopeNode only
    prim.add_def(null);         // Control for the primitive
    for( int i=0; i<args.length; i++ )
      prim.add_def(_gvn.init(new ParmNode(i,args[i],fun,_gvn.con(targs[i]))));
    PrimNode x = _gvn.init(prim);
    assert x==prim;
    ProjNode proj = _gvn.init(new ProjNode(_gvn.init(new RetNode(fun,prim,fun)),1));
    fun.init(proj);
    return fun._tf;
  }

  public Node add( String name, Node val ) { return _scope.add(name,val); }

  // A new top-level Env, above this is the basic public Env with all the primitives
  static Env top() { return new Env(TOP); }

  // Close the current Env, making its lexical scope dead (and making dead
  // anything only pointed at by this scope).
  @Override public void close() {
    assert check_live(_gvn._live);
    _scope.set_def(0,null,_gvn); // Kill control
    if( _scope.is_dead() ) return;
    while( _scope._uses._len > 0 ) {
      Node fuse = _scope._uses.pop();
      // Allow only forward-ref func decls here
      if( !(fuse instanceof FunNode) ) throw AA.unimpl();
      FunNode fun = (FunNode)fuse;
      for( Node use : fun._uses ) assert use instanceof RetNode;
      // Push forward refs to the next outer scope
      if( _par._par==null ) {   // Never defined at top level, so null out
        fun._defs.set(1,null);
      } else {                  // Push to outer scope
        fun._defs.set(1, _par._scope);
        _par._scope._uses.add(fun);
        _par._scope.add(fun._name, _gvn.con(fun._tf));
      }
    }
    _gvn.kill0(_scope);
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
    FunNode.FUNS.walk(bs);
    return _par == null ? bs : _par.check_live0(bs);
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

  // Lookup the name.  If the result is an ConNode of functions, filter out all
  // the wrong-arg-count functions.  Only returns nodes registered with GVN.
  Type lookup_filter( String token, GVNGCM gvn, int nargs ) {
    Node n = lookup(token);
    return n == null ? null : gvn.type(n).filter(nargs);
  }

  // Type lookup
  Type lookup_type( String token ) {
    Type t = _types.get(token);
    if( t != null ) return t;
    return _par == null ? null : _par.lookup_type(token);
  }
}
