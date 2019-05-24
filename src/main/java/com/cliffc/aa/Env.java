package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;

public class Env implements AutoCloseable {
  final Env _par;
  ScopeNode _scope; // Lexical anchor; goes when this environment leaves scope
  Env( Env par ) {
    _par = par;
    ScopeNode scope = new ScopeNode();
    if( par != null ) {
      scope.update(" control ",par._scope.get(" control "), GVN,true);
      scope.update(" memory " ,par._scope.get(" memory " ), GVN,true);
    }
    _scope = GVN.init(scope);
  }

  public final static GVNGCM GVN; // Initial GVN, defaults to ALL, lifts towards ANY
  public final static StartNode START; // Program start values (control, empty memory, cmd-line args)
         final static CProjNode CTL_0; // Program start value control
         final static MProjNode MEM_0; // Program start value memory
  public final static   ConNode ALL_CTRL;
  private final static int NINIT_CONS;
  private final static Env TOP; // Top-most lexical Environment, has all primitives, unable to be removed
  static {
    GVN = new GVNGCM();     // Initial GVN, defaults to ALL, lifts towards ANY
    // Initial control, memory, args, program state
    START = new StartNode();
    CTL_0 = GVN.init(new CProjNode(START,0));
    MEM_0 = GVN.init(new MProjNode(START,1));
    ALL_CTRL = GVN.init(new ConNode<>(Type.CTRL));
    TOP    = new Env(null);        // Top-most lexical Environment
    TOP.install_primitives();
    NINIT_CONS = START._uses._len;
  }
  private void install_primitives() {
    _scope.add_def(_scope); // Self-hook to prevent deletion
    _scope  .init0(); // Add base types
    _scope.update(" control ", CTL_0, GVN,true);
    _scope.update(" memory " , MEM_0, GVN,true);
    for( PrimNode prim : PrimNode.PRIMS )
      _scope.add_fun(prim._name,(EpilogNode) GVN.xform(prim.as_fun(GVN)));
    for( PrimNode prim : LibCallNode.LIBCALLS )
      _scope.add_fun(prim._name,(EpilogNode) GVN.xform(prim.as_fun(GVN)));
    // Now that all the UnresolvedNodes have all possible hits for a name,
    // register them with GVN.
    for( Node val : _scope._defs )  GVN.init0(val);
    // Top-level constants
    _scope.update("math_pi", GVN.con(TypeFlt.PI),null,false);
    // Run the worklist dry
    GVN.iter();
    BitsAlias.init0(); // Done with adding primitives
    BitsFun  .init0(); // Done with adding primitives
    BitsRPC  .init0(); // Done with adding primitives
    GVN      .init0(); // Done with adding primitives
  }
  
  // A new top-level Env, above this is the basic public Env with all the primitives
  public static Env top() { return new Env(TOP); }
  
  Node update( String name, Node val, GVNGCM gvn, boolean mutable ) { return _scope.update(name,val,gvn,mutable); }
  Node add_fun( String name, Node val ) { return _scope.add_fun(name,(EpilogNode)val); }

  void add_type( String name, Type t ) { _scope.add_type(name,t); }
  
  // Close the current Env, making its lexical scope dead (and making dead
  // anything only pointed at by this scope).
  @Override public void close() {
    ScopeNode pscope = _par._scope;
    _scope.promote_forward_del_locals(GVN,_par._par == null ? null : pscope);
    if( _scope.is_dead() ) return;
    // Closing top-most scope (exiting compilation unit)?
    if( _par._par == null ) {   // Then reset global statics to allow another compilation unit
      BitsAlias.reset_to_init0(); // Done with adding primitives
      BitsFun  .reset_to_init0(); // Done with adding primitives
      BitsRPC  .reset_to_init0(); // Done with adding primitives
      GVN      .reset_to_init0(); // Done with adding primitives
      // StartNode is used by global constants, which in turn are only used by
      // dead cycles.
      while( START._uses._len > NINIT_CONS ) {
        Node x = START._uses.pop();
        assert !GVN.touched(x); // Uses are all dead (but not reclaimed because in a cycle)
      }
      return;
    }
    // Whats left is function-ref generic entry points which promote to next
    // outer scope, and control-users which promote to the Scope's control.
    while( _scope._uses._len > 0 ) {
      Node use = _scope._uses.at(0);
      assert use != pscope;
      int idx = use._defs.find(_scope);
      GVN.set_def_reg(use,idx, idx==0 ? pscope.get(" control ") : pscope);
    }
    GVN.kill(_scope);
  }

  // Test support, return top-level token type
  static Type lookup_valtype( String token ) { return lookup_valtype(TOP.lookup(token)); }
  // Top-level exit type lookup
  private static Type lookup_valtype( Node n ) {
    Type t = GVN.type(n);
    if( t != Type.CTRL ) return t;
  //  if( n instanceof ProjNode ) // Get function type when returning a function
  //    return ((FunNode)(n.in(0).in(2)))._tf;
    throw AA.unimpl();
  }

  // Name lookup is the same for all variables, including function defs (which
  // are literally assigning a lambda to a ref).  Refs and Vars have a fixed
  // type (so can, for instance, assign a new function to a var as long as the
  // type signatures match).  Cannot re-assign to a ref, only var; vars only
  // available in loops.  Only returns nodes registered with GVN.
  public Node lookup( String token ) {
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
    Type t = _scope.get_type(token);
    if( t != null ) return t;
    return _par == null ? null : _par.lookup_type(token);
  }
  public boolean is_mutable( String name ) {
    Integer ii = _scope.get_idx(name);
    return ii == null ? _par.is_mutable(name) : _scope.is_mutable(ii);
  }

}
