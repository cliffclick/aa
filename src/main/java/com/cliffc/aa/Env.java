package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;

public class Env implements AutoCloseable {
  final Env _par;
  ScopeNode _scope;  // Lexical anchor; goes when this environment leaves scope
  Env( Env par, boolean closure ) {
    _par = par;
    ScopeNode scope = new ScopeNode(closure);
    if( par != null ) {
      scope.set_ctrl(par._scope.ctrl(),GVN);
      NewObjNode nnn = GVN.init(new NewObjNode(closure,scope.ctrl())).keep();
      Node frm = GVN.xform(new OProjNode(nnn,0));
      Node ptr = GVN.xform(new  ProjNode(nnn,1));
      scope.set_ptr (ptr,GVN);  // Address for 'nnn', the local stack frame
      MemMergeNode mem = new MemMergeNode(par._scope.mem(),frm,nnn.<NewObjNode>unhook()._alias);
      scope.set_active_mem(mem,GVN);  // Memory includes local stack frame
      CLOSURES = CLOSURES.meet(BitsAlias.make0(nnn._alias));
    }
    _scope = scope;
  }

  public  final static GVNGCM GVN; // Initial GVN, defaults to ALL, lifts towards ANY
  public  final static  StartNode START; // Program start values (control, empty memory, cmd-line args)
  public  final static  CProjNode CTL_0; // Program start value control
          final static       Node MEM_0; // Program start value memory
  private final static       Node PTR_0; // Program start stack frame address
  private final static       Node OBJ_0; // Program start stack frame memory
  public  final static NewObjNode STK_0; // Program start stack frame (has primitives)
  public  final static    ConNode ALL_CTRL;
          final static int LAST_START_UID;
  private final static int NINIT_CONS;
          final static Env TOP; // Top-most lexical Environment, has all primitives, unable to be removed
  public        static BitsAlias CLOSURES;

  static {
    GVN = new GVNGCM();      // Initial GVN, defaults to ALL, lifts towards ANY
    // Initial control & memory
    START        =          new  StartNode(       ) ;
    CTL_0        = GVN.init(new  CProjNode(START,0));
    Node all_mem = GVN.init(new  MProjNode(START,1));
    // Top-level closure defining all primitives
    STK_0        =          new NewObjNode(true,CTL_0).keep();
    PTR_0        = GVN.init(new   ProjNode(STK_0,1));
    OBJ_0        =          new  OProjNode(STK_0,0) ;
    CLOSURES = BitsAlias.make0(STK_0._alias);

    MEM_0 = GVN.init(new MemMergeNode(all_mem,OBJ_0,STK_0._alias)).keep();
    // Top-level default values; ALL_CTRL is used by declared functions to
    // indicate that future not-yet-parsed code may call the function.
    ALL_CTRL = GVN.init(new ConNode<>(Type.CTRL));
    // Used to reset between tests
    LAST_START_UID = ALL_CTRL._uid;
    // Top-most (file-scope) lexical environment
    TOP    = new Env(null,true);
    TOP.install_primitives();
    // Used to reset between tests
    NINIT_CONS = START._uses._len;
  }
  private void install_primitives() {
    _scope.init0();             // Add base types
    for( PrimNode prim : PrimNode.PRIMS )
      STK_0.add_fun(null,prim._name,(FunPtrNode) GVN.xform(prim.as_fun(GVN)), GVN);
    for( IntrinsicNewNode lib : IntrinsicNewNode.INTRINSICS )
      STK_0.add_fun(null,lib ._name,(FunPtrNode) GVN.xform(lib .as_fun(GVN)), GVN);
    // Top-level constants
    STK_0.create_active("math_pi", GVN.con(TypeFlt.PI),TypeStruct.ffinal(),GVN);
    // Now that all the UnresolvedNodes have all possible hits for a name,
    // register them with GVN.
    for( Node val : STK_0._defs )  if( val instanceof UnresolvedNode ) GVN.init0(val);
    _scope.set_ctrl(CTL_0, GVN);
    _scope.set_mem (MEM_0, GVN);
    _scope.set_ptr (PTR_0, GVN);
    GVN.rereg(STK_0,STK_0.value(GVN));
    GVN.rereg(OBJ_0,OBJ_0.value(GVN));
    // Run the worklist dry
    GVN.iter();
    BitsAlias.init0(); // Done with adding primitives
    BitsFun  .init0(); // Done with adding primitives
    BitsRPC  .init0(); // Done with adding primitives
    FunNode  .init0(); // Done with adding primitives
    GVN      .init0(); // Done with adding primitives
  }

  // A new top-level Env, above this is the basic public Env with all the primitives
  public static Env top() { return new Env(TOP,true); }

  // Wire up an early function exit
  Node early_exit( Parse P, Node val ) {
    return _scope.is_closure() ? P.do_exit(_scope,val) : _par.early_exit(P,val); // Hunt for an early-exit-enabled scope
  }

  // Close any currently open closure, and remove its alias from the set of
  // active closure aliases (which are otherwise available to all function
  // definitions getting parsed).
  public void close_closure( GVNGCM gvn ) {
    Node ptr = _scope.ptr();
    if( ptr == null ) return;   // Already done
    NewObjNode stk = _scope.stk();
    CLOSURES = CLOSURES.clear(stk._alias);
    for( Node use : stk._uses )
      gvn.add_work(use);        // Scope object going dead, trigger following projs to cleanup
    _scope.set_ptr(null,gvn);   // Clear pointer to closure
  }

  // Close the current Env and lexical scope.
  @Override public void close() {
    ScopeNode pscope = _par._scope;
    // Promote forward refs to the next outer scope
    if( pscope != null && pscope != TOP._scope)
      _scope.stk().promote_forward(GVN,pscope.stk());
    close_closure(GVN);
    // Whats left is function-ref generic entry points which promote to next
    // outer scope, and control-users which promote to the Scope's control.
    assert _scope._uses.isEmpty();
    _scope.unkeep(GVN);
    assert _scope.is_dead();
    // Closing top-most scope (exiting compilation unit)?
    if( _par._par == null ) {   // Then reset global statics to allow another compilation unit
      top_scope_close();
    }
  }

  private void top_scope_close() {
    FunNode  .reset_to_init0(); // Done with adding primitives
    GVN      .reset_to_init0(); // Done with adding primitives
    BitsAlias.reset_to_init0(); // Done with adding primitives
    BitsFun  .reset_to_init0(); // Done with adding primitives
    BitsRPC  .reset_to_init0(); // Done with adding primitives
    // StartNode is used by global constants, which in turn are only used by
    // dead cycles.
    while( START._uses._len > NINIT_CONS ) {
      Node x = START._uses.pop();
      assert !GVN.touched(x); // Uses are all dead (but not reclaimed because in a cycle)
    }
  }

  // Return Scope for a name, so can be used to determine e.g. mutability
  ScopeNode lookup_scope( String name, boolean lookup_current_scope_only ) {
    if( name == null ) return null; // Handle null here, easier on parser
    if( _scope.stk().exists(name) ) return _scope;
    return _par == null || lookup_current_scope_only ? null : _par.lookup_scope(name,false);
  }

  // Name lookup is the same for all variables, including function defs (which
  // are literally assigning a lambda to a ref).  Only returns nodes registered
  // with GVN.
  public Node lookup( String name ) {
    ScopeNode scope = lookup_scope(name,false);
    return scope==null ? null : scope.get(name);
  }
  // Return nearest enclosing closure, for forward-ref placement.
  // Struct-scopes do not count.
  ScopeNode lookup_closure( ) { return _scope.is_closure() ? _scope : _par.lookup_closure(); }
  // Test support, return top-level name type
  static Type lookup_valtype( String name ) { return GVN.type(TOP.lookup(name)); }

  // Lookup the name.  If the result is an UnresolvedNode of functions, filter out all
  // the wrong-arg-count functions.  Only returns nodes registered with GVN.
  Node lookup_filter( String name, GVNGCM gvn, int nargs ) {
    Node n = lookup(name);
    return n == null ? null : (n instanceof UnresolvedNode ? ((UnresolvedNode)n).filter(gvn,nargs) : n);
  }

  // Update function name token to Node mapping in the current scope
  Node add_fun( Parse bad, String name, Node val ) { return _scope.stk().add_fun(bad,name,(FunPtrNode)val,GVN); }


  // Type lookup in any scope
  Type lookup_type( String name ) {
    Type t = _scope.get_type(name);
    if( t != null ) return t;
    return _par == null ? null : _par.lookup_type(name);
  }
  // Update type name token to type mapping in the current scope
  void add_type( String name, Type t ) { _scope.add_type(name,t); }
  void def_type( String name, Type t ) { _scope.def_type(name,t); }

}
