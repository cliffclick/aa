package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;

public class Env implements AutoCloseable {
  final Env _par;
  ScopeNode _scope;  // Lexical anchor; goes when this environment leaves scope
  private boolean _if;            // If-scopes stop update propagation
  Env( Env par, boolean early, boolean ifscope ) {
    _par = par;
    _if = ifscope;
    ScopeNode scope = new ScopeNode(early,ifscope);
    if( par != null ) {
      NewNode nnn = GVN.init(new NewNode());
      Node ptr = GVN.xform(new ProjNode(nnn,1));
      Node mem = par._scope.mem();
      if( !ifscope ) {          // If mini-scopes not a real closure, not exposed to memory
        Node frm = GVN.xform(new OProjNode(nnn,0));
        mem = GVN.xform(new MemMergeNode(mem,frm));
      }

      scope.set_ctrl(par._scope.ctrl(),GVN);
      scope.set_mem (mem,GVN);  // Memory includes local stack frame
      scope.set_ptr (ptr,GVN);  // Address for 'nnn', the local stack frame
    }
    _scope = GVN.init(scope);
  }

  public  final static GVNGCM GVN; // Initial GVN, defaults to ALL, lifts towards ANY
  public  final static StartNode START; // Program start values (control, empty memory, cmd-line args)
          final static CProjNode CTL_0; // Program start value control
          final static      Node MEM_0; // Program start value memory
  private final static      Node PTR_0; // Program start stack frame address
  private final static   NewNode STK_0; // Program start stack frame (has primitives)
  public final static    ConNode ALL_CTRL;
  public final static int LAST_START_UID;
  private final static int NINIT_CONS;
  private final static Env TOP; // Top-most lexical Environment, has all primitives, unable to be removed
  static {
    GVN = new GVNGCM();     // Initial GVN, defaults to ALL, lifts towards ANY
    // Initial control, memory, args, program state
    START = new StartNode();
    assert START._uid==0;
    CTL_0 = GVN.init(new CProjNode(START,0));
    STK_0 = GVN.init(new NewNode());
    PTR_0 = GVN.init(new  ProjNode(STK_0,1));
    Node all_mem = GVN.init(new MProjNode(START,1));
    Node prims   = GVN.init(new OProjNode(STK_0,0));
    MEM_0 = GVN.init(new MemMergeNode(all_mem,prims));
    ALL_CTRL = GVN.init(new ConNode<>(Type.CTRL));
    LAST_START_UID = ALL_CTRL._uid;
    TOP    = new Env(null,false,false); // Top-most lexical Environment
    TOP.install_primitives();
    NINIT_CONS = START._uses._len;
  }
  private void install_primitives() {
    _scope.keep();              // do not delete
    _scope.init0();             // Add base types
    for( PrimNode prim : PrimNode.PRIMS )
      STK_0.add_fun(prim._name,(FunPtrNode) GVN.xform(prim.as_fun(GVN)), GVN);
    for( IntrinsicNewNode lib : IntrinsicNewNode.INTRINSICS )
      STK_0.add_fun(lib ._name,(FunPtrNode) GVN.xform(lib .as_fun(GVN)), GVN);
    // Top-level constants
    STK_0.create("math_pi", GVN.con(TypeFlt.PI),GVN,TypeStruct.ffinal());
    // Now that all the UnresolvedNodes have all possible hits for a name,
    // register them with GVN.
    for( Node val : STK_0._defs )  if( val instanceof UnresolvedNode ) GVN.init0(val);
    _scope.set_ctrl(CTL_0, GVN);
    _scope.set_mem (MEM_0, GVN);
    _scope.set_ptr (PTR_0, GVN);
    // Run the worklist dry
    GVN.iter();
    BitsAlias.init0(); // Done with adding primitives
    BitsFun  .init0(); // Done with adding primitives
    BitsRPC  .init0(); // Done with adding primitives
    FunNode  .init0(); // Done with adding primitives
    GVN      .init0(); // Done with adding primitives
  }

  // A new top-level Env, above this is the basic public Env with all the primitives
  public static Env top() { return new Env(TOP,true,false); }

  // Wire up an early function exit
  Node early_exit( Parse P, Node val ) {
    return _scope.early() ? P.do_exit(_scope,val) : _par.early_exit(P,val); // Hunt for an early-exit-enabled scope
  }

  // Close the current Env and lexical scope.
  @Override public void close() {
    ScopeNode pscope = _par._scope;
    // Promote forward refs to the next outer scope
    if( pscope != null && pscope != TOP._scope)
      _scope.stk().promote_forward(GVN,pscope.stk());
    if( _scope.is_dead() ) return;
    // Closing top-most scope (exiting compilation unit)?
    if( _par._par == null ) {   // Then reset global statics to allow another compilation unit
      top_scope_close();
      return;
    }
    // Whats left is function-ref generic entry points which promote to next
    // outer scope, and control-users which promote to the Scope's control.
    while( _scope._uses._len > 0 ) {
      Node use = _scope._uses.at(0);
      assert use != pscope;
      int idx = use._defs.find(_scope);
      GVN.set_def_reg(use,idx, idx==0 ? pscope.ctrl() : pscope);
    }
    _scope.unkeep(GVN);
    assert _scope.is_dead();
  }

  private void top_scope_close() {
    _scope.unkeep(GVN);
    BitsAlias.reset_to_init0(); // Done with adding primitives
    BitsFun  .reset_to_init0(); // Done with adding primitives
    BitsRPC  .reset_to_init0(); // Done with adding primitives
    FunNode  .reset_to_init0(); // Done with adding primitives
    GVN      .reset_to_init0(); // Done with adding primitives
    // StartNode is used by global constants, which in turn are only used by
    // dead cycles.
    while( START._uses._len > NINIT_CONS ) {
      Node x = START._uses.pop();
      assert !GVN.touched(x); // Uses are all dead (but not reclaimed because in a cycle)
    }
  }

  // Return Scope for a name, so can be used to determine e.g. mutability
  ScopeNode lookup_scope( String name ) {
    if( name == null ) return null; // Handle null here, easier on parser
    if( _scope.stk().exists(name) ) return _scope;
    return _par == null ? null : _par.lookup_scope(name);
  }
  // Lookup, stopping at an If mini-scope
  ScopeNode lookup_if( String name ) {
    if( _if || _scope.stk().exists(name) ) return _scope;
    return _par == null ? null : _par.lookup_if(name);
  }

  // Name lookup is the same for all variables, including function defs (which
  // are literally assigning a lambda to a ref).  Only returns nodes registered
  // with GVN.
  public Node lookup( String name ) {
    ScopeNode scope = lookup_scope(name);
    return scope==null ? null : scope.get(name);
  }
  // Test support, return top-level name type
  static Type lookup_valtype( String name ) { return GVN.type(TOP.lookup(name)); }

  // Lookup the name.  If the result is an UnresolvedNode of functions, filter out all
  // the wrong-arg-count functions.  Only returns nodes registered with GVN.
  Node lookup_filter( String name, GVNGCM gvn, int nargs ) {
    Node n = lookup(name);
    return n == null ? null : (n instanceof UnresolvedNode ? ((UnresolvedNode)n).filter(gvn,nargs) : n);
  }

  // Update function name token to Node mapping in the current scope
  Node add_fun( String name, Node val ) { return _scope.add_fun(name,(FunPtrNode)val,GVN); }


  // Type lookup in any scope
  Type lookup_type( String name ) {
    Type t = _scope.get_type(name);
    if( t != null ) return t;
    return _par == null ? null : _par.lookup_type(name);
  }
  // Update type name token to type mapping in the current scope
  void add_type( String name, Type t ) { _scope.add_type(name,t); }

}
