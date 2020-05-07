package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;

import java.util.BitSet;

public class Env implements AutoCloseable {
  final Env _par;
  Parse _P;          // Used to get debug info
  public final ScopeNode _scope;  // Lexical anchor; "end of display"; goes when this environment leaves scope
  Env( Env par, Parse P, boolean is_closure ) {
    _P = P;
    _par = par;
    Node ctl = par == null ? CTL_0 : par._scope.ctrl();
    Node clo = par == null ? GVN.con(Type.XNIL) : par._scope.ptr();
    Node mem = par == null ? MEM_0 : par._scope.mem ();
    TypeStruct tdisp = TypeStruct.make_tuple(TypeStruct.ts(par == null ? Type.XNIL : par._scope.stk().tptr()));
    NewObjNode nnn = (NewObjNode)GVN.xform(new NewObjNode(is_closure,tdisp,ctl,clo).keep());
    Node frm = DEFMEM.make_mem_proj(GVN,nnn);
    Node ptr = GVN.xform(new ProjNode(nnn,1));
    DISPLAY .set(nnn._alias);   // Current display stack
    DISPLAYS.set(nnn._alias);   // Displays for all time
    MemMergeNode mmem = new MemMergeNode(mem,frm,nnn.<NewObjNode>unhook()._alias);
    ScopeNode scope = _scope = new ScopeNode(P==null ? null : P.errMsg(),is_closure);
    scope.set_ctrl(ctl,GVN);
    scope.set_ptr (ptr,GVN);  // Address for 'nnn', the local stack frame
    scope.set_active_mem(mmem,GVN);  // Memory includes local stack frame
    scope.set_rez (GVN.con(Type.SCALAR),GVN);
  }

  public  final static GVNGCM GVN; // Initial GVN, defaults to ALL, lifts towards ANY
  public  final static  StartNode START; // Program start values (control, empty memory, cmd-line args)
  public  final static  CProjNode CTL_0; // Program start value control
  public  final static StartMemNode MEM_0; // Program start value memory
  public  final static NewObjNode STK_0; // Program start stack frame (has primitives)
  public  final static DefMemNode DEFMEM;// Default memory (all structure types)

  public  final static    ConNode ALL_CTRL; // Default control
          final static int LAST_START_UID;
  private final static int NINIT_CONS;
  public  final static Env TOP; // Top-most lexical Environment, has all primitives, unable to be removed
  public        static BitsAlias DISPLAY; // Currently active display stack
  // Set of display aliases, used for assertions
  public final static BitSet DISPLAYS = new BitSet();


  static {
    GVN = new GVNGCM();      // Initial GVN, defaults to ALL, lifts towards ANY
    DISPLAY = BitsAlias.EMPTY;
    DISPLAYS.clear();

    // Initial control & memory
    START  = (StartNode)GVN.xform(new StartNode(       ));
    CTL_0  = (CProjNode)GVN.xform(new CProjNode(START,0));
    DEFMEM = (DefMemNode)GVN.xform(new DefMemNode(GVN.con(TypeObj.OBJ)));
    MEM_0  = (StartMemNode)GVN.xform(new StartMemNode(START,DEFMEM));
    // Top-most (file-scope) lexical environment
    TOP = new Env(null,null, true);
    // Top-level display defining all primitives
    STK_0  = TOP._scope.stk();
    TOP._scope.add_def(DEFMEM);

    // Top-level default values; ALL_CTRL is used by declared functions to
    // indicate that future not-yet-parsed code may call the function.
    ALL_CTRL = GVN.init(new ConNode<>(Type.CTRL));
    // Used to reset between tests
    LAST_START_UID = ALL_CTRL._uid;
    // Install primitives.  :-)
    TOP.install_primitives();
    // Used to reset between tests
    NINIT_CONS = START._uses._len;
  }
  private void install_primitives() {
    _scope.init0();             // Add base types
    GVN.unreg(STK_0);           // Make STK_0 active, to cheaply add primitives
    for( Node use : STK_0._uses ) GVN.unreg(use); // Also the OProj,DProj will rapidly change types
    for( PrimNode prim : PrimNode.PRIMS )
      STK_0.add_fun(null,prim._name,(FunPtrNode) GVN.xform(prim.as_fun(GVN)), GVN);
    for( IntrinsicNewNode lib : IntrinsicNewNode.INTRINSICS )
      STK_0.add_fun(null,lib ._name,(FunPtrNode) GVN.xform(lib .as_fun(GVN)), GVN);
    // Top-level constants
    STK_0.create_active("math_pi", GVN.con(TypeFlt.PI),TypeStruct.FFNL,GVN);
    // Now that all the UnresolvedNodes have all possible hits for a name,
    // register them with GVN.
    for( Node val : STK_0._defs )  if( val instanceof UnresolvedNode ) GVN.init0(val);
    GVN.rereg(STK_0,STK_0.value(GVN));
    for( Node use : STK_0._uses ) GVN.rereg(use,use.value(GVN));
    GVN.rereg(_scope.mem(),_scope.mem().value(GVN));
    GVN.rereg(_scope,_scope.value(GVN));
    GVN.setype(DEFMEM,DEFMEM.value(GVN));
    // Uplift all types once, since early Parm:mem got early versions of prims,
    // and later prims *added* choices which *lowered* types.
    for( int i=0; i<2; i++ )
      for( Node n : GVN.valsKeySet() )
        GVN.setype(n,n.value(GVN));
    GVN.add_work(MEM_0);
    // Run the worklist dry
    GVN.iter(1);
    BitsAlias.init0(); // Done with adding primitives
    BitsFun  .init0(); // Done with adding primitives
    BitsRPC  .init0(); // Done with adding primitives
    DEFMEM   .init0(); // Done with adding primitives
    FunNode  .init0(); // Done with adding primitives
    GVN      .init0(); // Done with adding primitives
  }

  // A new Env for the current Parse scope (generally a file-scope or a
  // test-scope), above this is the basic public Env with all the primitives
  public static Env top() { return new Env(TOP,null, false); }

  // Wire up an early function exit
  Node early_exit( Parse P, Node val ) {
    return _scope.is_closure() ? P.do_exit(_scope,val) : _par.early_exit(P,val); // Hunt for an early-exit-enabled scope
  }

  // Close any currently open display, and remove its alias from the set of
  // active display aliases (which are otherwise available to all function
  // definitions getting parsed).
  public void close_display( GVNGCM gvn ) {
    Node ptr = _scope.ptr();
    if( ptr == null ) return;   // Already done
    NewObjNode stk = _scope.stk();
    DISPLAY = DISPLAY.clear(stk._alias);
    gvn.add_work_uses(stk);     // Scope object going dead, trigger following projs to cleanup
    _scope.set_ptr(null,gvn);   // Clear pointer to display
  }

  // Close the current Env and lexical scope.
  @Override public void close() {
    if( _P != null ) { _scope._debug_close = _P.errMsg(); _P = null; }
    ScopeNode pscope = _par._scope;
    // Promote forward refs to the next outer scope
    if( pscope != null && pscope != TOP._scope)
      _scope.stk().promote_forward(GVN,pscope.stk());
    close_display(GVN);
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
  // Test support, return top-level name type
  static Type lookup_valtype( String name ) {
    Node n = TOP.lookup(name);
    Type t = GVN.type(n);
    if( !(n instanceof UnresolvedNode) ) return t;
    // For unresolved, use the ambiguous type
    assert GVN._opt_mode==0;
    GVN._opt_mode=2;
    t = n.value(GVN);
    GVN._opt_mode=0;
    return t;
  }

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
