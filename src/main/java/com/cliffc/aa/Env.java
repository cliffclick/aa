package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.tvar.TVar;
import java.util.HashSet;

public class Env implements AutoCloseable {
  public final static GVNGCM GVN = new GVNGCM(); // Initial GVN
  public static    StartNode START; // Program start values (control, empty memory, cmd-line args)
  public static    CProjNode CTL_0; // Program start value control
  public static StartMemNode MEM_0; // Program start value memory
  public static   NewObjNode STK_0; // Program start stack frame (has primitives)
  public static    ScopeNode SCP_0; // Program start scope
  public static   DefMemNode DEFMEM;// Default memory (all structure types)
  public static      ConNode ALL_CTRL; // Default control
  public static      ConNode XCTRL; // Always dead control
  public static      ConNode XNIL;  // Common XNIL
  public static      ConNode ANY;   // Common ANY / used for dead
  public static      ConNode ALL;   // Common ALL / used for errors
  // Set of all display aliases, used to track escaped displays at call sites for asserts.
  public static BitsAlias ALL_DISPLAYS = BitsAlias.EMPTY;
  // Set of lexically active display aliases, used for a conservative display
  // approx for forward references.
  public static BitsAlias LEX_DISPLAYS = BitsAlias.EMPTY;


  final Env _par;                // Parent environment
  public final ScopeNode _scope; // Lexical anchor; "end of display"; goes when this environment leaves scope
  Parse _P;                      // Used to get debug info

  // Top-level Env.  Contains, e.g. the primitives.
  // Above any file-scope level Env.
  private Env(  ) {
    _par = null;
    _P = null;
    _scope = init(CTL_0,XNIL,MEM_0,Type.XNIL,null,true);
  }

  // A file-level Env, or below.  Contains user written code.
  Env( Env par, Parse P, boolean is_closure, Node ctrl, Node mem ) {
    GVN._opt_mode=GVNGCM.Mode.Parse;
    _P = P;
    _par = par;
    ScopeNode s = par._scope;   // Parent scope
    _scope = init(ctrl,s.ptr(),mem,s.stk()._tptr,P==null ? null : P.errMsg(),is_closure);
  }
  // Make the Scope object for an Env.
  private static ScopeNode init(Node ctl, Node clo, Node mem, Type back_ptr, Parse errmsg, boolean is_closure) {
    TypeStruct tdisp = TypeStruct.open(back_ptr);
    NewObjNode nnn = (NewObjNode)GVN.xform(new NewObjNode(is_closure,tdisp,clo));
    MrgProjNode  frm = DEFMEM.make_mem_proj(nnn,mem);
    Node ptr = GVN.xform(new ProjNode(nnn,AA.REZ_IDX));
    ALL_DISPLAYS = ALL_DISPLAYS.set(nnn._alias);   // Displays for all time
    LEX_DISPLAYS = LEX_DISPLAYS.set(nnn._alias);   // Lexically active displays
    ScopeNode scope = new ScopeNode(errmsg,is_closure);
    scope.set_ctrl(ctl);
    scope.set_ptr (ptr);  // Address for 'nnn', the local stack frame
    scope.set_mem (frm);  // Memory includes local stack frame
    scope.set_rez (Node.con(Type.SCALAR));
    return scope;
  }

  // Makes a new top Env with primitives
  public static Env top_scope() {
    boolean first_time = START == null;
    if( first_time ) record_for_top_reset1();
    else top_reset();

    // Top-level default values; ALL_CTRL is used by declared functions to
    // indicate that future not-yet-parsed code may call the function.
    START   = GVN.init (new StartNode());
    ALL_CTRL= GVN.xform(new ConNode<>(Type.CTRL )).keep();
    XCTRL   = GVN.xform(new ConNode<>(Type.XCTRL)).keep();
    XNIL    = GVN.xform(new ConNode<>(Type.XNIL )).keep();
    ANY     = GVN.xform(new ConNode<>(Type.ANY  )).keep();
    ALL     = GVN.xform(new ConNode<>(Type.ALL  )).keep();
    // Initial control & memory
    CTL_0  = GVN.init(new    CProjNode(START,0));
    DEFMEM = GVN.init(new   DefMemNode(  CTL_0));
    MEM_0  = GVN.init(new StartMemNode(START  ));
    // Top-most (file-scope) lexical environment
    Env top = new Env();
    // Top-level display defining all primitives
    SCP_0 = top._scope;
    SCP_0.init();               // Add base types
    STK_0 = SCP_0.stk();

    STK_0.keep();               // Inputs & type will rapidly change
    for( PrimNode prim : PrimNode.PRIMS() )
      STK_0.add_fun(null,prim._name,(FunPtrNode) GVN.xform(prim.as_fun(GVN)));
    for( NewNode.NewPrimNode lib : NewNode.NewPrimNode.INTRINSICS() )
      STK_0.add_fun(null,lib ._name,(FunPtrNode) GVN.xform(lib .as_fun(GVN)));
    // Top-level constants
    STK_0.create_active("math_pi", Node.con(TypeFlt.PI),TypeStruct.FFNL);
    STK_0.no_more_fields();
    STK_0.unkeep();
    // Run the worklist dry
    GVN.iter(GVNGCM.Mode.Parse);

    if( first_time ) record_for_top_reset2();
    return top;
  }

  // A new Env for the current Parse scope (generally a file-scope or a
  // test-scope), above this is the basic public Env with all the primitives
  public static Env file_scope(Env top_scope) {
    return new Env(top_scope,null, true, top_scope._scope.ctrl(), top_scope._scope.mem());
  }

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
    stk.no_more_fields();
    gvn.add_flow(stk);          // Scope object going dead, trigger following projs to cleanup
    _scope.set_ptr(null);       // Clear pointer to display
    gvn.add_flow(ptr);          // Clearing pointer changes liveness
    gvn.add_work_all(_scope.unkeep());
    LEX_DISPLAYS = LEX_DISPLAYS.clear(stk._alias);
  }

  // Close the current Env and lexical scope.
  @Override public void close() {
    if( _P != null ) { _scope._debug_close = _P.errMsg(); _P = null; }
    ScopeNode pscope = _par._scope;
    // Promote forward refs to the next outer scope
    if( pscope != null && _par._par != null )
      _scope.stk().promote_forward(pscope.stk());
    close_display(GVN);
    GVN.add_dead(_scope);
    GVN.iter(GVN._opt_mode);
    assert _scope.is_dead();
  }

  // Record global static state for reset
  private static void record_for_top_reset1() {
    BitsAlias.init0();
    BitsFun  .init0();
    BitsRPC  .init0();
  }
  private static void record_for_top_reset2() { GVN.init0(); Node.init0(); }

  // Reset all global statics for the next parse.  Useful during testing when
  // many top-level parses happen in a row.
  private static void top_reset() {
    BitsAlias .reset_to_init0();
    BitsFun   .reset_to_init0();
    BitsRPC   .reset_to_init0();
    GVN       .reset_to_init0();
    Node      .reset_to_init0();
    FunNode   .reset();
    NewNode.NewPrimNode.reset();
    PrimNode  .reset();
    ALL_DISPLAYS = BitsAlias.EMPTY; // Reset aliases declared as Displays
    LEX_DISPLAYS = BitsAlias.EMPTY;
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
  Type lookup_valtype( String name ) {
    Node n = lookup(name);
    if( !(n instanceof UnresolvedNode) ) return n.val();
    // For unresolved, use the ambiguous type
    return n.value(GVNGCM.Mode.Opto);
  }

  // Lookup the operator name.  Use the longest name that's found, so that long
  // strings of operator characters are naturally broken by (greedy) strings.
  // If nargs is positive, filter by nargs
  Node lookup_filter( String name, GVNGCM gvn, int nargs ) {
    if( !Parse.isOp(name) ) return null; // Limit to operators
    for( int i=name.length(); i>0; i-- ) {
      Node n = lookup(name.substring(0,i).intern());
      if( n != null ) {
        if( nargs == 0 ) return n;
        return n instanceof UnresolvedNode
          ? ((UnresolvedNode)n).filter(gvn,nargs)
          : ((    FunPtrNode)n).filter(nargs);
      }
    }
    return null;
  }

  // Update function name token to Node mapping in the current scope
  Node add_fun( Parse bad, String name, Node val ) { return _scope.stk().add_fun(bad,name,(FunPtrNode)val); }


  // Type lookup in any scope
  Type lookup_type( String name ) {
    Type t = _scope.get_type(name);
    if( t != null ) return t;
    return _par == null ? null : _par.lookup_type(name);
  }
  // Update type name token to type mapping in the current scope
  void add_type( String name, Type t ) { _scope.add_type(name,t); }
  void def_type( String name, Type t ) { _scope.def_type(name,t); }

  // Collect TVars from all variables in-scope.  Used to build a
  // "non-generative" set of TVars for Hindley-Milner typing.
  public HashSet<TVar> collect_active_scope() {
    HashSet<TVar> tvars = new HashSet<>();
    Env e = this;
    while( e!=null ) {
      for( Node def : _scope.stk()._defs )
        if( def != null ) tvars.add(def.tvar());
      e = e._par;
    }
    return tvars;
  }

}
