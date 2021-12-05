package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.VBitSet;

import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;

import static com.cliffc.aa.AA.DSP_IDX;

// An "environment", a lexical Scope tracking mechanism that runs 1-for-1 in
// parallel with a ScopeNode.
//
// TOP: The top-most environment, which includes the primitives (e.g. "+") and top-level types (e.g. "int64")
// TOP._scope: Node placeholder pointing to all the primitives and types, keeping them alive.
// The TOP env is closed when the 'aa' process no longer accepts more code.

// FILE: The next env down; the results of a single complete normal parse and typing.
// FILE._scope: Result of said parse.

// The FILE level env is used to hold the results of a single file parse, or a
// single test (but not a collection of tests in the same test function), or a
// single REPL session (but not a single REPL line).

// Testing generally starts with TOP, then parses whole complete (short)
// programs at a FILE env and checks their typing - within the same TOP scope.
// A single testParseXX() function will have many tests but only one TOP.

// The REPL starts with a TOP, then opens a FILE level env - then opens a
// single-line Env, parses and types it, then exports it to the FILE env.

public class Env implements AutoCloseable {
  public static Env TOP,FILE;
  public final static GVNGCM GVN = new GVNGCM(); // Initial GVN

  public static      ConNode ANY;   // Common ANY / used for dead
  public static      ConNode ALL;   // Common ALL / used for errors
  public static      ConNode XCTRL; // Always dead control
  public static      ConNode XNIL;  // Default 0
  public static      ConNode XUSE;  // Unused objects (dead displays)
  public static      ConNode ALL_PARM; // Default parameter
  public static      ConNode ALL_CALL; // Common during function call construction

  public static    StartNode START; // Program start values (control, empty memory, cmd-line args)
  public static    CProjNode CTL_0; // Program start value control
  public static StartMemNode MEM_0; // Program start value memory
  public static   NewObjNode STK_0; // Program start stack frame (has primitives)
  public static    ScopeNode SCP_0; // Program start scope

  public static   DefMemNode DEFMEM;// Default memory (all structure types)
  public static final Node[] DEFMEM_RESET;

  // Set of all display aliases, used to track escaped displays at call sites for asserts.
  public static BitsAlias ALL_DISPLAYS = BitsAlias.EMPTY;
  // Set of lexically active display aliases, used for a conservative display
  // approx for forward references.
  public static BitsAlias LEX_DISPLAYS = BitsAlias.EMPTY;


  static {
    // Top-level or common default values
    START   = GVN.init (new StartNode());
    ANY     = GVN.xform(new ConNode<>(Type.ANY   )).keep();
    ALL     = GVN.xform(new ConNode<>(Type.ALL   )).keep();
    XCTRL   = GVN.xform(new ConNode<>(Type.XCTRL )).keep();
    XNIL    = GVN.xform(new ConNode<>(Type.XNIL  )).keep();
    XUSE    = GVN.xform(new ConNode<>(TypeObj.UNUSED)).keep();
    ALL_PARM= GVN.xform(new ConNode<>(Type.SCALAR)).keep();
    ALL_CALL= GVN.xform(new ConNode<>(TypeRPC.ALL_CALL)).keep();
    // Initial control & memory
    CTL_0  = GVN.init(new    CProjNode(START,0));
    MEM_0  = GVN.init(new StartMemNode(START  ));
    DEFMEM = GVN.init(new   DefMemNode(CTL_0));

    // The Top-Level environment; holds the primitives.
    TOP = new Env();
    SCP_0 = TOP._scope;
    STK_0 = SCP_0.stk();
    PrimNode.PRIMS();           // Initialize

    // Parse PRIM_SOURCE for the primitives
    try {
      // Loading from a file is a Bad Idea in the long run
      byte[] encoded = Files.readAllBytes(Paths.get("./src/main/java/com/cliffc/aa/_prims.aa"));
      String prog = new String(encoded);
      ErrMsg err = new Parse("PRIMS",true,TOP,prog).prog();
      TOP._scope.set_rez(Node.con(Type.SCALAR));
      while( DEFMEM._defs.last()==null ) DEFMEM.pop(); // Remove temp unused aliases
      Env.GVN.iter(GVNGCM.Mode.PesiNoCG);
      TypeEnv te = TOP.gather_errors(err);
      assert te._errs==null && te._t==Type.SCALAR; // Primitives parsed fine
    } catch( Exception e ) { throw new RuntimeException(e); }; // Unrecoverable
    DEFMEM_RESET = DEFMEM._defs.asAry();
    record_for_reset();
  }


  final public Env _par;         // Parent environment
  public final ScopeNode _scope; // Lexical anchor; "end of display"; goes when this environment leaves scope
  public final FunNode _fun;     // Matching FunNode for this lexical environment

  // Shared Env constructor.
  private Env( Env par, FunNode fun, boolean is_closure, Node ctrl, Node mem, Node dsp_ptr ) {
    _par = par;
    _fun = fun;
    mem.keep(2);
    TypeStruct ts = TypeStruct.make("",false,true,TypeFld.make("^",dsp_ptr._val, DSP_IDX));
    NewObjNode nnn = GVN.xform(new NewObjNode(is_closure,ts,dsp_ptr)).keep(2);
    MrgProjNode frm = DEFMEM.make_mem_proj(nnn,mem.unkeep(2));
    Node ptr = GVN.xform(new ProjNode(nnn.unkeep(2),AA.REZ_IDX));
    _scope = new ScopeNode(is_closure);
    _scope.set_ctrl(ctrl);
    _scope.set_ptr (ptr);  // Address for 'nnn', the local stack frame
    _scope.set_mem (frm);  // Memory includes local stack frame
    _scope.set_rez (Node.con(Type.SCALAR));
    ALL_DISPLAYS = ALL_DISPLAYS.set(nnn._alias);   // Displays for all time
    LEX_DISPLAYS = LEX_DISPLAYS.set(nnn._alias);   // Lexically active displays
  }

  // Top-level Env.  Contains, e.g. the primitives.
  // Above any file-scope level Env.
  private Env( ) { this(null,null,true,CTL_0,MEM_0,XNIL); }


  // A file-level Env, or below.  Contains user written code as opposed to primitives.
  Env( Env par, FunNode fun, boolean is_closure, Node ctrl, Node mem ) {
    this(par,fun,is_closure,ctrl,mem, par._scope.ptr());
  }

  // Gather and report errors and typing
  TypeEnv gather_errors(ErrMsg err) {
    // Hunt for typing errors in the alive code
    HashSet<ErrMsg> errs = new HashSet<>();
    if( err!= null ) errs.add(err);
    VBitSet bs = new VBitSet();
    _scope.walkerr_def(errs,bs);
    ArrayList<ErrMsg> errs0 = new ArrayList<>(errs);
    Collections.sort(errs0);

    Node rez = _scope.rez();
    Type mem = _scope.mem()._val;
    TypeStruct formals = null;
    if( rez._val instanceof TypeFunPtr ) {
      int fidx2 = -1;
      for( int fidx : ((TypeFunPtr)rez._val)._fidxs )
        { fidx2 = fidx; break; }
      formals = FunNode.FUNS.at(fidx2).formals();
    }
    return new TypeEnv(_scope,
                       rez._val,
                       formals,
                       mem instanceof TypeMem ? (TypeMem)mem : mem.oob(TypeMem.ALLMEM),
                       rez.has_tvar() ? rez.tvar() : null,
                       errs0.isEmpty() ? null : errs0);
  }



  // Promote any forward refs in this display to an outer scope.
  // Close the currently open display, and remove its alias from the set of
  // active display aliases (which are otherwise available to all function
  // definitions getting parsed).
  @Override public void close() {
    // Promote forward refs to the next outer scope
    NewObjNode stk = _scope.stk();
    ScopeNode pscope = _par._scope;
    if( pscope != null && _par._par != null )
      stk.promote_forward(pscope.stk());

    Node ptr = _scope.ptr();
    //if( ptr == null ) return;   // Already done
    LEX_DISPLAYS = LEX_DISPLAYS.clear(stk._alias);
    stk.no_more_fields();
    GVN.add_flow(stk);          // Scope object going dead, trigger following projs to cleanup
    _scope.set_ptr(null);       // Clear pointer to display
    GVN.add_flow(ptr);          // Clearing pointer changes liveness
    GVN.add_work_all(_scope.unkeep());
    GVN.add_dead(_scope);
    GVN.iter(GVN._opt_mode);
  }

  // Wire up an early function exit
  Node early_exit( Parse P, Node val ) {
    return _scope.is_closure() ? P.do_exit(_scope,val) : _par.early_exit(P,val); // Hunt for an early-exit-enabled scope
  }

  // Remove all the hooks keeping things alive until Combo sorts it out right.
  static void pre_combo() {
    // Remove any Env.TOP hooks to function pointers, only kept alive until we
    // can compute a real Call Graph.
    Node n;
    while( (n=SCP_0._defs.last())!=null && !n.is_prim() )
      SCP_0.pop();
    // Replace the default memory into unknown caller functions, with the
    // matching display.
    for( Node use : DEFMEM._uses ) {
      FunNode fun;
      if( use instanceof ParmNode && !use.is_prim() && use.in(1)==DEFMEM && (fun=((ParmNode)use).fun()).has_unknown_callers() ) {
        ParmNode mem = (ParmNode)use, dsp = fun.parm(DSP_IDX);
        if( dsp !=null ) {
          Node display = dsp.in(1).in(0);
          if( display instanceof NewObjNode ) {
            MrgProjNode defmem = ((NewObjNode)display).mem();
            mem.set_def(1,defmem);
          }
        }
      }
    }

    // Kill all extra objects hooked by DEFMEM.
    while( DEFMEM.len() > DEFMEM_RESET.length ) DEFMEM.pop();
    for( int i=0; i<DEFMEM_RESET.length; i++ )
      DEFMEM.set_def(i,DEFMEM_RESET[i]);
  }

  // Record global static state for reset
  private static void record_for_reset() {
    Node.init0(); // Record end of primitives
    GVN.init0();
    FunNode.init0();
    BitsAlias.init0();
    BitsFun  .init0();
    BitsRPC  .init0();
  }

  // Reset all global statics for the next parse.  Useful during testing when
  // many top-level parses happen in a row.
  public static void top_reset() {
    // Kill all extra constants and cyclic ConTypeNodes hooked by Start
    Node c;
    while( !(c=START._uses.last()).is_prim() ) {
      while( c.len()>0 ) c.pop();
      Env.GVN.add_dead(c);
    }
    // Clear out the dead before clearing VALS, since they may not be reachable and will blow the elock assert
    Env.GVN.iter_dead();
    TV2.reset_to_init0();
    Node.VALS.clear();                         // Clean out hashtable
    Node.RESET_VISIT.clear();
    Env.START.walk_reset(Env.GVN._work_flow);  // Clean out any wired prim calls
    Env.GVN.iter(GVNGCM.Mode.Parse);   // Clean out any dead; reset prim types
    for( Node n : Node.VALS.keySet() ) // Assert no leftover bits from the prior compilation
      assert n._uid < Node._INIT0_CNT; //
    Node      .reset_to_init0();
    GVN       .reset_to_init0();
    FunNode   .reset_to_init0();
    BitsAlias .reset_to_init0();
    BitsFun   .reset_to_init0();
    BitsRPC   .reset_to_init0();
    Combo.reset();
    // Reset aliases declared as Displays
    ALL_DISPLAYS = LEX_DISPLAYS = BitsAlias.make0(STK_0._alias);
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
    if( !(n instanceof UnresolvedNode) ) return n._val;
    // For unresolved, use the ambiguous type
    return n.value(GVNGCM.Mode.Opto);
  }

  // Lookup the operator name.  Use the longest name that's found, so that long
  // strings of operator characters are naturally broken by (greedy) strings.

  // Prefix uniop lookup.  The '_' follows the uniop name.
  // Note that "!_var" parses as "! _var" and not as "!_ var".
  // Also "[_]" is a balanced uni-op.
  UnOrFunPtrNode lookup_filter_uni( String name ) {
    if( !Parse.isOp(name) ) return null; // Limit to operators
    UnOrFunPtrNode n = _lookup_filter(1,    name,1);     // Lookup unbalanced uni-op
    return  n==null ?  _lookup_filter(0," "+name,1) : n; // Try again for a balanced uni-op
  }

  // Infix binop lookup
  // _+_       - Normal binop, looks up "_+_"
  UnOrFunPtrNode lookup_filter_bin( String name ) {
    if( !Parse.isOp(name) ) return null; // Limit to operators
    return _lookup_filter(1,"_"+name,2);
  }
  // Infix balanced operators, including 3 argument
  // _[_]      - array-lookup     balanced op, looks up " _[_"
  // _[_]=_    - array-assignment balanced op, looks up " _[_"
  UnOrFunPtrNode lookup_filter_bal( String name ) {
    if( !Parse.isOp(name) ) return null; // Limit to operators
    return _lookup_filter(0," _"+name,2);
  }

  private UnOrFunPtrNode _lookup_filter( int op_prec_test, String name, int nargs ) {
    for( int i=name.length(); i>0; i-- ) { // First name found will return
      // Prepare the name from the token
      String name2 = name.substring(0,i)+"_";
      UnOrFunPtrNode n = (UnOrFunPtrNode)lookup(name2.intern());
      if( n != null && n.op_prec() >= op_prec_test ) {
        UnOrFunPtrNode m = n.filter(nargs); // Filter for args
        if( m!=null )
          return (UnOrFunPtrNode)Env.GVN.xform(new FreshNode(_fun,m));
      }
    }
    return null;
  }


  // Type lookup in any scope
  ConTypeNode lookup_type( String name ) {
    ConTypeNode t = _scope.get_type(name);
    if( t != null ) return t;
    return _par == null ? null : _par.lookup_type(name);
  }
  // Lookup by alias
  public ConTypeNode lookup_type( int alias ) {
    ConTypeNode t = _scope.get_type(alias);
    if( t != null ) return t;
    return _par == null ? null : _par.lookup_type(alias);
  }
  // Update type name token to type mapping in the current scope
  void add_type( String name, ConTypeNode t ) { _scope.add_type(name,t); }
}
