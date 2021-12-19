package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.VBitSet;

import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;

import static com.cliffc.aa.AA.DSP_IDX;
import static com.cliffc.aa.AA.unimpl;

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

  public static final KeepNode KEEP_ALIVE = new KeepNode();
  public static      ConNode ANY;   // Common ANY / used for dead
  public static      ConNode ALL;   // Common ALL / used for errors
  public static      ConNode XCTRL; // Always dead control
  public static      ConNode XNIL;  // Default 0
  public static      ConNode XUSE;  // Unused objects (dead displays)
  public static      ConNode XMEM;  // Unused whole memory
  public static      ConNode ALL_CTRL;  // Always alive control
  public static      ConNode ALL_MEM;   // Conservative all memory
  public static      ConNode ALL_PARM; // Default parameter
  public static      ConNode ALL_CALL; // Common during function call construction

  public static    StartNode START; // Program start values (control, empty memory, cmd-line args)
  public static    CProjNode CTL_0; // Program start value control
  public static StartMemNode MEM_0; // Program start value memory
  public static   NewObjNode STK_0; // Program start stack frame (has primitives)
  public static    ScopeNode SCP_0; // Program start scope

  // Set of all display aliases, used to track escaped displays at call sites for asserts.
  public static BitsAlias ALL_DISPLAYS = BitsAlias.EMPTY;

  // Add a permanent edge use to all these Nodes, keeping them alive forever.
  @SuppressWarnings("unchecked")
  private static <N extends Node> N keep(N n) {
    N xn = GVN.init(n);
    KEEP_ALIVE.add_def(xn);
    return xn;
  }

  static {
    // Top-level or common default values
    START   = keep(new StartNode());
    ANY     = keep(new ConNode<>(Type.ANY   ));
    ALL     = keep(new ConNode<>(Type.ALL   ));
    XCTRL   = keep(new ConNode<>(Type.XCTRL ));
    XNIL    = keep(new ConNode<>(Type.XNIL  ));
    XUSE    = keep(new ConNode<>(TypeObj.UNUSED));
    XMEM    = keep(new ConNode<>(TypeMem.ANYMEM));
    ALL_CTRL= keep(new ConNode<>(Type.CTRL  ));
    ALL_MEM = keep(new ConNode<>(TypeMem.ALLMEM));
    ALL_PARM= keep(new ConNode<>(Type.SCALAR));
    ALL_CALL= keep(new ConNode<>(TypeRPC.ALL_CALL));
    // Initial control & memory
    CTL_0  = keep(new    CProjNode(START,0));
    MEM_0  = keep(new StartMemNode(START  ));

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
      Env.GVN.iter();
      TOP._scope.walk_record_for_reset();  Env.GVN.flow_clear();
      TypeEnv te = TOP.gather_errors(err);
      assert te._errs==null && te._t==Type.SCALAR; // Primitives parsed fine
    } catch( Exception e ) { throw new RuntimeException(e); }; // Unrecoverable
    record_for_reset();
  }


  final public Env _par;         // Parent environment
  public final ScopeNode _scope; // Lexical anchor; "end of display"; goes when this environment leaves scope
  public final FunNode _fun;     // Matching FunNode for this lexical environment
  private final HashMap<String,Oper> _opers; // Lexically scoped operators

  // Shared Env constructor.
  private Env( Env par, FunNode fun, boolean is_closure, Node ctrl, Node mem, Node dsp_ptr ) {
    _par = par;
    _fun = fun;
    _opers = new HashMap<>();
    TypeStruct ts = TypeStruct.make("",false,true,TypeFld.make("^",dsp_ptr._val, DSP_IDX));
    NewObjNode nnn = GVN.init(new NewObjNode(is_closure,ts,dsp_ptr));
    Node frm = GVN.init(new MrgProjNode(nnn,mem));
    Node ptr = GVN.init(new ProjNode(nnn,AA.REZ_IDX));
    _scope = GVN.init(new ScopeNode(is_closure));
    _scope.set_ctrl(ctrl);
    _scope.set_ptr (ptr);  // Address for 'nnn', the local stack frame
    _scope.set_mem (frm);  // Memory includes local stack frame
    _scope.set_rez (ALL_PARM);
    KEEP_ALIVE.add_def(_scope);
    ALL_DISPLAYS = ALL_DISPLAYS.set(nnn._alias);   // Displays for all time
    GVN.do_iter();
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
      //int fidx2 = -1;
      //for( int fidx : ((TypeFunPtr)rez._val)._fidxs )
      //  { fidx2 = fidx; break; }
      //formals = FunNode.FUNS.at(fidx2).formals();
      throw unimpl();
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
    if( pscope != null ) {
      stk.promote_forward(pscope.stk());
      if( !_opers.isEmpty() )
        throw unimpl();         // Promote operators
    }

    Node ptr = _scope.ptr();
    stk.no_more_fields();
    GVN.add_flow(stk);          // Scope object going dead, trigger following projs to cleanup
    _scope.set_ptr(null);       // Clear pointer to display
    GVN.add_flow(ptr);          // Clearing pointer changes liveness
    Node xscope = KEEP_ALIVE.pop();
    assert _scope==xscope;
    GVN.add_work_new(_scope);
    GVN.add_dead(_scope);
    GVN.iter();
  }

  // Wire up an early function exit
  Node early_exit( Parse P, Node val ) {
    return _scope.is_closure() ? P.do_exit(_scope,val) : _par.early_exit(P,val); // Hunt for an early-exit-enabled scope
  }

  // Remove all the hooks keeping things alive until Combo sorts it out right.
  static void pre_combo() {
    // Remove any Env.TOP hooks to function pointers, only kept alive until we
    // can compute a real Call Graph.
    for( int i=ScopeNode.RET_IDX; i<SCP_0.len(); i++ )
      if( SCP_0.in(i) instanceof RetNode && !SCP_0.in(i).is_prim() )
        SCP_0.remove(i--);
    Env.GVN.flow_clear();       // Will be used as a worklist
//// Replace the default memory into unknown caller functions, with the
//// matching display.
//for( Node use : DEFMEM._uses ) {
//  FunNode fun;
//  if( use instanceof ParmNode && !use.is_prim() && use.in(1)==DEFMEM && (fun=((ParmNode)use).fun()).has_unknown_callers() ) {
//    ParmNode mem = (ParmNode)use, dsp = fun.parm(DSP_IDX);
//    if( dsp !=null ) {
//      Node display = dsp.in(1).in(0);
//      if( display instanceof NewObjNode ) {
//        MrgProjNode defmem = ((NewObjNode)display).mem();
//        mem.set_def(1,defmem);
//      }
//    }
//  }
//}
//
//// Kill all extra objects hooked by DEFMEM.
//while( DEFMEM.len() > DEFMEM_RESET.length ) DEFMEM.pop();
//for( int i=0; i<DEFMEM_RESET.length; i++ )
//  DEFMEM.set_def(i,DEFMEM_RESET[i]);
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
      GVN.add_dead(c);
    }
    // Clear out the dead before clearing VALS, since they may not be reachable and will blow the elock assert
    GVN.iter_dead();
    TV2.reset_to_init0();
    Node.VALS.clear();          // Clean out hashtable
    START.walk_reset();         // Clean out any wired prim calls
    KEEP_ALIVE.walk_reset();    // Clean out any wired prim calls
    GVNGCM.KEEP_ALIVE.walk_reset();
    GVN.iter();                 // Clean out any dead; reset prim types
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
    ALL_DISPLAYS = BitsAlias.make0(STK_0._alias);
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
    return n.value();
  }

  // Lookup the operator name.  Use the longest name that's found, so that long
  // strings of operator characters are naturally broken by (greedy) strings.
  private Oper _lookup_oper(String tok) {
    Oper o = _opers.get(tok);
    return o==null ? (_par==null ? null : _par._lookup_oper(tok)) : o;
  }

  private UnresolvedNode _lookup_filter( int op_prec_test, String name, int nargs ) {
    for( int i=name.length(); i>0; i-- ) { // First name found will return
      // Prepare the name from the token
      String name2 = name.substring(0,i)+"_";
      Oper o = _lookup_oper(name2.intern());
      //if( o != null && o.op_prec() >= op_prec_test ) {
      // TODO: Return a field load, so not a Unresolved?
      // TODO: Return a string field name, and caller does the Load + Instance-Call
      //  UnOrFunPtrNode m = n.filter(nargs); // Filter for args
      //  if( m!=null )
      //    return (UnOrFunPtrNode)Env.GVN.xform(new FreshNode(_fun,m));
      // }
      throw unimpl();
    }
    return null;
  }



  // Prefix uniop lookup.  The '_' follows the uniop name.
  // Note that "!_var" parses as "! _var" and not as "!_ var".
  // Also "[_]" is a balanced uni-op, and parses with the balanced ops.
  UnresolvedNode lookup_filter_uni( String name ) {
    //if( !Parse.isOp(name) ) return null; // Limit to operators
    //return _lookup_filter(0,name,1);     // Lookup unbalanced uni-op
    throw unimpl();
  }

  // Infix binop lookup
  // _+_       - Normal binop, looks up "_+_"
  UnresolvedNode lookup_filter_bin( String name ) {
    //if( !Parse.isOp(name) ) return null; // Limit to operators
    //return _lookup_filter(1,"_"+name,2);
    throw unimpl();
  }
  // Infix balanced operators, including 3 argument
  // _[_]      - array-lookup     balanced op, looks up " _[_"
  // _[_]=_    - array-assignment balanced op, looks up " _[_"
  UnresolvedNode lookup_filter_bal( String name ) {
    //if( !Parse.isOp(name) ) return null; // Limit to operators
    //return _lookup_filter(0," _"+name,2);
    throw unimpl();
    
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
  void reset_type( String name, Type t ) { _scope.reset_type(name,t); }
}
