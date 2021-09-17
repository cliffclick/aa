package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.nio.file.Files;
import java.nio.file.Paths;

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

  public static      ConNode ANY;   // Common ANY / used for dead
  public static      ConNode ALL;   // Common ALL / used for errors
  public static      ConNode XCTRL; // Always dead control
  public static      ConNode XNIL;  // Default 0
  public static      ConNode ALL_CTRL; // Default control
  public static      ConNode ALL_PARM; // Default parameter
  public static      ConNode ALL_CALL; // Common during function call construction

  public static    StartNode START; // Program start values (control, empty memory, cmd-line args)
  public static    CProjNode CTL_0; // Program start value control
  public static StartMemNode MEM_0; // Program start value memory
  public static   NewObjNode STK_0; // Program start stack frame (has primitives)
  public static    ScopeNode SCP_0; // Program start scope

  public static   DefMemNode DEFMEM;// Default memory (all structure types)
  private static int MAX_ALIAS;

  // Set of all display aliases, used to track escaped displays at call sites for asserts.
  public static BitsAlias ALL_DISPLAYS = BitsAlias.EMPTY;
  // Set of lexically active display aliases, used for a conservative display
  // approx for forward references.
  public static BitsAlias LEX_DISPLAYS = BitsAlias.EMPTY;


  static {
    // Top-level default values; ALL_CTRL is used by declared functions to
    // indicate that future not-yet-parsed code may call the function.
    START   = GVN.init (new StartNode());
    ANY     = GVN.xform(new ConNode<>(Type.ANY   )).keep();
    ALL     = GVN.xform(new ConNode<>(Type.ALL   )).keep();
    XCTRL   = GVN.xform(new ConNode<>(Type.XCTRL )).keep();
    XNIL    = GVN.xform(new ConNode<>(Type.XNIL  )).keep();
    ALL_CTRL= GVN.xform(new ConNode<>(Type.CTRL  )).keep();
    ALL_PARM= GVN.xform(new ConNode<>(Type.SCALAR)).keep();
    ALL_CALL= GVN.xform(new ConNode<>(TypeRPC.ALL_CALL)).keep();
    // Initial control & memory
    CTL_0  = GVN.init(new    CProjNode(START,0));
    MEM_0  = GVN.init(new StartMemNode(START  ));
    DEFMEM = GVN.init(new   DefMemNode(CTL_0));

    // The Top-Level environment; holds the primitives.
    TOP = new Env();
    // Parse PRIM_SOURCE for the primitives
    PrimNode.PRIMS();           // Initialize

    try {
      // Loading from a file is a Bad Idea in the long run
      byte[] encoded = Files.readAllBytes(Paths.get("./src/main/java/com/cliffc/aa/_prims.aa"));
      String prog = new String(encoded);
      ErrMsg err = new Parse("PRIMS",true,TOP,prog).prog();
      TOP._scope.set_rez(ALL_PARM);
      Env.GVN.iter(GVNGCM.Mode.PesiNoCG);
      TypeEnv te = TOP.gather_errors(err);
      assert te._errs==null && te._t==Type.SCALAR; // Primitives parsed fine
    } catch( Exception e ) { throw new RuntimeException(e); }; // Unrecoverable
    record_for_reset();
  }


  final public Env _par;         // Parent environment
  public final ScopeNode _scope; // Lexical anchor; "end of display"; goes when this environment leaves scope
  public VStack _nongen;         // Hindley-Milner "non-generative" variable set; current/pending defs

  // Shared Env constructor.
  private Env( Env par, VStack nongen, boolean is_closure, Node ctrl, Node mem, Node dsp_ptr ) {
    _par = par;
    _nongen = nongen;
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
  private Env( ) {
    this(null,null,true,CTL_0,MEM_0,XNIL);
    SCP_0 = _scope;
    STK_0 = SCP_0.stk();
    //SCP_0.init();               // Add base types; TODO: move into init code
  }


  // A file-level Env, or below.  Contains user written code as opposed to primitives.
  Env( Env par, boolean is_closure, Node ctrl, Node mem ) {
    this(par,new VStack(par._nongen),is_closure,ctrl,mem, par._scope.ptr());
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
    TypeFunSig sig = null;
    if( rez._val instanceof TypeFunPtr ) {
      int fidx2 = -1;
      for( int fidx : ((TypeFunPtr)rez._val)._fidxs )
        { fidx2 = fidx; break; }
      sig = FunNode.FUNS.at(fidx2)._sig;
    }
    return new TypeEnv(_scope,
                       rez._val,
                       sig,
                       mem instanceof TypeMem ? (TypeMem)mem : mem.oob(TypeMem.ALLMEM),
                       rez.tvar(),
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

  // Record global static state for reset
  private static void record_for_reset() {
    MAX_ALIAS = DEFMEM.len();
    Node.init0(); // Record end of primitives
    GVN.init0();
    FunNode.init0();
    BitsAlias.init0();
    BitsFun  .init0();
    BitsRPC  .init0();
  }

  // Reset all global statics for the next parse.  Useful during testing when
  // many top-level parses happen in a row.
  static void top_reset() {
    while( DEFMEM.len() > MAX_ALIAS ) DEFMEM.pop();
    TV2       .reset_to_init0();
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
  UnOrFunPtrNode lookup_filter_uni( String name ) {
    if( !Parse.isOp(name) ) return null; // Limit to operators
    for( int i=name.length(); i>0; i-- ) {
      UnOrFunPtrNode n = (UnOrFunPtrNode)lookup((name.substring(0,i)+"_").intern());
      if( n != null && n.op_prec() > 0 ) { // First name found will return
        UnOrFunPtrNode m = n.filter(1);    // Filter down to 1 arg
        if( m!=null )
          return m;
      }
    }
    return null;
  }

  UnOrFunPtrNode lookup_filter_2( String name ) {
    if( !Parse.isOp(name) ) return null; // Limit to operators
    for( int i=name.length(); i>0; i-- ) {
      UnOrFunPtrNode n = (UnOrFunPtrNode)lookup(("_"+name.substring(0,i)+"_").intern());
      if( n != null && n.op_prec() > 0 ) { // First name found will return
        UnOrFunPtrNode m = n.filter(2);    // Filter down to 2 args
        if( m!=null )
          return m;
      }
    }
    return null;
  }

  String lookup_filter_bal( String bopen ) {
    if( !Parse.isOp(bopen) ) return null; // Limit to operators
    for( int i=bopen.length(); i>0; i-- ) {
      UnOrFunPtrNode n = (UnOrFunPtrNode)lookup(("_"+bopen.substring(0,i)+"_").intern());
      if( n != null && n.op_prec() == 0 ) // First name found will return
        return n.funptr()._name;
    }
    return null;
  }

  UnOrFunPtrNode lookup_filter_bal( String bopen, String bclose ) {
    if( !Parse.isOp(bopen ) ) return null; // Limit to operators
    if( !Parse.isOp(bclose) ) return null; // Limit to operators
    String name = ("_"+bopen+"_"+bclose+"_").intern();
    // Try both the 2 and 3 forms
    //UnOrFunPtrNode n = (UnOrFunPtrNode)lookup(name);
    //if( n != null && n.op_prec()==0 )
    //  return n;
    //return null;
    throw unimpl();
  }

  // Update function name token to Node mapping in the current scope
  Node add_fun( Parse bad, String name, Node val ) { return _scope.stk().add_fun(bad,name,(FunPtrNode)val); }


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

  // Collect TVars from all variables in-scope.  Used to build a
  // "non-generative" set of TVars for Hindley-Milner typing.
  public HashSet<TV2> collect_active_scope() {
    HashSet<TV2> tvars = new HashSet<>();
    Env e = this;
    while( e!=null ) {
      for( Node def : _scope.stk()._defs )
        if( def != null ) tvars.add(def.tvar());
      e = e._par;
    }
    return tvars;
  }

  // Small classic tree of TV2s, immutable, with sharing at the root parts.
  // Used to track the lexical scopes of vars, to allow for the H-M 'occurs_in'
  // check.  This stack sub-sequences the main Env._scope stack, having splits
  // for every unrelated set of mutually-self-recursive definitions.  This is
  // typically just a single variable, currently being defined.
  Node nongen_pop(Node ret) { _nongen = _nongen._par; return ret;}
  void nongen_push(Env par) { _nongen = new VStack(par._nongen); }
  public static class VStack {
    public final VStack _par;          // Parent
    public Ary<String> _flds;          // Field names, unique per-Scope
    public Ary<TV2> _tvars; // Type variable, set at first reference (forward-ref or not)
    private VStack( VStack par ) { _par=par; _flds = new Ary<>(new String[1],0); _tvars = new Ary<>(new TV2[1],0); }
    String add_var(String fld, TV2 tv) { _flds.push(fld);  _tvars.push(tv); return fld; }
    public boolean isEmpty() {
      return _flds.isEmpty() && (_par == null || _par.isEmpty());
    }

    // Return a compact list of active tvars
    public TV2[] compact() {
      int cnt=0;
      for( VStack vs = this; vs!=null; vs=vs._par )
        cnt += vs._tvars._len;
      TV2[] tv2s = new TV2[cnt];
      cnt=0;
      for( VStack vs = this; vs!=null; vs=vs._par ) {
        System.arraycopy(vs._tvars._es,0,tv2s,cnt,vs._tvars._len);
        cnt += vs._tvars._len;
      }
      return tv2s;
    }


    @Override public String toString() {
      // These types get large & complex; find all the dups up-front to allow
      // for prettier printing.  Uses '$A' style for repeats.
      VBitSet dups  = new VBitSet();
      VBitSet visit = new VBitSet();
      for( VStack vs = this; vs!=null ; vs=vs._par )
        if( vs._tvars != null )
          for( TV2 tv2 : vs._tvars )
            if( tv2 != null ) tv2._get_dups(visit,dups);

      // Print stack of types, grouped by depth
      visit.clr();
      SB sb = new SB().p("[");
      for( VStack vs = this; vs!=null ; vs=vs._par ) {
        if( vs._tvars != null ) {
          for( int i=0; i<vs._tvars._len; i++ ) {
            sb.p(vs._flds.at(i)).p('=');
            TV2 tv2 = vs._tvars.at(i);
            if( tv2 !=null ) tv2.str(sb,visit,dups,true);
            sb.p(", ");
          }
          if( vs._tvars._len>0 ) sb.unchar(2);
        }
        sb.p(" >> ");
      }
      if( _par!=null ) sb.unchar(4);
      return sb.p("]").toString();
    }
  }

  Env lookup_fref(String tok) {
    if( _nongen!=null && _nongen._flds.find(tok)!= -1 ) return this;
    return _par==null ? null : _par.lookup_fref(tok);
  }
}
