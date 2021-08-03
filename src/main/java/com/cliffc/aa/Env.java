package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;

import java.util.HashSet;

import static com.cliffc.aa.type.TypeFld.Access;

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
  public static      ConNode NIL;   // Common NIL
  public static      ConNode ANY;   // Common ANY / used for dead
  public static      ConNode ALL;   // Common ALL / used for errors
  public static      ConNode ALL_CALL; // Common during function call construction
  // Set of all display aliases, used to track escaped displays at call sites for asserts.
  public static BitsAlias ALL_DISPLAYS = BitsAlias.EMPTY;
  // Set of lexically active display aliases, used for a conservative display
  // approx for forward references.
  public static BitsAlias LEX_DISPLAYS = BitsAlias.EMPTY;


  final public Env _par;         // Parent environment
  public final ScopeNode _scope; // Lexical anchor; "end of display"; goes when this environment leaves scope
  public VStack _nongen;         // Hindley-Milner "non-generative" variable set; current/pending defs

  // Top-level Env.  Contains, e.g. the primitives.
  // Above any file-scope level Env.
  private Env(  ) {
    _par = null;
    _nongen = null;
    _scope = init(CTL_0,XNIL,MEM_0,Type.XNIL,null,true);
  }

  // A file-level Env, or below.  Contains user written code.
  Env( Env par, Parse P, boolean is_closure, Node ctrl, Node mem ) {
    GVN._opt_mode=GVNGCM.Mode.Parse;
    _par = par;
    nongen_push(par);
    ScopeNode s = par._scope;   // Parent scope
    _scope = init(ctrl,s.ptr(),mem,s.stk()._tptr,P==null ? null : P.errMsg(),is_closure);
  }
  // Make the Scope object for an Env.
  private static ScopeNode init(Node ctl, Node clo, Node mem, Type back_ptr, Parse errmsg, boolean is_closure) {
    TypeStruct tdisp = TypeStruct.open(back_ptr);
    mem.keep();
    NewObjNode nnn = GVN.xform(new NewObjNode(is_closure,tdisp,clo)).keep();
    MrgProjNode  frm = DEFMEM.make_mem_proj(nnn,mem.unkeep());
    Node ptr = GVN.xform(new ProjNode(nnn.unkeep(),AA.REZ_IDX));
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
    NIL     = GVN.xform(new ConNode<>(Type.NIL  )).keep();
    ANY     = GVN.xform(new ConNode<>(Type.ANY  )).keep();
    ALL     = GVN.xform(new ConNode<>(Type.ALL  )).keep();
    ALL_CALL= GVN.xform(new ConNode<>(TypeRPC.ALL_CALL)).keep();
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
    STK_0.create_active("math_pi", Node.con(TypeFlt.PI),Access.Final);
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
    // Promote forward refs to the next outer scope
    ScopeNode pscope = _par._scope;
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
    TV2       .reset_to_init0();
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
    if( !(n instanceof UnresolvedNode) ) return n._val;
    // For unresolved, use the ambiguous type
    return n.value(GVNGCM.Mode.Opto);
  }

  // Lookup the operator name.  Use the longest name that's found, so that long
  // strings of operator characters are naturally broken by (greedy) strings.
  // If nargs is positive, filter by nargs.
  // If nargs is zero, this is a balanced-op lookup, filter by op_prec==0
  // Always makes a 'fresh' result, as-if HM.Ident primitive lookup.
  UnOrFunPtrNode lookup_filter_fresh( String name, int nargs, Node ctrl ) {
    if( !Parse.isOp(name) ) return null; // Limit to operators
    for( int i=name.length(); i>0; i-- ) {
      UnOrFunPtrNode n = (UnOrFunPtrNode)lookup(name.substring(0,i).intern());
      if( n != null ) {         // First name found will return
        UnOrFunPtrNode u = nargs == 0 // Requiring a balanced-op?
          ? (n.op_prec()==0 ? n : null) // Return a balanced-op or error
          : n.filter(nargs);    // Non-balanced ops also check arg count; distinguish e.g. -x from x-y.
        return u==null ? null : (UnOrFunPtrNode)Env.GVN.xform(new FreshNode(_nongen,ctrl,u));
      }
    }
    return null;
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
      NonBlockingHashMapLong<String> dups = new NonBlockingHashMapLong<>();
      VBitSet bs = new VBitSet();
      for( VStack vs = this; vs!=null ; vs=vs._par )
        if( vs._tvars != null )
          for( TV2 tv2 : vs._tvars )
            if( tv2 != null ) tv2.find_dups(bs,dups,0);

      // Print stack of types, grouped by depth
      bs.clr();
      SB sb = new SB().p("[");
      for( VStack vs = this; vs!=null ; vs=vs._par ) {
        if( vs._tvars != null ) {
          for( int i=0; i<vs._tvars._len; i++ ) {
            sb.p(vs._flds.at(i)).p('=');
            TV2 tv2 = vs._tvars.at(i);
            if( tv2 !=null ) tv2.str(sb,bs,dups,false,0,0);
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
