package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.NonBlockingHashMap;

import static com.cliffc.aa.AA.ARG_IDX;
import static com.cliffc.aa.Env.GVN;

// See CallNode and FunNode comments. The FunPtrNode converts a RetNode into a
// TypeFunPtr with a constant fidx and variable displays.  Used to allow 1st
// class functions to be passed about.
public final class FunPtrNode extends UnOrFunPtrNode {
  public String _name;          // Optional for debug only
  private ErrMsg _referr;       // Forward-ref error, cleared after defining
  final Env.VStack _vs;         // Not-null means "fresh"

  // Every var use that results in a function, so actually only these FunPtrs,
  // needs to make a "fresh" copy before unification.  "Fresh" makes a
  // structural copy of the TVar, keeping TVars from Nodes currently in-scope
  // as-is, and making structural copies of out-of-scope TVars.  The only
  // interesting thing is when an out-of-scope TVar uses the same TVar
  // internally in different parts - the copy replicates this structure.  When
  // unified, it forces equivalence in the same places.
  public  FunPtrNode( String name, RetNode ret, Env env ) {
    this(name,null,ret,
         env==null ? Node.con(TypeMemPtr.NO_DISP) : env._scope.ptr(),
         env==null ? null : env._nongen);
  }
  public  FunPtrNode( RetNode ret, Node display ) { this(null,null,ret,display,null); }
  // For forward-refs only; super weak display & function.
  private FunPtrNode( String name, ErrMsg referr, RetNode ret, Node display, Env.VStack vs ) {
    super(OP_FUNPTR,ret,display);
    _name = name;
    _referr = referr;
    _vs = vs;
  }
  public RetNode ret() { return (RetNode)in(0); }
  public Node display(){ return in(1); }
  public FunNode fun() { return ret().fun(); }
  public FunNode xfun() { RetNode ret = ret(); return ret.in(4) instanceof FunNode ? ret.fun() : null; }
  @Override public int nargs() { return ret()._nargs; }
  @Override public FunPtrNode funptr() { return this; }
  @Override public boolean is_fresh() { return _vs!=null; }
  // Self short name
  @Override public String xstr() {
    if( is_dead() || _defs._len==0 ) return "*fun";
    int fidx = ret()._fidx;    // Reliably returns a fidx
    FunNode fun = FunNode.find_fidx(fidx);
    return (_vs!=null ? "@" : "*")+(fun==null ? ""+fidx : fun.name());
  }
  // Inline longer name
  @Override String str() {
    if( is_dead() ) return "DEAD";
    if( _defs._len==0 ) return "MAKING";
    RetNode ret = ret();
    if( ret.is_copy() ) return "gensym:"+xstr();
    FunNode fun = ret.fun();
    return fun==null ? xstr() : fun.str();
  }

  // Debug only: make an attempt to bind name to a function
  public void bind( String tok ) {
    assert _name==null || _name.equals(tok); // Attempt to double-bind
    _name = tok;
    fun().bind(tok);
  }

  @Override public Node ideal_reduce() {
    if( is_forward_ref() ) return null;

    // Display is known dead?  Yank it.
    Node dsp = display();
    Type tdsp = dsp._val;
    if( tdsp instanceof TypeMemPtr && ((TypeMemPtr)tdsp)._obj==TypeObj.UNUSED && !(dsp instanceof ConNode) )
      return set_def(1,Env.ANY); // No display needed

    // Remove unused displays.  Track uses; Calling with no display is OK.
    // Uses storing the FPTR and passing it along still require a display.
    if( GVN._opt_mode._CG && !(dsp instanceof ConNode) && !display_used() )
      return set_def(1,Env.ANY); // No display needed
    return null;
  }
  // Called if Display goes unused
  @Override public void add_flow_use_extra(Node chg) {
    Type tdsp = display()._val;
    if( tdsp instanceof TypeMemPtr && ((TypeMemPtr)tdsp)._obj==TypeObj.UNUSED )
      Env.GVN.add_reduce(this);
  }

  // Is the display used?
  private boolean display_used() {
    for( Node call : _uses ) {
      if( call instanceof CallNode ) {
        if( call._defs.find(e->e==this) < call._defs._len-1 )
          return true;          // Call-use other than the last position is using the display
      } else {
        return true;            // Anything other than a Call is using the display
      }
    }
    return false;
  }


  @Override public Type value(GVNGCM.Mode opt_mode) {
    if( !(in(0) instanceof RetNode) )
      return TypeFunPtr.EMPTY;
    return TypeFunPtr.make(ret()._fidx,nargs(),display()._val);
  }

  @Override public TypeMem live(GVNGCM.Mode opt_mode) {
    // Pre-GCP, might be used anywhere (still finding the CFG)
    return !opt_mode._CG ? TypeMem.ESCAPE : super.live(opt_mode);
  }
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    return def==ret() ? TypeMem.ANYMEM : TypeMem.ESCAPE;
  }

  @Override public TV2 new_tvar(String alloc_site) {
    return TV2.make("Fun",this,alloc_site);
  }

  @Override public boolean unify( boolean test ) {
    // Build a HM tvar (args->ret), same as HM.java Lambda does.
    // FunNodes are just argument collections (no return).
    RetNode ret = ret();
    FunNode fun = xfun();
    if( fun==null ) return false;
    TV2 tret = ret.tvar();
    if( tret.is_dead() ) return false;
    assert tret.isa("Ret"); // Ret is always a Ret

    // Check for progress before allocation
    TV2 tvar = tvar();
    if( tvar.is_dead() ) return false;
    assert tvar.isa("Fun"); // Self is always a Fun
    TV2 tvar_args = tvar.get("Args");
    TV2 tvar_ret  = tvar.get("Ret" );
    Node[] parms = fun.parms();
    parms[0] = fun;
    if( tvar_args!=null && tvar_args.eq(parms) && tvar_ret==tret ) return false; // Equal parts
    // Build function arguments; "fun" itself is just control.
    TV2 targ = TV2.make("Args",fun,"FunPtr_unify_Args",parms);
    NonBlockingHashMap<Object,TV2> args = new NonBlockingHashMap<Object,TV2>(){{ put("Args",targ);  put("Ret",tret); }};
    TV2 tfun = TV2.make("Fun",this,"FunPtr_unify_Fun",args);
    return tvar.unify(tfun,test);
  }

  // Filter out all the wrong-arg-count functions from Parser.
  // Always return a FRESH copy, as-if HM.Ident primitive lookup.
  @Override public FunPtrNode filter_fresh( Env env, int nargs ) {
    // User-nargs are user-visible #arguments.
    // Fun-nargs include ctrl, memory & the display, hence the +3.
    return nargs() == ARG_IDX+nargs ? fresh(env._nongen) : null;
  }

  // Always return a FRESH copy, as-if HM.Ident primitive lookup.
  @Override public FunPtrNode fresh( Env.VStack vs ) {
    FunPtrNode fptr = new FunPtrNode(_name,_referr,ret(),display(),vs);
    tvar().fresh_unify(fptr.tvar(),vs,false); // Make a fresh copy of the type var
    fptr.xval();
    return fptr;
  }

  // Return the op_prec of the returned value.  Not sensible except when called
  // on primitives.
  @Override public byte op_prec() { return fun()._op_prec; }

  // Instead of returning the pre-call memory on true, returns self.
  // Changes as the graph changes, because works purely off of graph shape.
  @Override Node is_pure_call() {
    // See if the RetNode points to a Parm:mem (so no mods on memory).
    RetNode ret = ret();
    if( ret.is_copy() ) return null;
    FunNode fun = ret.fun();
    if( fun.noinline() ) return null; // Disallow if no-inline
    Node mem = ret.mem();
    if( mem.in(0)==fun && mem instanceof ParmNode ) return this; // Parm:mem on fun, no mods to memory
    return null;
  }

  // A forward-ref is an assumed unknown-function being used before being
  // declared.  Hence we want a callable function pointer, but have no defined
  // body (yet).  Make a function pointer that takes/ignores all args, and
  // returns a scalar.
  public static FunPtrNode forward_ref( GVNGCM gvn, String name, Parse unkref, Env e ) {
    FunNode fun = gvn.init(new FunNode(name)).unkeep();
    RetNode ret = gvn.init(new RetNode(fun,Node.con(TypeMem.MEM),Node.con(Type.SCALAR),Node.con(TypeRPC.ALL_CALL),fun)).unkeep();
    gvn.add_flow(fun);
    gvn.add_flow(ret);
    // Display is limited to any one of the current lexical scopes.
    TypeMemPtr tdisp = TypeMemPtr.make(Env.LEX_DISPLAYS,TypeObj.ISUSED);
    return new FunPtrNode( name, ErrMsg.forward_ref(unkref,name),ret,Node.con(tdisp),e._nongen);
  }

  // True if this is a forward_ref
  @Override public boolean is_forward_ref() { return _referr!=null; }

  // 'this' is a forward reference, probably with multiple uses (and no inlined
  // callers).  Passed in the matching function definition, which is brand new
  // and has no uses.  Merge the two.
  public void merge_ref_def( String tok, FunPtrNode def, NewObjNode dsp ) {
    FunNode rfun = fun();
    FunNode dfun = def.fun();
    assert rfun._defs._len==2 && rfun.in(0)==null && rfun.in(1) == Env.ALL_CTRL; // Forward ref has no callers
    assert dfun._defs._len==2 && dfun.in(0)==null;
    assert def ._uses._len==0;  // Def is brand new, no uses
    assert _vs!=null && def._vs==null;

    // Make a function pointer based on the original forward-ref fidx, but with
    // the known types.
    FunNode.FUNS.setX(dfun._fidx,null); // Untrack dfun by old fidx
    dfun._fidx = rfun._fidx;
    FunNode.FUNS.setX(dfun._fidx,dfun); // Track FunNode by new fidx

    // Update the fidx
    RetNode dret = def.ret();
    dret.set_fidx(rfun._fidx);
    FunPtrNode fptr = dret.funptr();
    fptr.xval();
    Env.GVN.add_flow_uses(this);

    // The existing forward-ref becomes a normal (not f-ref) but internal
    // FunPtr; the H-M type is NOT Fresh, and forces alignment amongst the
    // recursive uses.  Make a new FunPtr which IS Fresh for future external
    // uses.
    _referr = null;             // No longer a forward ref
    set_def(0,def.in(0));       // Same inputs
    set_def(1,def.in(1));
    dsp.set_def(NewObjNode.def_idx(dsp._ts.find(tok)),def);
    dsp.tvar().reset_at(tok);
    dsp.xval();

    fptr.bind(tok); // Debug only, associate variable name with function
    Env.GVN.add_reduce_uses(this);
    assert Env.START.more_flow(true)==0;
    Env.GVN.iter(GVNGCM.Mode.Parse);
  }

  @Override public int hashCode() { return super.hashCode()+(_vs==null ? 0 : 1); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof FunPtrNode) ) return false;
    FunPtrNode fptr = (FunPtrNode)o;
    return _vs==null && fptr._vs==null; // Unequal if either is FRESH, need to keep the TVARs from unifying
  }

  @Override public ErrMsg err( boolean fast ) { return is_forward_ref() ? _referr : null; }
}
