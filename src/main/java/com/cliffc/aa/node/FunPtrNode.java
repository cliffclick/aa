package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;
import com.cliffc.aa.tvar.*;
import org.jetbrains.annotations.NotNull;

// See CallNode and FunNode comments. The FunPtrNode converts a RetNode into a
// TypeFunPtr with a constant fidx and variable displays.  Used to allow 1st
// class functions to be passed about.
public final class FunPtrNode extends Node {
  private final ErrMsg _referr;
  // Every var use that results in a function, so actually only these FunPtrs,
  // needs to make a "fresh" copy before unification.  "Fresh" makes a
  // structural copy of the TVar, keeping TVars from Nodes currently in-scope
  // as-is, and making structural copies of out-of-scope TVars.  The only
  // interesting thing is when an out-of-scope TVar uses the same TVar
  // internally in different parts - the copy replicates this structure.  When
  // unified, it forces equivalence in the same places.
  public  FunPtrNode( RetNode ret, Env e ) { this(null,e,ret,e==null ? Env.GVN.con(TypeMemPtr.NO_DISP) : e._scope.ptr()); }
  public  FunPtrNode( RetNode ret, Env e, Node display ) { this(null,e,ret,display); }
  // For forward-refs only; super weak display & function.
  private FunPtrNode( ErrMsg referr, Env e, RetNode ret, Node display ) {
    super(OP_FUNPTR,ret,display);
    _referr = referr;
    // Add the "non-generative" set to the TFun structure, but no other
    // structural is available (args and ret are new TVars).
    tvar().unify(new TFun(this,e == null ? null : e.collect_active_scope(),new TVar(),new TVar()));
  }
  public RetNode ret() { return (RetNode)in(0); }
  public Node display(){ return in(1); }
  public FunNode fun() { return ret().fun(); }
  public FunNode xfun() { RetNode ret = ret(); return ret.in(4) instanceof FunNode ? ret.fun() : null; }
  // Self short name
  @Override public String xstr() {
    if( is_dead() ) return "*fun";
    int fidx = ret()._fidx;    // Reliably returns a fidx
    FunNode fun = FunNode.find_fidx(fidx);
    return "*"+(fun==null ? ""+fidx : fun.name());
  }
  // Inline longer name
  @Override String str() {
    if( is_dead() ) return "DEAD";
    RetNode ret = ret();
    if( ret.is_copy() ) return "gensym:"+xstr();
    FunNode fun = ret.fun();
    return fun==null ? xstr() : fun.str();
  }

  @Override public Node ideal(GVNGCM gvn, int level) {
    if( is_forward_ref() ) return null;

    // Display is known dead?  Yank it.
    if( display().in(0) instanceof NewNode ) {
      NewNode nn = (NewNode)display().in(0);
      if( nn._ts==nn.dead_type() ) {
        BitsAlias aliases = nn._tptr._aliases;
        return set_def(1,gvn.con(TypeMemPtr.make(aliases,aliases.oob(TypeObj.ISUSED))),gvn); // No display needed
      }
    }

    // Remove unused displays.  Track uses; Calls with no FPClosure are OK.
    // Uses storing the FPTR and passing it along are dangerous.
    if( gvn._opt_mode._CG && !(display() instanceof ConNode) ) {
      boolean safe=true;
      for( Node use : _uses )  {
        if( !(use instanceof CallNode) ) { safe=false; break; }
        CallNode call = (CallNode)use;
        for( int i=0; i<call.nargs(); i++ ) if( call.arg(i)==this ) { safe=false; break; }
        for( Node cuse : call._uses )
          if( cuse instanceof FP2ClosureNode )
            { safe=false; break; }
        if( !safe ) break;
      }
      if( safe ) {              // No unsafe users; nuke display
        TypeMemPtr tdisp = (TypeMemPtr) display().val();
        return set_def(1,gvn.con(tdisp.make_from(TypeObj.UNUSED)),gvn); // No display needed
      }
    }

    return null;
  }
  @Override public Type value(GVNGCM.Mode opt_mode) {
    if( !(in(0) instanceof RetNode) )
      return TypeFunPtr.EMPTY;
    RetNode ret = ret();
    Node disp = display();
    Type tdisp = disp.val();
    if( !(tdisp instanceof TypeMemPtr) )
      tdisp = tdisp.oob(TypeMemPtr.DISP_SIMPLE);
    return TypeFunPtr.make(ret._fidx,ret._nargs,(TypeMemPtr)tdisp);
  }

  @Override public TypeMem live(GVNGCM.Mode opt_mode) {
    // Pre-GCP, might be used anywhere (still finding the CFG)
    return !opt_mode._CG ? TypeMem.ESCAPE : super.live(opt_mode);
  }
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    return def==ret() ? TypeMem.ANYMEM : TypeMem.ESCAPE;
  }

  @Override public boolean unify( GVNGCM gvn, boolean test ) {
    // Build a HM tvar (args->ret), same as HM.java Lambda does.
    // FunNodes are just argument collections (no return).
    FunNode fun = xfun();
    if( fun==null ) return false;
    RetNode ret = ret();
    TFun tvar = (TFun)tvar();   // Self is always a TFun
    // Build function arguments; "fun" itself is just control.
    TArgs targs = new TArgs(fun,true);
    TVar tret  = ret.tvar();
    if( tvar.args().eq(targs) &&
        tvar.ret ().eq(tret ) )
      return false;             // No progress
    if( !test )
      tvar.unify(new TFun(this,tvar._nongen,targs,tret));
    return true;
  }

  // Filter out all the wrong-arg-count functions
  public Node filter( int nargs ) {
    // User-nargs are user-visible #arguments.
    // Fun-nargs include ctrl, memory & the display, hence the +3.
    return fun().nargs() == nargs+3 ? this : null;
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
    Node mem = ret.mem();
    if( mem.in(0)==fun && mem instanceof ParmNode ) return this; // Parm:mem on fun, no mods to memory
    return null;
  }

  // A forward-ref is an assumed unknown-function being used before being
  // declared.  Hence we want a callable function pointer, but have no defined
  // body (yet).  Make a function pointer that takes/ignores all args, and
  // returns a scalar.
  public static FunPtrNode forward_ref( GVNGCM gvn, String name, Parse unkref ) {
    FunNode fun = gvn.init(new FunNode(name));
    RetNode ret = gvn.init(new RetNode(fun,gvn.con(TypeMem.MEM),gvn.con(Type.SCALAR),gvn.con(TypeRPC.ALL_CALL),fun));
    // Display is limited to any one of the current lexical scopes.
    TypeMemPtr tdisp = TypeMemPtr.make(Env.LEX_DISPLAYS,TypeObj.ISUSED);
    return new FunPtrNode( ErrMsg.forward_ref(unkref,fun),null,ret,gvn.con(tdisp));
  }

  // True if this is a forward_ref
  @Override public boolean is_forward_ref() { return _referr!=null; }

  // 'this' is a forward reference, probably with multiple uses (and no inlined
  // callers).  Passed in the matching function definition, which is brand new
  // and has no uses.  Merge the two.
  public void merge_ref_def( GVNGCM gvn, String tok, FunPtrNode def, TypeMemPtr disp_ptr ) {
    FunNode rfun = fun();
    FunNode dfun = def.fun();
    assert rfun._defs._len==2 && rfun.in(0)==null && rfun.in(1) == Env.ALL_CTRL; // Forward ref has no callers
    assert dfun._defs._len==2 && dfun.in(0)==null;
    assert def ._uses._len==0;  // Def is brand new, no uses

    // Make a function pointer based on the original forward-ref fidx, but with
    // the known types.
    FunNode.FUNS.setX(dfun._fidx,null); // Untrack dfun by old fidx
    gvn.unreg(dfun);  dfun._fidx = rfun._fidx;  gvn.rereg(dfun,Type.CTRL);
    FunNode.FUNS.setX(dfun._fidx,dfun); // Track FunNode by fidx

    RetNode dret = def.ret();
    Type tret = gvn.unreg(dret);
    dret._fidx  = rfun._fidx ;
    gvn.rereg(dret,tret);
    FunPtrNode fptr = dret.funptr();
    fptr.xval(gvn._opt_mode);

    // Replace the forward_ref with the def.
    gvn.subsume(this,def);
    dfun.bind(tok);
  }

  @Override public ErrMsg err( boolean fast ) { return is_forward_ref() ? _referr : null; }
  // clones during inlining all become unique new sites
  @SuppressWarnings("unchecked")
  @Override @NotNull public FunPtrNode copy( boolean copy_edges, GVNGCM gvn) {
    FunPtrNode nnn = (FunPtrNode)super.copy(copy_edges, gvn);
    nnn.tvar().unify(new TFun(nnn,((TFun)_tvar)._nongen,new TVar(),new TVar()));
    return nnn;
  }
}
