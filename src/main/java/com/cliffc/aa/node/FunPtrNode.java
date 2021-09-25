package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.*;
import static com.cliffc.aa.Env.GVN;

// See CallNode and FunNode comments. The FunPtrNode converts a RetNode into a
// TypeFunPtr with a constant fidx and variable displays.  Used to allow first
// class functions to be passed about.

// FIDXs above-center are used by UnresolvedNode to represent choice.
// Normal FunPtrs, in both GCP and Opto/Iter, should be a single (low) FIDX.

// Display is e.g. *[12] (alias 12 struct), or some other thing to represent an
// unused/dead display.  I've been using either ANY or XNIL.

// There are several invariants we'd like to have:

// The FIDX and DISP match sign: so {-15,ANY} and {+15,NIL} are OK, but
// {+15,XNIL} and {+15,ANY} are not.  This one is in conflict with the others,
// and is DROPPED.  Instead we allow e.g. {+15,ANY} to indicate a FIDX 15 with
// no display.
//
// FunPtrNodes strictly fall during GCP; lift during Opto.
// So e.g. any -> [-15,any] -> [-15,-12] -> [+15,+12] -> [+15,all] -> all.
// But need to fall preserving the existing of DISP.
// So e.g.  any -> [-15,any] -> [-15,xnil] -> [+15,nil] -> [+15,all] -> all.
// So e.g.  any -> [-15,-12] ->                            [+15,+12] -> all.
//
// FunPtrNodes start being passed e.g. [+12], but during GCP can discover DISP
// is dead... but then after GCP need to migrate the types from [+15,+12] to
// [+15,nil] which is sideways.  Has to happen in a single monolithic pass
// covering all instances of [+15,+12].  Also may impact mixed +15 and other
// FIDXs with unrelated DISPs.  Instead a dead display just flips to ANY.

public final class FunPtrNode extends UnOrFunPtrNode {
  public String _name;          // Optional for debug only
  private ErrMsg _referr;       // Forward-ref error, cleared after defining

  // Every var use that results in a function, so actually only these FunPtrs,
  // needs to make a "fresh" copy before unification.  "Fresh" makes a
  // structural copy of the TVar, keeping TVars from Nodes currently in-scope
  // as-is, and making structural copies of out-of-scope TVars.  The only
  // interesting thing is when an out-of-scope TVar uses the same TVar
  // internally in different parts - the copy replicates this structure.  When
  // unified, it forces equivalence in the same places.
  public  FunPtrNode( String name, RetNode ret, Node display ) { this(name,null,ret,display ); }
  // Explicitly, no display
  public  FunPtrNode( String name, RetNode ret ) { this(name,null,ret, Env.ANY ); }
  // Display (already fresh-loaded) but no name.
  public  FunPtrNode( RetNode ret, Node display ) { this(null,null,ret,display); }
  // For forward-refs only; super weak display & function.
  private FunPtrNode( String name, ErrMsg referr, RetNode ret, Node display ) {
    super(OP_FUNPTR,ret,display);
    _name = name;
    _referr = referr;
  }
  public RetNode ret() { return (RetNode)in(0); }
  public Node display(){ return in(1); }
  public FunNode fun() { return ret().fun(); }
  public FunNode xfun() { RetNode ret = ret(); return ret !=null && ret.in(4) instanceof FunNode ? ret.fun() : null; }
  @Override public int nargs() { return ret()._nargs; }
  @Override public FunPtrNode funptr() { return this; }
  @Override public UnresolvedNode unk() { return null; }
  // Self short name
  @Override public String xstr() {
    RetNode ret = ret();
    if( is_dead() || _defs._len==0 || ret==null) return "*fun";
    return "*"+_name;
  }
  // Inline longer name
  @Override String str() {
    if( is_dead() ) return "DEAD";
    if( _defs._len==0 ) return "MAKING";
    RetNode ret = ret();
    if( ret==null || ret.is_copy() ) return "gensym:"+xstr();
    FunNode fun = ret.fun();
    return fun==null ? xstr() : fun.str();
  }

  // Debug only: make an attempt to bind name to a function
  public void bind( String tok ) {
    _name = tok;
    fun().bind(tok);
  }

  @Override public Node ideal_reduce() {
    if( is_forward_ref() ) return null;

    Node dsp = display();
    if( dsp!=Env.ANY ) {
      Type tdsp = dsp._val;
      FunNode fun;
      // Display is known dead?
      if( (tdsp instanceof TypeMemPtr && ((TypeMemPtr)tdsp)._obj==TypeObj.UNUSED) ||
          // Collapsing to a gensym, no need for display
          ret().is_copy() ||
          // Also unused if function has no display parm.
          ((fun=xfun())!=null && fun.is_copy(0)==null && fun.parm(DSP_IDX)==null) ||
          // Remove unused displays.  Track uses; Calling with no display is OK.
          // Uses storing the FPTR and passing it along still require a display.
          (GVN._opt_mode._CG && !display_used())
          )
        return set_def(1,Env.ANY); // No display needed
    }
    return null;
  }
  // Called if Display goes unused
  @Override public void add_work_use_extra(Work work, Node chg) {
    Type tdsp = display()._val;
    if( tdsp instanceof TypeMemPtr && ((TypeMemPtr)tdsp)._obj==TypeObj.UNUSED )
      Env.GVN.add_reduce(this);
  }

  // Is the display used?  Calls may use the TFP portion but not the display.
  private boolean display_used() {
    for( Node call : _uses ) {
      if( !(call instanceof CallNode) ) return true; // Anything other than a Call is using the display
      for( int i=ARG_IDX; i<call.len(); i++ )
        if( call.in(i)==this ) return true; // Call-use other than the last position is using the display portion of this FPTR
      assert ((CallNode)call).fdx()==this;
      if( ProjNode.proj(call,DSP_IDX)!=null )
        return true;            // Call needs the display and fptr both
    }
    return false;               // Only uses are Calls needing the fptr but not the display
  }


  @Override public Type value(GVNGCM.Mode opt_mode) {
    if( !(in(0) instanceof RetNode) )
      return TypeFunPtr.EMPTY;
    return TypeFunPtr.make(ret()._fidx,nargs(),display()._val);
  }
  @Override public void add_work_extra(Work work, Type old) {
    if( old==_live )            // live impacts value
      work.add(this);
  }

  @Override public TypeMem live(GVNGCM.Mode opt_mode) {
    // Pre-GCP, might be used anywhere (still finding the CFG)
    return !opt_mode._CG ? TypeMem.ESCAPE : super.live(opt_mode);
  }
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    return def==ret() ? TypeMem.ANYMEM : (_live==TypeMem.LNO_DISP ? TypeMem.DEAD : TypeMem.ESCAPE);
  }

  @Override public boolean unify( Work work ) {
    TV2 self = tvar();
    if( self.is_err() ) return false;
    if( is_forward_ref() )
      return work==null || self.unify(TV2.make_err(this,"A forward reference is not a function","FunPtr_unify"),work);
    RetNode ret = ret();
    if( ret.is_copy() ) return false; // GENSYM
    FunNode fun = ret.fun();

    boolean progress = false;
    if( !self.is_fun() ) {      // Force a function if not already
      if( work==null ) return true;
      progress = self.unify(TV2.make_fun(ret.rez(),TypeFunPtr.make(fun._fidx,fun._sig.nargs(),TypeMemPtr.NO_DISP),fun._sig,"FunPtr_unify"),work);
      self = self.find();
    }

    // Return
    progress |= self.unify_at(ret.rez()," ret",ret.rez().tvar(),work);

    // Each argument from the parms directly
    Node[] parms = fun.parms();
    for( int i=DSP_IDX; i<parms.length; i++ ) {
      if( parms[i]==null ) continue;
      String key = (""+i).intern();
      TV2 old = self.get(key);
      TV2 arg = parms[i].tvar();
      assert arg!=null;//if( arg==null )  arg = TV2.make_leaf(fun,"FunPtr_unify"); // null on 1st visit to a missing (unused) parm
      if( old==arg ) continue;      // No progress
      if( work==null ) return true; // Early cutout
      progress |= self.unify_at(parms[i],key,arg,work);
    }

    return progress;
  }

  // Filter out all the wrong-arg-count functions from Parser.
  @Override public FunPtrNode filter( int nargs ) {
    // User-nargs are user-visible #arguments.
    // Fun-nargs include ctrl, memory & the display, hence the +ARG_IDX.
    return nargs() == ARG_IDX+nargs ? this : null;
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
  public static FunPtrNode forward_ref( GVNGCM gvn, String name, Parse unkref ) {
    FunNode fun = gvn.init(new FunNode(name)).unkeep(2);
    RetNode ret = gvn.init(new RetNode(fun,Node.con(TypeMem.MEM),Node.con(Type.SCALAR),Node.con(TypeRPC.ALL_CALL),fun)).unkeep(2);
    gvn.add_flow(fun);
    gvn.add_flow(ret);
    // Display is limited to any one of the current lexical scopes.
    TypeMemPtr tdisp = TypeMemPtr.make(Env.LEX_DISPLAYS,TypeObj.ISUSED);
    return new FunPtrNode( name, ErrMsg.forward_ref(unkref,name),ret,Node.con(tdisp));
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

    // Make a function pointer based on the original forward-ref fidx, but with
    // the known types.
    FunNode.FUNS.setX(dfun._fidx,null); // Untrack dfun by old fidx
    dfun._fidx = rfun._fidx;
    FunNode.FUNS.setX(dfun._fidx,dfun); // Track FunNode by new fidx
    ret().unelock();
    ret()._fidx = 0; // No longer killing def fidx when dying

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

    dsp.update(tok,dsp.access(tok),def);
    fptr.bind(tok); // Debug only, associate variable name with function
    assert Env.START.more_flow(Env.GVN._work_flow,true)==0;
    Env.GVN.iter(GVNGCM.Mode.Parse);
  }

  @Override public ErrMsg err( boolean fast ) { return is_forward_ref() ? _referr : null; }
}
