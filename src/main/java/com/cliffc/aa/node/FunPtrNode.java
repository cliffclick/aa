package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

// See CallNode and FunNode comments. The FunPtrNode converts a RetNode into a
// TypeFunPtr with a constant fidx and variable displays.  Used to allow 1st
// class functions to be passed about.
public final class FunPtrNode extends Node {
  private final ErrMsg _referr;
  public  FunPtrNode( RetNode ret, Node display ) { this(null,ret,display); }
  // For forward-refs only; super weak display & function.
  private FunPtrNode( ErrMsg referr, RetNode ret, Node display ) {
    super(OP_FUNPTR,ret,display);
    _referr = referr;
  }
  public RetNode ret() { return (RetNode)in(0); }
  public Node display(){ return in(1); }
  public FunNode fun() { return ret().fun(); }
  // Self short name
  @Override String xstr() {
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
        TypeMemPtr tdisp = (TypeMemPtr)display()._val;
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
    Type tdisp = disp._val;
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

  // Filter out all the wrong-arg-count functions
  public Node filter( GVNGCM gvn, int nargs ) {
    // User-nargs are user-visible #arguments.
    // Fun-nargs include the display, hence the +1.
    return fun().nargs() == nargs+1 ? this : null;
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
    return new FunPtrNode( ErrMsg.forward_ref(unkref,fun),ret,gvn.con(tdisp));
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
}
