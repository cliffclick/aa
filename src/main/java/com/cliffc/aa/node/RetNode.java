package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeTuple;

import static com.cliffc.aa.AA.MEM_IDX;
import static com.cliffc.aa.AA.REZ_IDX;

/**
 See CallNode comments.  The RetNode gathers {control (function exits or
 not), memory, value, rpc, fun}, and sits at the end of a function.  The RPC
 dictates which calls can be reached from here.  The Fun is used to rapidly
 find the FunNode, as a SESE region shortcut.  A FunPtrNode points to this
 Ret, and is used for all function-pointer uses.  Otherwise only CallEpis
 point to a Ret representing wired calls.
*/

public final class RetNode extends Node {
  int _fidx;                 // Shortcut to fidx when the FunNode has collapsed
  int _nargs;                // Replicated from FunNode
  public RetNode( Node ctrl, Node mem, Node val, Node rpc, FunNode fun ) {
    super(OP_RET,ctrl,mem,val,rpc,fun);
    _fidx = fun._fidx;
    _nargs=fun.nargs();
    fun.unkeep();         // Unkeep the extra, now that a Ret completes the Fun
  }
  public Node ctl() { return in(0); }
  public Node mem() { return in(1); }
  public Node rez() { return in(2); }
  public Node rpc() { return in(3); }
  public FunNode fun() { return (FunNode)in(4); }
  @Override public boolean is_mem() { return true; }
  /**
   * If this function is not using any displays, then there is a single unique
   * FunPtr.  Otherwise this call is ambiguous, as each execution of the
   * FunPtrNode makes a new display.
   */
  public FunPtrNode funptr() {
    FunPtrNode fpn=null;
    for( Node use : _uses )
      if( use instanceof FunPtrNode ) {
        if( fpn!=null ) return null; // Ambiguous; several displays from the same function
        fpn = (FunPtrNode)use;
      }
    return fpn;                 // Zero (null) or 1 display.
  }
  public int fidx() { return _fidx; }
  void set_fidx(int fidx) { unelock(); _fidx = fidx; } // Unlock before changing hash
  @Override public int hashCode() { return super.hashCode()+_fidx; }
  @Override public boolean equals(Object o) {
    if( !super.equals(o) ) return false;
    return _fidx==((RetNode)o)._fidx;
  }

  // Short self name
  @Override public String xstr() {
    if( is_dead() ) return "Ret";
    FunNode fun = FunNode.find_fidx(_fidx);
    return "Ret_"+(is_copy() ? "!copy!" : (fun==null ? ""+_fidx : fun.name()));
  }

  @Override public Node ideal_reduce() {
    // If control is dead, but the Ret is alive, we're probably only using the
    // FunPtr as a 'gensym'.  Nuke the function body.
    if( !is_copy() && ctl()._val == Type.XCTRL && !is_prim() && fun()._val ==Type.XCTRL )
      set_def(4,null);          // We're a copy now!

    // If no users inlining, wipe out all edges
    if( is_copy() && in(0)!=null ) {
      boolean only_fptr = true;
      for( Node use : _uses )  if( !(use instanceof FunPtrNode) ) { only_fptr=false; break; }
      if( only_fptr ) {           // Only funptr uses, make them all gensyms
        set_def(0,null);          // No ctrl
        set_def(1,null); if( is_dead() ) return this; // No mem
        set_def(2,null);          // No val
        set_def(3,null);          // No rpc
        set_def(4,null);          // No fun
        return this;              // Progress
      }
    }
    if( is_copy() ) return null;
    // Collapsed to a constant?  Remove any control interior.
    Node ctl = ctl();
    if( rez()._val.is_con() && ctl!=fun() && // Profit: can change control and delete function interior
        (mem()._val ==TypeMem.EMPTY || (mem() instanceof ParmNode && mem().in(0)==fun())) ) // Memory has to be trivial also
      return set_def(0,fun());  // Gut function body
    return null;
  }

  // Look for a tail recursive call
  @Override public Node ideal_mono() { return is_copy() ? null : tail_recursive(); }

  // Look for a tail-Call.  There should be 1 (collapsed) Region, and maybe a
  // tail Call.  Look no further than 1 Region, since collapsing will fold
  // nested regions up.  Since the RetNode is a single "pinch point" for
  // control flow in the entire function, if we see a tail-call here, it means
  // the function ends in an infinite loop, not currently optimized.
  Node tail_recursive() {
    Node ctl = ctl();
    if( ctl._op!=OP_REGION ) return null;
    int idx; for( idx=1; idx<ctl._defs._len; idx++ ) {
      Node c = ctl.in(idx), cepi = c.in(0);
      if( c._op == OP_CPROJ && cepi._op == OP_CALLEPI &&
          ((CallEpiNode)cepi).nwired()==1 &&
          ((CallEpiNode)cepi).wired(0)== this && // TODO: if in tail position, can be a tail call not self-recursive
          ((CallEpiNode)cepi).call().fdx()._op == OP_FUNPTR ) // And a direct call
        break;
    }
    if( idx == ctl._defs._len ) return null; // No call-epi found
    CallEpiNode cepi = (CallEpiNode)ctl.in(idx).in(0);
    CallNode call = cepi.call();
    if( call.ctl()._val != Type.CTRL ) return null; // Dead call
    // Every Phi on the region must come directly from the CallEpi.
    for( Node phi : ctl._uses )
      if( phi._op == OP_PHI && phi.in(idx).in(0)!=cepi )
        return null;
    FunNode fun = fun();
    // Every Phi must be type compatible
    for( int i=MEM_IDX; i<call.nargs(); i++ )
      if( !check_phi_type(fun,call, i) )
        return null;

    // TODO: Turn this back on.
    // Currently does not unroll, which is the moral equivalent of repeated inlining...
    // so fails the Church-Rosser 1-step property.
    if( true ) return null;

    // Behind the function entry, split out a LoopNode/Phi setup - one phi for
    // every argument.  The first input comes from the parms; the second input
    // from the Call arguments - including the control.  Cut the call control,
    // which will go dead & collapse.

    // Find the trailing control behind the Fun.
    Node cuse = null;           // Control use behind fun.
    for( Node use : fun._uses )
      if( use != this && use.is_CFG() )
        { assert cuse==null; cuse = use; }
    assert cuse!=null;
    int cidx = cuse._defs.find(fun);
    // Insert loop in-the-middle
    try(GVNGCM.Build<Node> X = Env.GVN.new Build<>()) {
      LoopNode loop = new LoopNode();
      loop.add_def(fun);
      loop.add_def(call.ctl());
      X.xform(loop);
      cuse.set_def(cidx,loop);
      // Insert loop phis in-the-middle
      for( int argn=MEM_IDX; argn<call.nargs(); argn++ ) {
        ParmNode parm = fun.parm(argn);
        if( parm==null ) continue; // arg/parm might be dead
        Node phi = new PhiNode(parm._t,parm._badgc,loop,null,call.arg(argn));
        phi._val  = parm._val ; // Inserting inside a loop, take optimistic values
        phi._live = parm._live; // Inserting inside a loop, take optimistic lives
        parm.insert(phi);
        phi.set_def(1,parm);
        X.add(phi);
      }
      // Cut the Call control
      call.set_def(0, Env.XCTRL);
      Env.GVN.add_unuse(call);
      return this;
    }
  }

  private static boolean check_phi_type( FunNode fun, CallNode call, int argn ) {
    ParmNode parm = fun.parm(argn);
    if( parm==null ) return true; // arg/parm might be dead
    Type tenter = parm._val;
    Type tback  = call.arg(argn)._val;
    return tback.isa(tenter);
  }


  @Override public Type value(GVNGCM.Mode opt_mode) {
    if( ctl()==null ) return _val; // No change if a copy
    Type ctl = ctl()._val;
    if( ctl != Type.CTRL ) return ctl.oob(TypeTuple.RET);
    Type mem = mem()._val;
    if( !(mem instanceof TypeMem) ) mem = mem.oob(TypeMem.ALLMEM);
    Type val = rez()._val;
    return TypeTuple.make(ctl,mem,val);
  }


  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
  @Override public TypeMem live(GVNGCM.Mode opt_mode) {
    // Pre-GCP, might be used anywhere (still finding CFG)
    return !is_copy() && fun().has_unknown_callers() && !opt_mode._CG ? TypeMem.ALLMEM : super.live(opt_mode);
  }
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    if( def==mem() ) return _live;
    if( def==rez() ) return TypeMem.ESCAPE;
    return TypeMem.ALIVE;       // Basic aliveness
  }

  //@Override public TV2 new_tvar(String alloc_site) {
  //  return TV2.make("Ret",this,alloc_site);
  //}
  //
  //@Override public boolean unify( boolean test ) {
  //  if( is_copy() ) return false; // Disappearing
  //  FunPtrNode fptr = funptr();
  //  if( fptr != null && fptr.is_forward_ref() ) return false;
  //  TV2 tvar = tvar();
  //  if( tvar.is_dead() ) return false;
  //  assert tvar.isa("Ret");
  //  boolean progress = false;
  //  for( int i=0; i<=REZ_IDX; i++ )
  //    progress |= tvar.unify_at(i,tvar(i),test);
  //  return progress;
  //}

  @Override public Node is_copy(int idx) { throw com.cliffc.aa.AA.unimpl(); }
  boolean is_copy() { return !(in(4) instanceof FunNode) || fun()._fidx != _fidx; }
  @Override public boolean is_forward_ref() { return fun().is_forward_ref(); }
}
