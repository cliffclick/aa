package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.tvar.TVar;
import com.cliffc.aa.tvar.TTup3;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeTuple;

// See CallNode comments.  The RetNode gathers {control (function exits or
// not), memory, value, rpc, fun}, and sits at the end of a function.  The RPC
// dictates which calls can be reached from here.  The Fun is used to rapidly
// find the FunNode, as a SESE region shortcut.  A FunPtrNode points to this
// Ret, and is used for all function-pointer uses.  Otherwise only CallEpis
// point to a Ret representing wired calls.

public final class RetNode extends Node {
  int _fidx;                 // Shortcut to fidx when the FunNode has collapsed
  int _nargs;                // Replicated from FunNode
  public RetNode( Node ctrl, Node mem, Node val, Node rpc, FunNode fun ) {
    super(OP_RET,ctrl,mem,val,rpc,fun);
    _fidx = fun._fidx;
    _nargs=fun.nargs();
    // RetNodes are structural copies of their inputs, reflect this in their type variables
    tvar().unify(new TTup3(this));
  }
  public Node ctl() { return in(0); }
  public Node mem() { return in(1); }
  public Node rez() { return in(2); }
  public Node rpc() { return in(3); }
  public FunNode fun() { return (FunNode)in(4); }
  @Override public boolean is_mem() { return true; }
  // If this function is not using any displays, then there is a single unique
  // FunPtr.  Otherwise this call is ambiguous, as each execution of the
  // FunPtrNode makes a new display.
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
  @Override public int hashCode() { return super.hashCode()+_fidx; }
  @Override public boolean equals(Object o) {
    if( !super.equals(o) ) return false;
    return _fidx==((RetNode)o)._fidx;
  }

  // Short self name
  @Override String xstr() {
    if( is_dead() ) return "Ret";
    FunNode fun = FunNode.find_fidx(_fidx);
    return "Ret_"+(is_copy() ? "!copy!" : (fun==null ? ""+_fidx : fun.name()));
  }

  @Override public Node ideal(GVNGCM gvn, int level) {
    // If control is dead, but the Ret is alive, we're probably only using the
    // FunPtr as a 'gensym'.  Nuke the function body.
    if( !is_copy() && ctl().val() == Type.XCTRL && !is_prim() && fun().val() ==Type.XCTRL )
      set_def(4,null,gvn);      // We're a copy now!

    // If no users inlining, wipe out all edges
    if( is_copy() && in(0)!=null ) {
      boolean only_fptr = true;
      for( Node use : _uses )  if( !(use instanceof FunPtrNode) ) { only_fptr=false; break; }
      if( only_fptr ) {           // Only funptr uses, make them all gensyms
        set_def(0,null,gvn);      // No ctrl
        set_def(1,null,gvn); if( is_dead() ) return this; // No mem
        set_def(2,null,gvn);      // No val
        set_def(3,null,gvn);      // No rpc
        set_def(4,null,gvn);      // No fun
        _tvar = new TVar(this);   // Not unified into anything
        return this;              // Progress
      }
    }
    if( is_copy() ) return null;
    // Collapsed to a constant?  Remove any control interior.
    Node ctl = ctl();
    if( rez().val().is_con() && ctl!=fun() && // Profit: can change control and delete function interior
        (mem().val() ==TypeMem.EMPTY || (mem() instanceof ParmNode && mem().in(0)==fun())) ) // Memory has to be trivial also
      return set_def(0,fun(),gvn); // Gut function body

    // Look for a tail recursive call
    Node tail = tail_recursive(gvn);
    if( tail != null ) return tail;

    return null;
  }

  // Look for a tail-Call.  There should be 1 (collapsed) Region, and maybe a
  // tail Call.  Look no further than 1 Region, since collapsing will fold
  // nested regions up.  Since the RetNode is a single "pinch point" for
  // control flow in the entire function, if we see a tail-call here, it means
  // the function ends in an infinite loop, not currently optimized.
  Node tail_recursive( GVNGCM gvn ) {
    Node ctl = ctl();
    if( ctl._op!=OP_REGION ) return null;
    int idx; for( idx=1; idx<ctl._defs._len; idx++ ) {
      Node c = ctl.in(idx), cepi = c.in(0);
      if( c._op == OP_CPROJ && cepi._op == OP_CALLEPI &&
          ((CallEpiNode)cepi).nwired()==1 &&
          ((CallEpiNode)cepi).wired(0)== this && // TODO: if in tail position, can be a tail call not self-recursive
          ((CallEpiNode)cepi).call().fun()._op == OP_FUNPTR ) // And a direct call
        break;
    }
    if( idx == ctl._defs._len ) return null; // No call-epi found
    CallEpiNode cepi = (CallEpiNode)ctl.in(idx).in(0);
    CallNode call = cepi.call();
    if( call.ctl().val() != Type.CTRL ) return null; // Dead call
    // Every Phi on the region must come directly from the CallEpi.
    for( Node phi : ctl._uses )
      if( phi._op == OP_PHI && phi.in(idx).in(0)!=cepi )
          return null;
    FunNode fun = fun();
    // Every Phi must be type compatible
    for( int i=0; i<call.nargs(); i++ )
      if( !check_phi_type(gvn,fun,call, i) )
        return null;

    // Behind the function entry, split out a LoopNode/Phi setup - one phi for
    // every argument.  The first input comes from the parms; the second input
    // from the Call arguments - including the control.  Cut the call control,
    // which will go dead & collapse.

    // Find the trailing control behind the Fun.
    Node cuse = null;           // Control use behind fun.
    for( Node use : fun._uses )
      if( use != this && use.is_CFG() )
        { assert cuse==null; cuse = use; }
    int cidx = cuse._defs.find(fun);
    // Insert loop in-the-middle
    LoopNode loop = new LoopNode();
    loop.add_def(fun);
    loop.add_def(call.ctl());
    loop = (LoopNode)gvn.xform(loop);
    gvn.set_def_reg(cuse,cidx,loop);
    // Insert loop phis in-the-middle
    for( int i=0; i<call.nargs(); i++ ) do_phi(gvn,fun,call,loop,i);
    // Cut the Call control
    gvn.set_def_reg(call,0, Env.XCTRL);

    return this;
  }

  private static boolean check_phi_type( GVNGCM gvn, FunNode fun, CallNode call, int argn ) {
    ParmNode parm = fun.parm(argn);
    if( parm==null ) return true; // arg/parm might be dead
    Type tenter = parm.val();
    Type tback  = call.argm(argn, gvn).val();
    return tback.isa(tenter);
  }

  private static void do_phi(GVNGCM gvn, FunNode fun, CallNode call, LoopNode loop, int argn) {
    ParmNode parm = fun.parm(argn);
    if( parm==null ) return; // arg/parm might be dead
    PhiNode phi = new PhiNode(parm._t,parm._badgc,loop,null,call.argm(argn,gvn));
    gvn.replace(parm,phi);
    phi.set_def(1,parm,null);
    phi._live = parm._live;
    gvn.rereg(phi, parm.val());
  }

  @Override public Type value(GVNGCM.Mode opt_mode) {
    if( ctl()==null ) return val(); // No change if a copy
    Type ctl = ctl().val();
    if( ctl != Type.CTRL ) return ctl.oob(TypeTuple.RET);
    Type mem = mem().val();
    if( !(mem instanceof TypeMem) ) mem = mem.oob(TypeMem.ALLMEM);
    Type val = rez().val();
    return TypeTuple.make(ctl,mem,val);
  }


  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
  @Override public TypeMem live(GVNGCM.Mode opt_mode) {
    // Pre-GCP, might be used anywhere (still finding CFG)
    return in(4) instanceof FunNode && fun().has_unknown_callers() && !opt_mode._CG ? TypeMem.ALLMEM : super.live(opt_mode);
  }
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    if( def==mem() ) return _live;
    if( def==rez() ) return TypeMem.ESCAPE;
    return TypeMem.ALIVE;       // Basic aliveness
  }

  @Override public Node is_copy(int idx) { throw com.cliffc.aa.AA.unimpl(); }
  boolean is_copy() { return !(in(4) instanceof FunNode) || fun()._fidx != _fidx; }
  @Override public boolean is_forward_ref() { return fun().is_forward_ref(); }
}
