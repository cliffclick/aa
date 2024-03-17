package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;

import static com.cliffc.aa.AA.*;

// See CallNode comments.  The RetNode gathers {control (function exits or
// not), memory, value, rpc, fun}, and sits at the end of a function.  The RPC
// dictates which calls can be reached from here.  The Fun is used to rapidly
// find the FunNode, as a SESE region shortcut.  A FunPtrNode points to this
// Ret, and is used for all function-pointer uses.  Otherwise, only CallEpis
// point to a RetNode representing wired calls.

public final class RetNode extends Node {
  int _fidx;                 // Shortcut to fidx when the FunNode has collapsed
  int _nargs;                // Replicated from FunNode
  public RetNode( Node ctrl, Node mem, Node val, Node rpc, FunNode fun ) {
    super(ctrl,mem,val,rpc,fun);
    _nargs=fun.nargs();
    set_fidx(fun._fidx);
    _live = RootNode.removeKills(null);   // All mem minus KILLS
  }
  
  // Short self name
  @Override public String label() {
    if( isDead() ) return "Ret!";
    FunNode fun = in(4) instanceof FunNode fun2 ? fun2 : null;
    return "Ret"+(isCopy() ? "!copy!" : (fun==null ? "["+_fidx+"]" : fun._name));
  }
  
  @Override public boolean isCFG() { return true; }
  @Override public boolean isMem() { return true; }
  @Override public Node isCopy(int idx) { return isCopy() ? in(idx) : null; }
  boolean isCopy() { return len() <= 4 || !(in(4) instanceof FunNode) || fun()._fidx != _fidx; }

  public Node ctl() { return in(0); }
  public Node mem() { return in(1); }
  public Node rez() { return in(2); }
  public Node rpc() { return in(3); }
  public FunNode fun() { return (FunNode)in(4); }
  
  public FunPtrNode funptr() {
    for( int i=0; i<nUses(); i++ )
      if( use(i) instanceof FunPtrNode fptr )
        return fptr;
    return null;
  }
  public int fidx() { return _fidx; }
  void set_fidx(int fidx) { unelock(); assert FUNS.at(_fidx)!=this; _fidx = fidx; FUNS.setX(fidx,this); } // Unlock before changing hash
  @Override int hash() { return _fidx; }
  @Override public boolean equals(Object o) {
    if( !super.equals(o) ) return false;
    return _fidx==((RetNode)o)._fidx;
  }
  // Formals from the function parms.
  // TODO: needs to come from both Combo and _t
  Type formal(int idx) { return fun().parm(idx)._t; }
  // Called by testing
  public TypeStruct formals() {
    ParmNode[] parms = fun().parms();
    TypeFld[] ts = TypeFlds.get(_nargs-DSP_IDX);
    for( int i=DSP_IDX; i<_nargs; i++ )
      ts[i-DSP_IDX] = TypeFld.make_tup(parms[i]==null ? Type.ANY : parms[i]._t, i);
    return TypeStruct.make(ts);
  }


  @Override public Type value() {
    if( ctl()==null ) return _val; // No change if a copy
    Type ctl = ctl()._val;
    if( ctl != Type.CTRL ) ctl = ctl.oob(Type.CTRL);
    Type mem = mem()==null ? TypeMem.ANYMEM : mem()._val;
    if( !(mem instanceof TypeMem) ) mem = mem.oob(TypeMem.ALLMEM);
    Type val = rez()._val;
    return TypeTuple.make(ctl,mem,val);
  }

  @Override public Type live_use( int i ) {
    return i==MEM_IDX ? _live : Type.ALL;
  }

  // Funs get special treatment by the H-M algo.
  @Override public boolean has_tvar() { return false; }

  @Override public Node ideal_reduce() {
    if( isPrim() ) return null;
    if( in(0)==null ) return null; // No users inlining; dead gensym
    Node cc = NodeUtil.fold_ccopy(this); // Fold control copies
    if( cc!=null ) return cc;
    
    // If the fun is a copy, then we are collapsing
    if( in(4) instanceof FunNode fun ) {
      Node cp = fun.isCopy(0);
      if( cp!=null ) setDef(4,cp);
    }

    // If control is dead, but the Ret is alive, we're probably only using the
    // FunPtr as a 'gensym'.  Nuke the function body.
    Node progress = null;
    if( !isCopy() ) {
      if( ctl()._val == Type.XCTRL && fun()._val ==Type.XCTRL ) {
        setDef(4,null);          // We're a copy now!
        progress=this;
        Env.GVN.add_reduce_uses(this); // Following FunPtrs do not need their displays
      }
    }

    // If no users inlining, wipe out all edges
    if( isCopy() && in(0)!=null ) {
      boolean only_fptr = true;
      for( Node use : uses() )  if( !(use instanceof FunPtrNode) ) { only_fptr=false; break; }
      if( only_fptr ) {         // Only funptr uses, make them all gensyms
        setDef(0,null);         // No ctrl
        setDef(1,null); if( isDead() ) return this; // No mem
        setDef(2,null);         // No val
        setDef(3,null);         // No rpc
        setDef(4,null);         // No fun
        return this;            // Progress
      }
    }
    if( isCopy() ) return progress;

    // Function is 'pure', nuke memory edge.
    Node mem = mem();
    if( mem instanceof ParmNode && mem.in(0)==fun() )
      return setDef(1,null);

    // Collapsed to a constant?  Remove any control interior.
    Node ctl = ctl();
    if( rez()._val.is_con() && !rez()._val.above_center() && ctl!=fun() && // Profit: can change control and delete function interior
        (mem==null || mem._val ==TypeMem.ANYMEM) ) // Memory has to be trivial also
      return setDef(0,fun());  // Gut function body

    return progress;
  }

  // Look for a tail recursive call
  @Override public Node ideal_mono() { return isCopy() ? null : tail_recursive(); }

  // Look for a tail-Call.  There should be 1 (collapsed) Region, and maybe a
  // tail Call.  Look no further than 1 Region, since collapsing will fold
  // nested regions up.  Since the RetNode is a single "pinch point" for
  // control flow in the entire function, if we see a tail-call here, it means
  // the function ends in an infinite loop, not currently optimized.
  Node tail_recursive() {
    Node ctl = ctl();
    if( !(ctl instanceof RegionNode) ) return null;
    int idx; for( idx=1; idx<ctl.len(); idx++ ) {
      Node c = ctl.in(idx), cepi0 = c.in(0);
      if( c instanceof CProjNode && cepi0 instanceof CallEpiNode cepi &&
          cepi.nwired()==1 &&
          cepi.wired(0)== this && // TODO: if in tail position, can be a tail call not self-recursive
          cepi.call().fdx() instanceof FunPtrNode ) // And a direct call
        break;
    }
    if( idx == ctl.len() ) return null; // No call-epi found
    CallEpiNode cepi = (CallEpiNode)ctl.in(idx).in(0);
    CallNode call = cepi.call();
    if( call.ctl()._val != Type.CTRL ) return null; // Dead call
    // Every Phi on the region must come directly from the CallEpi.
    for( Node phi : ctl.uses() )
      if( phi instanceof PhiNode && phi.in(idx).in(0)!=cepi )
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
    for( Node use : fun.uses() )
      if( use != this && use.isCFG() )
        { assert cuse==null; cuse = use; }
    assert cuse!=null;
    int cidx = cuse.findDef(fun);
    //// Insert loop in-the-middle
    //try(GVNGCM.Build<Node> X = Env.GVN.new Build<>()) {
    //  LoopNode loop = new LoopNode();
    //  loop.add_def(fun);
    //  loop.add_def(call.ctl());
    //  X.xform(loop);
    //  cuse.set_def(cidx,loop);
    //  // Insert loop phis in-the-middle
    //  for( int argn=MEM_IDX; argn<call.nargs(); argn++ ) {
    //    ParmNode parm = fun.parm(argn);
    //    if( parm==null ) continue; // arg/parm might be dead
    //    Node phi = new PhiNode(parm._t,parm._badgc,loop,null,call.arg(argn));
    //    phi._val  = parm._val ; // Inserting inside a loop, take optimistic values
    //    phi._live = parm._live; // Inserting inside a loop, take optimistic lives
    //    parm.insert(phi);
    //    phi.set_def(1,parm);
    //    X.add(phi);
    //  }
    //  // Cut the Call control
    //  call.set_def(0, Env.XCTRL);
    //  Env.GVN.add_unuse(call);
    //  return this;
    //}
    throw TODO();
  }

  private static boolean check_phi_type( FunNode fun, CallNode call, int argn ) {
    ParmNode parm = fun.parm(argn);
    if( parm==null ) return true; // arg/parm might be dead
    Type tenter = parm._val;
    Type tback  = call.arg(argn)._val;
    return tback.isa(tenter);
  }

  // Checks for sane Call Graph, similar to CallEpiNode.is_CG
  boolean is_CG( boolean precise ) {
    FunNode fun = fun();
    for( Node use : uses() ) {
      if( use instanceof CallEpiNode cepi ) {
        throw TODO();
      }
    }

    return true;
  }

  // Find RetNode by fidx
  private static int FLEN;      // Primitives length; reset amount
  static Ary<RetNode> FUNS = new Ary<>(new RetNode[]{null,});
  public static void init0() { FLEN = FUNS.len(); }
  public static void reset_to_init0() { FUNS.set_len(FLEN); }

  // Null if not a FunPtr to a Fun.
  public static RetNode get( int fidx ) {
    RetNode ret = FUNS.atX(fidx);
    if( ret==null || ret.isDead() ) return null;
    if( ret.fidx()==fidx ) return ret;
    // Split & renumbered FunNode, fixup in FUNS.
    throw TODO();
  }
  // First match from fidxs
  public static RetNode get( BitsFun fidxs ) {
    for( int fidx : fidxs ) {
      RetNode ret = get(fidx);
      if( ret!=null ) return ret;
    }
    return null;
  }

}
