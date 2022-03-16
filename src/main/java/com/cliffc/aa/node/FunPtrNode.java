package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.*;

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

public final class FunPtrNode extends Node {
  public String _name;          // Optional for debug only

  // Every var use that results in a function, so actually only these FunPtrs,
  // needs to make a "fresh" copy before unification.  "Fresh" makes a
  // structural copy of the TVar, keeping TVars from Nodes currently in-scope
  // as-is, and making structural copies of out-of-scope TVars.  The only
  // interesting thing is when an out-of-scope TVar uses the same TVar
  // internally in different parts - the copy replicates this structure.  When
  // unified, it forces equivalence in the same places.
  public  FunPtrNode( String name, RetNode ret, Node display ) {
    super(OP_FUNPTR,ret,display);
    _name = name;
  }
  // Explicitly, no display
  public  FunPtrNode( String name, RetNode ret ) { this(name,ret, Env.ANY ); }
  // Display (already fresh-loaded) but no name.
  public  FunPtrNode( RetNode ret, Node display ) { this(null,ret,display); }
  public RetNode ret() { return in(0)==null ? null : (RetNode)in(0); }
  public Node display(){ return in(1); }
  public FunNode fun() { return ret().fun(); }
  public FunNode xfun() { RetNode ret = ret(); return ret !=null && ret.in(4) instanceof FunNode ? ret.fun() : null; }
  int nargs() { return ret()._nargs; }
  int fidx() { return fun()._fidx; }
  String name() { return _name; } // Debug name, might be empty string
  // Formals from the function parms.
  // TODO: needs to come from both Combo and _t
  Type formal(int idx) { return ret().formal(idx); }

  // Self short name
  @Override public String xstr() {
    if( is_dead() || _defs._len==0 ) return "*fun";
    RetNode ret = ret();
    return ret==null ? "*fun" : "*"+_name;
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
    Node dsp = display();
    if( dsp!=Env.ANY ) {
      Type tdsp = dsp._val;
      FunNode fun;
      // Display is known dead?
      if( _live==Type.ANY ||
          // Collapsing to a gensym, no need for display
          ret().is_copy() ||
          // Also unused if function has no display parm.
          ((fun=xfun())!=null && fun.is_copy(0)==null && fun.parm(DSP_IDX)==null)  )
        return set_def(1,Env.ANY); // No display needed
    }
    return null;
  }
  // Called if Display goes unused
  @Override public void add_flow_use_extra(Node chg) {
    Type tdsp = display()._val;
    if( tdsp instanceof TypeMemPtr tmp && tmp._obj==TypeStruct.UNUSED )
      Env.GVN.add_reduce(this);
  }


  @Override public Type value() {
    if( !(in(0) instanceof RetNode) )
      return TypeFunPtr.EMPTY;
    RetNode ret = ret();
    TypeTuple tret = (TypeTuple)(ret._val instanceof TypeTuple ? ret._val : ret._val.oob(TypeTuple.RET));
    return TypeFunPtr.make(ret._fidx,nargs(),display()._val,tret.at(REZ_IDX));
  }
  @Override public void add_flow_extra(Type old) {
    //if( old==_live )            // live impacts value
    //  Env.GVN.add_flow(this);
    //if( _live==Type.ANY && display() != Env.ANY )
    //  Env.GVN.add_reduce(this);
    //if( old instanceof TypeFunPtr )
    //  for( Node use : _uses )
    //    if( use instanceof UnresolvedNode )
    //      for( Node call : use._uses )
    //        if( call instanceof CallNode ) {
    //          TypeFunPtr tfp = CallNode.ttfp(call._val);
    //          if( tfp.fidxs()==((TypeFunPtr)old).fidxs() )
    //            Env.GVN.add_flow(call);
    //        }
  }

  @Override public Type live_use(Node def ) {
    if( _live==Type.ALL ) return Type.ALL;
    // Else must be a TS with no-display.  Display is dead, but the rest of the
    // function is alive.
    return def==display() ? Type.ANY : Type.ALL;
  }

  // Implements class HM.Lambda unification.
  @Override public boolean unify( boolean test ) {
    TV2 self = tvar();
    if( self.is_err() ) return false;
    RetNode ret = ret();
    if( ret.is_copy() ) return false; // GENSYM
    FunNode fun = ret.fun();
    int nargs = fun.nargs();

    boolean progress = false;
    if( !self.is_fun() ) {      // Force a function if not already
      if( test ) return true;
      TV2[] tv2s = new TV2[nargs];
      for( Node use : fun._uses )
        if( use instanceof ParmNode parm && parm.has_tvar() )
          tv2s[parm._idx] = parm.tvar();
      assert tv2s[0]==null;
      tv2s[0] = ret.rez().tvar(); // Return in slot 0
      progress = self.unify(TV2.make_fun("FunPtr_unify",tv2s),test);
      self = self.find();
      assert self.is_fun();
    }

    // Each normal argument from the parms directly
    Node[] parms = fun.parms();  assert parms.length==nargs;
    for( int i=DSP_IDX; i<nargs; i++ )
      if( parms[i]!=null ) {
        if( self.arg(TV2.argname(i)).unify(parms[i].tvar(), test) ) {
          if( test ) return true;
          progress = true;
          self = self.find();
        }
      }
    progress |= self.arg(" ret").unify(ret.rez().tvar(),test);

    // FunPtr also does Apply unification, for JUST the display argument.
    if( display().has_tvar() )
      progress |= self.arg("2").unify(display().tvar(),test);

    return progress;
  }
}
