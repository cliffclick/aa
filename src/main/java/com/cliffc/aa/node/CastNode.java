package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;
import org.jetbrains.annotations.NotNull;

import static com.cliffc.aa.AA.unimpl;

// Gain precision after an If-test.
public class CastNode extends Node {
  public final Type _t;
  public CastNode( Node ctrl, Node ret, Type t ) {
    super(OP_CAST,ctrl,ret); _t=t;
    Env.GVN.add_dom(this);
  }
  @Override public String xstr() { return "("+_t+")"; }

  @Override public Node ideal_reduce() {
    Node cc = in(0).is_copy(0);
    if( cc!=null ) return set_def(0,cc);
    // Cast is useless?  Remove same as a TypeNode
    Node ctrl = in(0), addr = in(1);
    Type c = ctrl._val, t = addr._val;
    if( c != Type.CTRL ) return null;
    if( t.isa(_t) ) return in(1);
    return null;
  }

  @Override public Node ideal_mono() {
    // Can we hoist control to a higher test?
    Node ctrl = in(0);
    Node baseaddr = in(1);
    while( baseaddr instanceof CastNode ) baseaddr = baseaddr.in(1);
    while( baseaddr instanceof FreshNode ) baseaddr = ((FreshNode)baseaddr).id();
    final Node fbaseaddr = baseaddr;

    Node tru = ctrl.walk_dom_last(n -> checked(n,fbaseaddr));
    if( tru==null || tru==ctrl ) return null;
    set_def(0,tru);
    return this;
  }

  @Override public Type value() {
    Type c = val(0);
    if( c != Type.CTRL ) return c.oob();
    Type t = val(1);

    // If the cast is in-error, we cannot lift.
    Node n1 = in(1);
    if( n1 instanceof FreshNode frs ) n1 = frs.id();
    if( !checked(in(0),n1) ) return t;
    // Lift result.
    return _t.join(t);
  }
  @Override public void add_flow_extra(Type old) {
    // If address sharpens, Cast can go dead because all Load uses make constants.
    if( _val!=old )
      Env.GVN.add_flow(this);
  }

  @Override public Type live_use(Node def ) {
    return def==in(0) ? Type.ALL : _live;
  }

  @Override public boolean has_tvar() { return true; }

  // Unifies the input to '(Nil ?:self)'
  @Override public boolean unify( boolean test ) {
    TV2 maynil = tvar(1); // arg in HM
    TV2 notnil = tvar();  // ret in HM

    // If this is a type-cast, and not a not-nil cast
    // just do a normal base unification.
    if( TypeNil.XNIL.isa(_t) ) {
      boolean progress = notnil.unify(maynil,test);
      TV2 tv2 = notnil.find();
      if( tv2.is_base() && tv2._tflow ==_t )
        return progress;
      return test || tv2.unify(TV2.make_base(_t,"Cast_unify"),test);
    }


    // If the maynil is already nil-checked, can be a nilable of a nilable.
    if( maynil==notnil ) throw unimpl(); // return false;

    // Already an expanded nilable
    if( maynil.is_nil() && maynil.arg("?") == notnil ) return false;

    // Expand nilable to either base
    if( maynil.is_base() && notnil.is_base() )
      //assert !arg.is_open() && !ret.is_open();
      //assert arg._flow == ret._flow.meet(Type.NIL);
      //return false;
      throw unimpl(); //

    // Already an expanded nilable with ptr
    if( maynil.is_ptr() && notnil.is_ptr() )
      return maynil.arg("*").unify(notnil.arg("*"),test);

    // All other paths may progress
    if( test ) return true;

    // Can be nilable of nilable; fold the layer
    if( maynil.is_nil() && notnil.is_nil() )
      throw unimpl(); // return maynil.unify(notnil,work);

    // Unify the maynil with a nilable version of notnil
    return TV2.make_nil(notnil,"Cast_unify").find().unify(maynil,test);
  }

  @Override public void add_work_hm() {
    Env.GVN.add_flow(in(1));
    Env.GVN.add_flow_uses(this);
  }

  @Override public @NotNull CastNode copy( boolean copy_edges) {
    @NotNull CastNode nnn = (CastNode)super.copy(copy_edges);
    Env.GVN.add_dom(nnn);
    return nnn;
  }

  private boolean checked( Node n, Node addr ) {
    // Cast up for a typed Parm; always apply
    if( TypeNil.XNIL.isa(_t) ) return true;
    // Cast-away-nil at a IfNode
    if( !(n instanceof CProjNode cpj && cpj._idx==1) ) return false; // Not a Cast of a CProj-True
    Node n0 = n.in(0);
    if( n0 instanceof IfNode ) {
      Node na = n0.in(1);
      if( na instanceof FreshNode frs ) na = frs.id();
      if( na == addr ) return true; // Guarded by If-n-zero
    }
    if( n0 instanceof ConNode && ((TypeTuple) n0._val).at(1)==Type.XCTRL )
      return true;
    return false;
  }
}
