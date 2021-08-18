package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeTuple;
import org.jetbrains.annotations.NotNull;

// Gain precision after an If-test.
public class CastNode extends Node {
  public final Type _t;                // TypeVar???
  public CastNode( Node ctrl, Node ret, Type t ) {
    super(OP_CAST,ctrl,ret); _t=t;
    Env.GVN._work_dom.add(this);
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

  @Override public Type value(GVNGCM.Mode opt_mode) {
    Type c = val(0);
    if( c != Type.CTRL ) return c.oob();
    Type t = val(1);
    if( t.is_forward_ref() ) return Type.SCALAR;

    // If the cast is in-error, we cannot lift.
    Node n1 = in(1);
    if( n1 instanceof FreshNode ) n1 = ((FreshNode)n1).id();
    if( !checked(in(0),n1) ) return t;
    // Lift result.
    return _t.join(t);
  }
  @Override public void add_work_extra(Work work, Type old) {
    // If address sharpens, Cast can go dead because all Load uses make constants.
    if( _val!=old )
      work.add(this);
  }
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    return def==in(0) ? TypeMem.ALIVE : _live;
  }

  @Override public boolean unify( Work work ) { return tvar(1).unify(tvar(), work); }

  @Override public @NotNull CastNode copy( boolean copy_edges) {
    CastNode nnn = (CastNode)super.copy(copy_edges);
    return Env.GVN._work_dom.add(nnn);
  }

  private static boolean checked( Node n, Node addr ) {
    if( !(n instanceof CProjNode && ((CProjNode)n)._idx==1) ) return false; // Not a Cast of a CProj-True
    Node n0 = n.in(0);
    if( n0 instanceof IfNode ) {
      Node na = n0.in(1);
      if( na instanceof FreshNode ) na = ((FreshNode)na).id();
      if( na == addr ) return true; // Guarded by If-n-zero
    }
    if( n0 instanceof ConNode && ((TypeTuple) n0._val).at(1)==Type.XCTRL )
      return true;
    return false;
  }
}
