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
    if( n1 instanceof FreshNode ) n1 = ((FreshNode)n1).id();
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

    // Two structs, one nilable.  Nilable is moved into the alias, but also
    // need to align the fields.
    if( maynil.is_obj() && notnil.is_obj() ) {
      boolean progress = false;
      Type omt = maynil._flow;
      Type ont = notnil._flow;
      Type mt = omt.meet(ont);
      Type mt0 = mt.meet(TypeNil.NIL);
      Type nt0 = mt.join(TypeNil.NSCALR);
      if( mt0!=omt ) { maynil._flow = mt0; progress=true; }
      if( nt0!=ont ) { notnil._flow = nt0; progress=true; }

      Type ome = maynil._eflow;
      Type one = notnil._eflow;
      Type mte = ome==null ? one : (one==null ? ome : ome.meet(one));
      if( mte!=null ) {
        Type mt1 = mte.meet(TypeNil.NIL);
        Type nt1 = mte.join(TypeNil.NSCALR);
        if( mt1 != ome ) { maynil._eflow = mt1; progress = true; }
        if( nt1 != one ) { notnil._eflow = nt1; progress = true; }
      }
      // Also check that the fields align
      //return TV2.unify_flds(maynil,notnil,test) | progress;
      throw unimpl();           // TODO: top-level distinction removed, 
    }

    // All other paths may progress
    if( test ) return true;

    // Can be nilable of nilable; fold the layer
    if( maynil.is_nil() && notnil.is_nil() )
      throw unimpl(); // return maynil.unify(notnil,work);

    // Unify the maynil with a nilable version of notnil
    return TV2.make_nil(notnil,"Cast_unify").find().unify(maynil,test);
  }

  @Override public @NotNull CastNode copy( boolean copy_edges) {
    @NotNull CastNode nnn = (CastNode)super.copy(copy_edges);
    Env.GVN.add_dom(nnn);
    return nnn;
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
