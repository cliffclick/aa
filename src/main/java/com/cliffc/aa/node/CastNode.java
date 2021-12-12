package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeTuple;
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
  
  @Override public TypeMem live_use(Node def ) {
    return def==in(0) ? TypeMem.ALIVE : _live;
  }

  // Unifies the input to '(Nil ?:self)'
  @Override public boolean unify( boolean test ) {
    TV2 maynil = tvar(1); // arg in HM
    TV2 notnil = tvar();  // ret in HM
    if( maynil.is_err() ) return false;

    // Can already be nil-checked and will then unify to self
    if( maynil==notnil ) throw unimpl(); // return false;

    // Already an expanded nilable
    if( maynil.is_nil() && maynil.get("?") == notnil ) return false;

    // Expand nilable to either base
    if( maynil.is_base() && notnil.is_base() )
      throw unimpl(); //

    // Two structs, one nilable.  Nilable is moved into the alias, but also
    // need to align the fields.
    if( maynil.is_struct() && notnil.is_struct() && maynil._type == maynil._type.meet_nil(Type.XNIL) ) {
      boolean progress = false;
      // Also check that the fields align
      for( String fld : maynil.args() ) {
        TV2 mfld = maynil.get(fld);
        TV2 nfld = notnil.get(fld);
        if( nfld!=null && nfld!=mfld )
          { progress = true; break; } // Unequal fields
      }
      // Find any extra fields
      if( !progress && maynil.open() )
        for( String fld : notnil.args() )
          if( maynil.get(fld) == null )
            { progress = true; break; }
      if( !progress ) return false; // No progress
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
