package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.tvar.*;
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

  @Override public Type value() {
    Type c = val(0);
    if( c != Type.CTRL ) return c.oob();
    Type t = val(1);

    // If the cast is in-error, we cannot lift.
    Node n1 = in(1);
    if( n1 instanceof FreshNode frs ) n1 = frs.id();
    // No-Op, should remove shortly
    if( n1._val instanceof TypeStruct )
      return n1._val;    
    if( !checked(in(0),n1) ) return t;
      // Pin t between cast
      //return t.meet(_t.dual()).join(_t);
    // Lift result.
    return _t.join(t);
  }

  @Override public Type live_use(Node def ) {
    return def==in(0) ? Type.ALL : _live;
  }

  @Override public Node ideal_reduce() {
    Node cc = in(0).is_copy(0);
    if( cc!=null ) return set_def(0,cc);
    // Cast is useless?  Remove same as a TypeNode
    Node ctrl = in(0), addr = in(1);
    Type c = ctrl._val, t = addr._val;
    // Cast when Load/Field from a int/flt?  This is an oper Load, pulls from
    // the CLZ and cannot be nil; remove.
    if( _t instanceof TypeMemPtr ) {
      if( t instanceof TypeInt ) return addr;
      if( t instanceof TypeFlt ) return addr;
      if( t instanceof TypeStruct ) return addr;
    }
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

  @Override public boolean has_tvar() { return true; }

  // Unifies the input to '(Nil ?:self)'
  @Override public boolean unify( boolean test ) {
    TV3 maynil = tvar(1); // arg in HM
    TV3 notnil = tvar();  // ret in HM

    // Cast-notnil vs Cast-other

    // If the maynil is already nil-checked, can be a nilable of a nilable.
    // If the cast is already satisfied, then no change
    if( maynil==notnil ) return false;

    // Never a nilable nor nil
    if( maynil instanceof TVStruct )
      return notnil.unify(maynil,test);

    if( maynil instanceof TVClz )
      // TODO: probably should be the CLZ RHS
      return notnil.unify(maynil,test);

    // Already an expanded nilable
    if( maynil instanceof TVNil tmaynil && tmaynil.not_nil() == notnil )
      return false;

    // Expand nilable to either base
    if( maynil instanceof TVBase maybase && notnil instanceof TVBase notbase ) {
      assert maybase._t == notbase._t.meet(TypeNil.XNIL);
      return false;
    }
    
    // Already an expanded nilable with ptr
    if( maynil instanceof TVPtr && notnil instanceof TVPtr )
    //  return maynil.arg("*").unify(notnil.arg("*"),test);
      // TODO: suspicious, thing this should be the default
      throw unimpl();

    // Can be nilable of nilable; fold the layer
    if( maynil instanceof TVNil && notnil instanceof TVNil )
      throw unimpl(); // return maynil.unify(notnil,work);

    // Stall, until notnil becomes a TVNilable or a TVStruct
    if( maynil instanceof TVLeaf ) {
      maynil.deps_add_deep(this);
      return false;
    }
    
    // Unify the maynil with a nilable version of notnil
    return maynil.unify(new TVNil(notnil),test);
  }

  @Override public @NotNull CastNode copy( boolean copy_edges) {
    @NotNull CastNode nnn = (CastNode)super.copy(copy_edges);
    Env.GVN.add_dom(nnn);
    return nnn;
  }

  @Override public ErrMsg err( boolean fast ) {
    if( val(0)==Type.XCTRL || val(1).isa(_t) ) return null;
    return fast ? ErrMsg.FAST : ErrMsg.typerr(null,val(1),_t);
  }
  
  private boolean checked( Node n, Node addr ) {
    // Cast up for a typed Parm; always apply
    //if( TypeNil.XNIL.isa(_t) ) return true;
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
