package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeTuple;
import com.cliffc.aa.type.TypeFunPtr;

// Assert the matching type.  Parse-time error if it does not remove.  Note the
// difference with CastNode: both Nodes always join their input with their
// constant but a TypeNode has to be proven useless and removed before the
// program is type-correct.  A CastNode is always correct from call/return
// semantics, but the join is not-locally-obviously-correct.  The Cast makes it
// locally obvious.
public class TypeNode extends Node {
  final Type _t;                // TypeVar???
  final Parse _error_parse;     // Used for error messages
  public TypeNode( Type t, Node c, Node n, Parse P ) { super(OP_TYPE,c,n); _t=t; _error_parse = P; }
  @Override String xstr() { return ":"+_t; }
  @Override public Node ideal(GVNGCM gvn) {
    Node ctl = in(0);
    Node arg = in(1);
    Type t = gvn.type(arg);
    if( t.isa(_t) )
      return ctl; // No conflict, remove TypeNode
    // Push TypeNodes 'up' to widen the space they apply to, and hopefully push
    // the type check closer to the source of a conflict.
    if( arg instanceof PhiNode && arg.in(0)==ctl &&
        // Not allowed to push up the typing on the unknown arg... because
        // unknown new callers also need the check.
        (!(ctl instanceof FunNode) || !((FunNode)ctl).has_unknown_callers()) ) {
      assert ctl instanceof RegionNode;
      for( int i=1; i<arg._defs._len; i++ )
        gvn.set_def_reg(ctl,i,gvn.xform(new TypeNode(_t,ctl.in(i),arg.in(i),_error_parse)));
      return ctl;               // Remove TypeNode, since completely replaced
    }
    // Push TypeNode 'up' into functions, so all the args get checked.
    // Rewrites: "fun:(int->int) = (x -> x*2)"
    // into    : "fun = (x:int -> (x*2):int)"
    if( _t instanceof TypeFunPtr && arg instanceof EpilogNode ) {
      TypeFunPtr tfp = (TypeFunPtr)_t;
      EpilogNode epi = (EpilogNode)arg;
      FunNode fun = epi.fun();
      assert tfp._args._ts.length == fun._tf._args._ts.length;

      // Find control exit from Fun
      Node fctl = null;
      if( epi.ctl()==fun ) fctl = epi;
      else {
        for( Node n : fun._uses ) {
          Type all = n.all_type();
          if( all==Type.CTRL || (all instanceof TypeTuple && ((TypeTuple)all).at(0)==Type.CTRL) ) {
            assert n.in(0)==fun;
            assert fctl==null;
            fctl = n;
          }
        }
      }

      // Typecheck all args
      for( int i=0; i<tfp._args._ts.length; i++ ) {
        Node p = fun.parm(i);
        if( p == null ) {
          p = new ParmNode(i,"arg"+i,fun,gvn.con(Type.SCALAR),"dead");
          while( p._defs._len < fun._defs._len )
            p.add_def(gvn.con(Type.SCALAR));
          p = gvn.xform(p);
        }
        Node tchk = gvn.xform(new TypeNode(tfp._args._ts[i],fun,p,_error_parse));
        gvn.set_def_reg(fctl,0,tchk);
        fctl = tchk;
      }

      // Type-check return value
      gvn.set_def_reg(epi,0,gvn.xform(new TypeNode(tfp._ret,epi.ctl(),epi.val(),_error_parse)));
      return ctl;               // Collapse away
    }

    return null;
  }
  @Override public Type value(GVNGCM gvn) { return Type.CTRL; }
  @Override public Type all_type() { return Type.CTRL; }
  // Check TypeNode for being in-error
  @Override public String err(GVNGCM gvn) {
    return _error_parse.typerr(gvn.type(in(1)),_t);
  }
}
