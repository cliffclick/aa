package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeObj;
import com.cliffc.aa.util.IBitSet;

// Merge results; extended by ParmNode
public class PhiNode extends Node {
  final Parse _badgc;
  final Type _t;
  private PhiNode( byte op, Type t, Parse badgc, Node... vals ) {
    super(op,vals);
    if( t instanceof TypeMem ) _t = TypeMem.ALLMEM;
    else if( t instanceof TypeObj ) _t = TypeObj.OBJ; // Need to check liveness
    else { assert t.isa(Type.SCALAR); _t = Type.SCALAR; }
    _badgc = badgc;
    _live = _t==Type.SCALAR ? TypeMem.ESCAPE : TypeMem.ALLMEM;
  }
  public PhiNode( Type t, Parse badgc, Node... vals ) { this(OP_PHI,t,badgc,vals); }
  // For ParmNodes
  PhiNode( byte op, Node fun, Type tdef, Node defalt, Parse badgc ) { this(op,tdef,badgc, fun,defalt); }
  @Override boolean is_mem() { return _t==TypeMem.ALLMEM; }
  @Override public int hashCode() { return super.hashCode()+_t.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof PhiNode) ) return false;
    PhiNode phi = (PhiNode)o;
    return _t==phi._t;
  }

  @Override public Node ideal(GVNGCM gvn, int level) {
    if( gvn.type(in(0)) == Type.XCTRL ) return null;
    RegionNode r = (RegionNode) in(0);
    assert r._defs._len==_defs._len;
    if( gvn.type(r) == Type.XCTRL ) return null; // All dead, c-prop will fold up
    if( r._defs.len() > 1 &&  r.in(1) == Env.ALL_CTRL ) return null;
    if( r instanceof FunNode && ((FunNode)r).noinline() )
      return null; // Do not start peeling apart parameters to a no-inline function
    // If only 1 unique live input, return that
    Node live=null;
    for( int i=1; i<_defs._len; i++ ) {
      if( gvn.type(r.in(i))==Type.XCTRL ) continue; // Ignore dead path
      Node n = in(i);
      if( n==this || n==live ) continue; // Ignore self or duplicates
      if( live==null ) live = n;         // Found unique live input
      else live=this;                    // Found 2nd live input, no collapse
    }
    if( live != this ) return live; // Single unique input

    return null;
  }

  @Override public Type value(GVNGCM gvn) {
    Type ctl = gvn.type(in(0));
    if( ctl != Type.CTRL ) return ctl.oob();
    RegionNode r = (RegionNode) in(0);
    assert r._defs._len==_defs._len;
    Type t = Type.ANY;
    for( int i=1; i<_defs._len; i++ )
      if( gvn.type(r.in(i))==Type.CTRL ) // Only meet alive paths
        t = t.meet(gvn.type(in(i)));
    if( _t.isa(t) ) return _t;
    return t;
  }
  @Override IBitSet escapees(GVNGCM gvn) { return IBitSet.FULL; }
  @Override public boolean basic_liveness() { return _t==Type.SCALAR; }
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) {
    if( def==in(0) ) return TypeMem.ALIVE;
    return basic_liveness() && !def.basic_liveness() ? TypeMem.ANYMEM : _live;
  }

  @Override public String err(GVNGCM gvn) {
    if( !(in(0) instanceof FunNode && ((FunNode)in(0))._name.equals("!") ) && // Specifically "!" takes a Scalar
        (gvn.type(this).contains(Type.SCALAR) ||
         gvn.type(this).contains(Type.NSCALR)) ) // Cannot have code that deals with unknown-GC-state
      return _badgc.errMsg("Cannot mix GC and non-GC types");
    return null;
  }
}
