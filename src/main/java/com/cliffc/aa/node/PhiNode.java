package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

// Merge results; extended by ParmNode
public class PhiNode extends Node {
  final Parse _badgc;
  final Type _t;                // Just a flag to signify scalar vs memory vs object
  private PhiNode( byte op, Type t, Parse badgc, Node... vals ) {
    super(op,vals);
    if( t instanceof TypeMem ) _t = TypeMem.ALLMEM;
    else if( t instanceof TypeObj ) _t = TypeObj.OBJ; // Need to check liveness
    else if( t instanceof TypeTuple ) _t = Type.SCALAR;
    else { _t = Type.SCALAR; }
    _badgc = badgc;
    _live = all_live();         // Recompute starting live after setting t
  }
  public PhiNode( Type t, Parse badgc, Node... vals ) { this(OP_PHI,t,badgc,vals); }
  // For ParmNodes
  PhiNode( byte op, Node fun, Type tdef, Node defalt, Parse badgc ) { this(op,tdef,badgc, fun,defalt); }
  @Override public boolean is_mem() { return _t==TypeMem.ALLMEM; }
  @Override public int hashCode() { return super.hashCode()+_t.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof PhiNode) ) return false;
    PhiNode phi = (PhiNode)o;
    return _t==phi._t;
  }

  @Override public Node ideal(GVNGCM gvn, int level) {
    if( val(0) == Type.XCTRL ) return null;
    RegionNode r = (RegionNode) in(0);
    assert r._defs._len==_defs._len;
    if( r.val() == Type.XCTRL ) return null; // All dead, c-prop will fold up
    if( r._defs.len() > 1 &&  r.in(1) == Env.ALL_CTRL ) return null;
    if( r instanceof FunNode && ((FunNode)r).noinline() )
      return null; // Do not start peeling apart parameters to a no-inline function
    // If only 1 unique live input, return that
    Node live=null;
    for( int i=1; i<_defs._len; i++ ) {
      if( r.val(i)==Type.XCTRL ) continue; // Ignore dead path
      Node n = in(i);
      if( n==this || n==live ) continue; // Ignore self or duplicates
      if( live==null ) live = n;         // Found unique live input
      else live=this;                    // Found 2nd live input, no collapse
    }
    if( live != this ) return live; // Single unique input

    return null;
  }

  @Override public Type value(GVNGCM.Mode opt_mode) {
    Type ctl = val(0);
    if( ctl != Type.CTRL ) return ctl.oob();
    RegionNode r = (RegionNode) in(0);
    assert r._defs._len==_defs._len;
    if( r instanceof LoopNode &&
        r.val(1)!=Type.XCTRL && r.val(1)!=Type.ANY &&
        r.val(2)!=Type.XCTRL && r.val(2)!=Type.ANY )
      return val(1).meet_loop(val(2)); // Optimize for backedges: no final-field updates.
    Type t = Type.ANY;
    for( int i=1; i<_defs._len; i++ )
      if( r.val(i)!=Type.XCTRL && r.val(i)!=Type.ANY ) // Only meet alive paths
        t = t.meet(val(i));
    return t;
  }
  @Override BitsAlias escapees() { return BitsAlias.FULL; }
  @Override public TypeMem all_live() {
    return _t==Type.SCALAR ? TypeMem.LIVE_BOT : TypeMem.ALLMEM;
  }
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    if( def==in(0) ) return TypeMem.ALIVE;
    return all_live().basic_live() && !def.all_live().basic_live() ? TypeMem.ANYMEM : _live;
  }

  @Override public ErrMsg err( boolean fast ) {
    if( !(in(0) instanceof FunNode && ((FunNode)in(0))._name.equals("!") ) && // Specifically "!" takes a Scalar
        (val() !=null &&
         (val().contains(Type.SCALAR) ||
          val().contains(Type.NSCALR))) ) // Cannot have code that deals with unknown-GC-state
      return ErrMsg.badGC(_badgc);
    return null;
  }
}
