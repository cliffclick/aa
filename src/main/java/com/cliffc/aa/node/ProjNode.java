package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.MEM_IDX;

// Proj data
public class ProjNode extends Node {
  public int _idx;
  public ProjNode( Node head, int idx ) { this(OP_PROJ,head,idx); }
  public ProjNode( int idx, Node... ns ) { super(OP_PROJ,ns); _idx=idx; }
  ProjNode( byte op, Node ifn, int idx ) {
    super(op,ifn);
    _idx=idx;
  }
  @Override public String xstr() { return "DProj"+_idx; }

  @Override public Type value() {
    Type c = val(0);
    if( c instanceof TypeTuple ct && _idx < ct._ts.length )
      c = ct._ts[_idx];
    if( c!=Type.ANY && c!=Type.ALL ) return c;
    return c.oob(TypeNil.SCALAR);
  }
  @Override Type live_use( int i ) { return i==MEM_IDX ? TypeMem.ANYMEM : _live; }
  
  // Strictly reducing
  @Override public Node ideal_reduce() {
    Node c = in(0).is_copy(_idx);
    if( c != null )
      return c==this ? Env.ANY : c; // Happens in dying loops
    return null;
  }

  // Standard data ProjNode has a type variable, Control does not
  @Override public boolean has_tvar() { return true; }

  // Unify with the parent TVar sub-part
  @Override public boolean unify( boolean test ) {
    return has_tvar() && in(0).unify_proj(this,test);
  }

  public static ProjNode proj( Node head, int idx ) {
    for( Node use : head._uses )
      if( use instanceof ProjNode proj && proj._idx==idx )
        return proj;
    return null;
  }

  void set_idx( int idx ) { unelock(); _idx=idx; } // Unlock before changing hash
  @Override public int hashCode() { return super.hashCode()+_idx; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof ProjNode proj) ) return false;
    return _idx==proj._idx;
  }
}
