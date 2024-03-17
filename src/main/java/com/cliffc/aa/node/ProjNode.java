package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.type.*;
import com.cliffc.aa.tvar.TV3;

import static com.cliffc.aa.AA.MEM_IDX;

// Proj data
public class ProjNode extends Node {
  public int _idx;
  //public ProjNode( int idx, Node... ns ) { super(ns); _idx=idx; }
  public ProjNode( Node head, int idx ) { super(head); _idx=idx; }
  
  @Override public String label() { return "DProj"+_idx; }
  @Override public boolean isMultiTail() { return true; }

  @Override public Type value() {
    Type c = val(0);
    if( c instanceof TypeTuple ct && _idx < ct._ts.length )
      c = ct._ts[_idx];
    if( c!=Type.ANY && c!=Type.ALL ) return c;
    return c.oob(TypeNil.SCALAR);
  }
  
  // Strictly reducing
  @Override public Node ideal_reduce() {
    Node c = in(0).isCopy(_idx);
    if( c != null )
      return c==this ? Env.ANY : c; // Happens in dying loops
    return null;
  }

  // Standard data ProjNode has a type variable, Control does not
  @Override public boolean has_tvar() { return true; }

  // Unify with the parent TVar sub-part
  @Override public TV3 _set_tvar( ) {
    return in(0).unify_proj(this);
  }

  public static ProjNode proj( Node head, int idx ) {
    for( int i=0; i<head.nUses(); i++ )
      if( head.use(i) instanceof ProjNode proj && proj._idx==idx )
        return proj;
    return null;
  }

  void set_idx( int idx ) { unelock(); _idx=idx; } // Unlock before changing hash
  @Override int hash() { return _idx; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof ProjNode proj) ) return false;
    return _idx==proj._idx;
  }
}
