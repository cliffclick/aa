package com.cliffc.aa.node;

import com.cliffc.aa.*;

// Merge results
public class RegionNode extends Node {
  int _cidx; // Copy index; monotonic change from zero to Control input this Region is collapsing to
  public RegionNode( Node... ctrls) { super(OP_REGION,ctrls); }
  RegionNode( byte op ) { super(op); add_def(null); } // For FunNodes
  @Override public Node ideal(GVNGCM gvn) { return ideal(gvn,false); }
  // Ideal call, but FunNodes keep index#1 for future parsed call sites
  Node ideal(GVNGCM gvn, boolean more) {
    if( _cidx !=0 ) return null; // Already found single control path
    // TODO: The unzip xform, especially for funnodes doing type-specialization
    // TODO: Check for dead-diamond merges
    // TODO: treat _cidx like U/F and skip_dead it also

    // Find 0, 1 or many live paths
    int live=0, dead=0;
    for( int i=1; i<_defs._len; i++ )
      if( gvn.type(at(i))==Type.XCTRL )
        dead++;                  // Count dead paths
      else                       // Found a live path
        if( live == 0 ) live = i;// Remember live path
        else live = -1;          // Found many live paths
    if( live==0 ) return null;   // Nothing live?  Let value() handle it

    if( !more && live > 0 ) {   // Exactly one and no more?
      // Note: we do not return the 1 alive control path, as then trailing
      // PhiNodes will subsume that control - instead they each need to
      // collapse to their one alive input in their own ideal() calls - and
      // they will be using the _cidx to make their decisions.
      _cidx=live;               // Flag the 1 live path
      return this;              // Return self
    }
    if( dead==0 ) return null;  // No dead paths

    // Do a parallel bulk reshape: remove the dead edges from Phis and the
    // Region all at once
    for( Node phi : _uses )
      if( phi instanceof PhiNode )
        for( int i=1,j=1; i<_defs._len; i++ )
          if( gvn.type(at(i))==Type.XCTRL ) { gvn.unreg(phi); phi.remove(j,gvn); gvn.rereg(phi); }
          else j++;
    for( int i=1; i<_defs._len; i++ ) if( gvn.type(at(i))==Type.XCTRL ) remove(i--,gvn);
    return this;
  }

  @Override public Type value(GVNGCM gvn) {
    Type t = Type.XCTRL;
    for( int i=1; i<_defs._len; i++ )
      t = t.meet(gvn.type(_defs._es[i]));
    return t;
  }
  @Override public Node is_copy(GVNGCM gvn, int idx) { assert idx==-1; return _cidx == 0 ? null : at(_cidx); }
  @Override public Type all_type() { return Type.CTRL; }
}
