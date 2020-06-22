package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeObj;

import java.util.BitSet;

public class DefMemNode extends Node {
  public static BitSet CAPTURED = new BitSet();

  public DefMemNode( Node ctrl, Node isuse) { super(OP_DEFMEM,ctrl,isuse); }
  @Override public Node ideal(GVNGCM gvn, int level) { return null; }
  @Override public TypeMem value(GVNGCM gvn) {
    TypeObj[] tos = new TypeObj[_defs._len];
    for( int i=1; i<_defs._len; i++ ) {
      Node n = _defs.at(i);
      if( n==null ) continue;
      if( n instanceof OProjNode ) {
        tos[i] = ((NewNode)n.in(0))._defmem;
      } else {
        Type tn = gvn.type(n);
        tos[i] = tn instanceof TypeObj ? (TypeObj)tn : tn.oob(TypeObj.ISUSED);
      }
    }
    return TypeMem.make0(tos);
  }
  @Override public boolean basic_liveness() { return false; }
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) { return _live; }
  @Override public boolean equals(Object o) { return this==o; } // Only one

  // Make an OProj for a New, and 'hook' it into the default memory
  public OProjNode make_mem_proj(GVNGCM gvn, NewNode nn) {
    OProjNode mem = (OProjNode)gvn.xform(new OProjNode(nn,0));
    return make_mem(gvn,nn,mem);
  }
  public OProjNode make_mem(GVNGCM gvn, NewNode nn, OProjNode mem) {
    TypeObj[] tos0 = TypeMem.MEM.alias2objs();
    while( _defs._len < tos0.length )
      gvn.add_def(this,gvn.con(TypeMem.MEM.at(_defs._len)));
    while( _defs._len <= nn._alias ) gvn.add_def(this,null);
    gvn.set_def_reg(this,nn._alias,mem);
    // Lift default immediately; default mem used by the Parser to load-thru displays.
    gvn.setype(this,value(gvn));
    gvn.add_work_uses(this);
    return mem;
  }
  // Between compilations
  public static void reset() { CAPTURED.clear(); }
}

