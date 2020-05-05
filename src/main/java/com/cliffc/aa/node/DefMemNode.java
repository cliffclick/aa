package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeObj;
import com.cliffc.aa.type.TypeTuple;

import java.util.BitSet;

public class DefMemNode extends Node {
  public static BitSet CAPTURED = new BitSet();

  public DefMemNode( Node obj) { super(OP_DEFMEM,Env.START,obj); }
  @Override public Node ideal(GVNGCM gvn, int level) { return null; }
  @Override public TypeMem value(GVNGCM gvn) {
    TypeObj[] tos = new TypeObj[_defs._len];
    for( int i=1; i<_defs._len; i++ ) {
      Node n = _defs.at(i);
      if( n==null ) continue;
      if( n instanceof OProjNode ) {
        if( n.in(0) instanceof NewNode )
          tos[i] = ((NewNode)n.in(0))._ts;
        else
          tos[i] = (TypeObj)((TypeTuple)gvn.type(n.in(0)))._ts[0];
      } else
        tos[i] = (TypeObj)gvn.type(n);
    }
    return TypeMem.make0(tos);
  }
  // Uses OProjs but never demands memory
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) { return def instanceof ConNode ? TypeMem.EMPTY : TypeMem.DEAD; }
  @Override public TypeMem all_type() { return TypeMem.MEM; }
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
  private static int PRIM_DEFS;
  public void init0() { PRIM_DEFS = _defs._len; }
  @Override public void reset_to_init1(GVNGCM gvn ) {
    gvn.unreg(this);
    while( _defs._len > PRIM_DEFS ) pop(gvn);
    CAPTURED.clear();
  }

}

