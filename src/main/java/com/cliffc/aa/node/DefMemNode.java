package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

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
      } else {
        Type tn = gvn.type(n);
        tos[i] = tn instanceof TypeObj ? (TypeObj)tn : (tn.above_center() ? TypeObj.XOBJ : TypeObj.OBJ);
      }
    }
    return TypeMem.make0(tos);
  }
  // Basic live only, never uses memory.  If this is all that keeps an OProj
  // alive, the NewNode will shortly declare captured.
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
  public static void reset() { CAPTURED.clear(); }

}

