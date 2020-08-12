package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Proj memory
public class MrgProjNode extends ProjNode {
  public MrgProjNode( NewNode nnn, Node mem ) { super(0,nnn,mem); }
  @Override String xstr() { return "MrgProj"+_idx; }
  @Override public boolean is_mem() { return true; }
  NewNode nnn() { return (NewNode)in(0); }
  Node    mem() { return          in(1); }
  @Override public Node ideal(GVNGCM gvn, int level) {
    if( nnn().is_unused() ) {
      Type t = gvn.type(mem());
      if( t instanceof TypeMem && ((TypeMem)t).at(nnn()._alias)==TypeObj.UNUSED )
        return mem();
    }
    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    if( !(in(0) instanceof NewNode) ) return Type.ANY;
    NewNode nnn = nnn();
    Type tn = gvn.type(nnn);
    Type tm = gvn.type(mem());
    if( !(tn instanceof TypeTuple) ) return tn.oob();
    if( !(tm instanceof TypeMem  ) ) return tm.oob();
    TypeObj to = (TypeObj)((TypeTuple)tn).at(0);
    TypeMem tmem = (TypeMem)tm;
    return nnn.is_unused()
      ? tmem.set   (nnn._alias,TypeObj.UNUSED)
      : tmem.st_new(nnn._alias, to);
  }

  @Override BitsAlias escapees( GVNGCM gvn) { return in(0).escapees(gvn); }
  @Override public boolean basic_liveness() { return false; }
  // Only called here if alive, and input is more-than-basic-alive
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) { return def==in(0) ? TypeMem.ALIVE : _live; }
}
