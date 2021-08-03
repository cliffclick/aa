package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.Env.GVN;

public class DefMemNode extends Node {
  public DefMemNode( Node ctrl) { super(OP_DEFMEM,ctrl); }
  @Override public TypeMem value(GVNGCM.Mode opt_mode) {
    if( opt_mode._CG ) return TypeMem.ANYMEM;
    if( _defs._len <= 1 ) return TypeMem.ALLMEM;
    TypeObj[] tos = new TypeObj[_defs._len];
    for( int i=1; i<_defs._len; i++ ) {
      Node n = in(i);
      if( n==null ) continue;
      if( n instanceof MrgProjNode ) { // NewNode still alive
        NewNode nnn = n.in(0) instanceof NewNode ? (NewNode) n.in(0) : null;
        tos[i] = (nnn != null && nnn._val != Type.ANY && nnn._live != TypeMem.DEAD) ? nnn._crushed : TypeObj.UNUSED;
      } else if( n instanceof ConTypeNode ) {
        tos[i] = ((TypeMemPtr)n._val)._obj;
      } else {                  // Collapsed NewNode
        Type tn = n._val;
        if( tn instanceof TypeMem ) tn = ((TypeMem)tn).at(i);
        tos[i] = tn instanceof TypeObj ? (TypeObj)tn : tn.oob(TypeObj.ISUSED);
      }
    }
    return TypeMem.make0(tos);
  }
  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    if( opt_mode._CG ) return TypeMem.DEAD; // Have a Call-Graph, do not need DefMem
    if( def==in(0) ) return TypeMem.ALIVE;  // Control
    return _live;
  }

  //@Override public TV2 new_tvar(String alloc_site) { return TV2.make("Mem",this,alloc_site); }
  //
  //@Override public boolean unify( boolean test ) {
  //  // Self should always should be a TMem
  //  TV2 tvar = tvar();
  //  assert tvar.isa("Mem");
  //  // Structural unification on all objects
  //  boolean progress=false;
  //  for( int i=1; i<_defs._len; i++ ) {
  //    Node n = in(i);
  //    if( n==null ) continue;
  //    TV2 tv = (n instanceof MrgProjNode && !tvar(i).is_dead() ? n.in(0) : n).tvar();
  //    progress |= tvar.unify_at(i,tv,test);
  //    if( progress && test ) return true;
  //  }
  //  return progress;
  //}


  @Override public boolean equals(Object o) { return this==o; } // Only one

  // Make an MProj for a New, and 'hook' it into the default memory
  public MrgProjNode make_mem_proj(NewNode nn, Node mem) {
    MrgProjNode mrg = (MrgProjNode)GVN.xform(new MrgProjNode(nn,mem));
    return make_mem(nn._alias,mrg);
  }
  public <N extends Node> N make_mem(int alias, N obj) {
    TypeObj[] tos0 = TypeMem.MEM.alias2objs();
    while( _defs._len < tos0.length )
      add_def(Node.con(TypeMem.MEM.at(_defs._len)));
    while( _defs._len <= alias ) this.add_def(null);
    set_def(alias,obj);
    // Lift default immediately; default mem used by the Parser to load-thru displays.
    do_flow();
    return obj;
  }
}
