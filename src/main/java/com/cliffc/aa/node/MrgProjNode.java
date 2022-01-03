package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeStruct;

import static com.cliffc.aa.AA.MEM_IDX;
import static com.cliffc.aa.AA.unimpl;

// Not really a ProjNode; merges memory from a NewNode into the main memory.
public class MrgProjNode extends ProjNode {
  public MrgProjNode( NewNode nnn, Node mem ) { super(MEM_IDX,nnn,mem); }
  @Override public String xstr() { return "MrgProj"+_idx; }
  @Override public boolean is_mem() { return true; }
  public NewNode nnn() { return (NewNode)in(0); }
  public Node mem() { return in(1); }


  @Override public Type value() {
    Type tm = mem()._val;
    if( !(in(0) instanceof NewNode nnn) ) return tm;
    if( !(tm instanceof TypeMem tmem) ) return tm.oob();
    // Get the value at the alias slice from nnn
    TypeStruct ts = nnn.valueobj();
    return tmem.make_from(nnn._alias,ts);
  }

  //@Override BitsAlias escapees() { return in(0).escapees(); }
  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
  // Only called here if alive, and input is more-than-basic-alive
  @Override public TypeMem live_use(Node def ) {
    if( def==in(0) && in(0) instanceof NewNode && _live.at(nnn()._alias).above_center() )
      return TypeMem.DEAD;
    return _live;
  }

  @Override public void add_flow_def_extra(Node chg) {
    for( Node use : _uses ) {          // Lost a use, could be a 2nd mem writer
      if( use instanceof MrgProjNode ) // Look for back-to-back MrgProj
        Env.GVN.add_grow(use);
      if( use instanceof StoreNode )   // Look for a Store folding into a New
        Env.GVN.add_reduce(use);
      if( use instanceof MemSplitNode ) { //
        MemJoinNode jn = ((MemSplitNode)use).join();
        if( jn!=null ) Env.GVN.add_reduce(jn);
      }
      if( use instanceof CallNode )
        Env.GVN.add_grow(use); // Swap Call & New
    }
  }

  @Override public TV2 new_tvar( String alloc_site) { return null; }

  @Override public Node ideal_reduce() {
    if( !is_prim() && val(0).above_center() )
      return mem();
    NewNode nnn = nnn();
    Node mem = mem();
    // New is dead from below, or no pointers.
    if( _live.at(nnn._alias)== TypeStruct.UNUSED || nnn.len()==1 ) // New is dead for no pointers
      // Kill MrgNode when it no longer lifts values relative to the default mem
      return ((TypeMem)mem._val).at(nnn._alias) ==TypeStruct.UNUSED ? mem : null;

    // If is of a MemJoin, and it can enter the split region, do so.
    if( mem instanceof MemJoinNode && mem._uses._len==1 ) {
      MrgProjNode mprj = new MrgProjNode(nnn,mem);
      MemJoinNode mjn = ((MemJoinNode)mem).add_alias_below_new(mprj,this);
      return mjn;
    }

    return null;
  }

  @Override public Node ideal_mono() { return null; }

  @Override public Node ideal_grow() {
    Node mem = mem();
    // Look for back-to-back unrelated aliases and Split/Join
    Node head2 = MemJoinNode.find_sese_head(mem);
    if( head2 != null && !head2.is_prim() ) {
      //BitsAlias escs1 = escapees();
      //if( MemSplitNode.check_split(this,escs1,mem) )
      //  return MemSplitNode.insert_split(this,escs1,this,head2,mem);
      throw unimpl();
    }
    return null;
  }

}
