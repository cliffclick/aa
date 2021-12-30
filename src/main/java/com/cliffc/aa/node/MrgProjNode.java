package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.MEM_IDX;

// Proj memory
public class MrgProjNode extends ProjNode {
  public MrgProjNode( NewNode nnn, Node mem ) { super(MEM_IDX,nnn,mem); }
  @Override public String xstr() { return "MrgProj"+_idx; }
  @Override public boolean is_mem() { return true; }
  public NewNode nnn() { return (NewNode)in(0); }
  public Node mem() { return in(1); }


  @Override public Node ideal_reduce() {
    if( !is_prim() && val(0).above_center() )
      return mem();
    NewNode nnn = nnn();
    Node mem = mem();
    // Alias is dead-on-entry.  Then this MrgPrj no longer lifts
    //Type t = mem._val;
    if( nnn.is_unused() || nnn.len()==1 ) // New is dead for no pointers
      return mem;                // Kill MrgNode when it no longer lifts values

    // New is dead from below.
    if( _live.at(nnn._alias)==TypeObj.UNUSED && !nnn.is_unused() ) {
      nnn.kill2();      // Killing a NewNode has to do more updates than normal
      return this;
    }

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
      BitsAlias escs1 = escapees();
      if( MemSplitNode.check_split(this,escs1,mem) )
        return MemSplitNode.insert_split(this,escs1,this,head2,mem);
    }
    return null;
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
  @Override public Type value() {
    if( !(in(0) instanceof NewNode) ) return mem()._val;
    NewNode nnn = nnn();
    Type tn = nnn._val;
    Type tm = mem()._val;
    if( !(tm instanceof TypeMem tmem) ) return tm.oob();
    if( !(tn instanceof TypeTuple tt) ) return tn.oob();
    TypeObj to = (TypeObj)tt.at(MEM_IDX);
    return nnn.is_unused()      // This is a cycle-breaking lifting value
      ? tmem.set   (nnn._alias,tmem.at(nnn._alias))
      : tmem.st_new(nnn._alias, to);
  }

  @Override BitsAlias escapees() { return in(0).escapees(); }
  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
  // Only called here if alive, and input is more-than-basic-alive
  @Override public TypeMem live_use(Node def ) {
    if( def==in(0) && in(0) instanceof NewNode && _live.at(nnn()._alias).above_center() )
      return TypeMem.DEAD;
    return _live;
  }

  @Override public TV2 new_tvar( String alloc_site) { return null; }
}
