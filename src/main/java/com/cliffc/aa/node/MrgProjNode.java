package com.cliffc.aa.node;

import com.cliffc.aa.Env;
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
    NewNode nnn = nnn();
    Node mem = mem();
    Type t = mem.val();
    // Alias is dead-on-entry.  Then this MrgPrj no longer lifts
    boolean doe = t instanceof TypeMem && ((TypeMem)t).at(nnn._alias)==TypeObj.UNUSED;

    if( doe && nnn.is_unused() ) // New is dead for no pointers
      return mem;                // Kill MrgNode when it no longer lifts values

    // New is dead from below.
    if( _live.at(nnn._alias)==TypeObj.UNUSED && nnn._keep==0 && !nnn.is_unused() && !is_prim() ) {
      gvn.unreg(nnn);   // Unregister before self-kill
      nnn.kill(gvn);    // Killing a NewNode has to do more updates than normal
      return this;
    }

    // Look for back-to-back unrelated aliases and Split/Join
    Node head2 = MemJoinNode.find_sese_head(mem);
    if( head2 != null && !head2.is_prim() ) {
      BitsAlias escs1 = escapees();
      if( MemSplitNode.check_split(this,escs1) )
        return MemSplitNode.insert_split(gvn,this,escs1,this,head2,mem);
    }

    // If is of a MemJoin and it can enter the split region, do so.
    if( _keep==0 && mem instanceof MemJoinNode && mem._uses._len==1 ) {
      MrgProjNode mprj = new MrgProjNode(nnn,mem);
      MemJoinNode mjn = ((MemJoinNode)mem).add_alias_below_new(gvn,mprj,this);
      gvn.set_def_reg(Env.DEFMEM,nnn._alias,mprj);
      return mjn;
    }

    return null;
  }
  @Override public Type value(GVNGCM.Mode opt_mode) {
    if( !(in(0) instanceof NewNode) ) return Type.ANY;
    NewNode nnn = nnn();
    Type tn = nnn.val();
    Type tm = mem().val();
    if( !(tm instanceof TypeMem  ) ) return tm.oob();
    if( !(tn instanceof TypeTuple) ) return tn.oob();
    TypeObj to = (TypeObj)((TypeTuple)tn).at(0);
    TypeMem tmem = (TypeMem)tm;
    return nnn.is_unused()      // This is a cycle-breaking lifting value
      ? tmem.set   (nnn._alias,TypeObj.UNUSED)
      : tmem.st_new(nnn._alias, to);
  }

  @Override BitsAlias escapees() { return in(0).escapees(); }
  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
  // Only called here if alive, and input is more-than-basic-alive
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) { return def==in(0) ? TypeMem.ALIVE : _live; }
}
