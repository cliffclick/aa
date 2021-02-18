package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.tvar.TMem;
import com.cliffc.aa.tvar.TVDead;
import com.cliffc.aa.tvar.TVar;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.MEM_IDX;

// Proj memory
public class MrgProjNode extends ProjNode {
  public MrgProjNode( NewNode nnn, Node mem ) { super(MEM_IDX,nnn,mem); }
  @Override public String xstr() { return "MrgProj"+_idx; }
  @Override public boolean is_mem() { return true; }
  NewNode nnn() { return (NewNode)in(0); }
  Node    mem() { return          in(1); }


  @Override public Node ideal_reduce() {
    NewNode nnn = nnn();
    Node mem = mem();
    Type t = mem._val;
    // Alias is dead-on-entry.  Then this MrgPrj no longer lifts
    if( t instanceof TypeMem && ((TypeMem)t).at(nnn._alias)==TypeObj.UNUSED && nnn.is_unused() ) // New is dead for no pointers
      return mem;                // Kill MrgNode when it no longer lifts values

    // New is dead from below.
    if( _live.at(nnn._alias)==TypeObj.UNUSED && nnn._keep==0 && !nnn.is_unused() && !is_prim() ) {
      nnn.kill2();      // Killing a NewNode has to do more updates than normal
      return this;
    }

    // If is of a MemJoin and it can enter the split region, do so.
    if( _keep==0 && mem instanceof MemJoinNode && mem._uses._len==1 ) {
      MrgProjNode mprj = new MrgProjNode(nnn,mem);
      MemJoinNode mjn = ((MemJoinNode)mem).add_alias_below_new(mprj,this);
      Env.DEFMEM.set_def(nnn._alias,mprj);
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
      if( MemSplitNode.check_split(this,escs1) )
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
  @Override public Type value(GVNGCM.Mode opt_mode) {
    if( !(in(0) instanceof NewNode) ) return Type.ANY;
    NewNode nnn = nnn();
    Type tn = nnn._val;
    Type tm = mem()._val;
    if( !(tm instanceof TypeMem  ) ) return tm.oob();
    if( !(tn instanceof TypeTuple) ) return tn.oob();
    TypeObj to = (TypeObj)((TypeTuple)tn).at(MEM_IDX);
    TypeMem tmem = (TypeMem)tm;
    return nnn.is_unused()      // This is a cycle-breaking lifting value
      ? tmem.set   (nnn._alias,TypeObj.UNUSED)
      : tmem.st_new(nnn._alias, to);
  }

  @Override BitsAlias escapees() { return in(0).escapees(); }
  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
  // Only called here if alive, and input is more-than-basic-alive
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) { return def==nnn() ? TypeMem.ALIVE : _live; }

  @Override public boolean unify( boolean test ) {
    if( !(in(0) instanceof NewNode) ) return false;
    if( tvar() instanceof TVDead ) return false;
    TMem tmem = (TMem)mem().tvar();
    TVar tself = tvar();
    boolean progress = !(tself instanceof TMem) && tself.unify(tmem, test);
    return tmem.unify_alias(nnn()._alias,nnn().tvar(),test) | progress; // Unify at the alias
  }

}
