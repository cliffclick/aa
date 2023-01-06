package com.cliffc.aa.node;

import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeStruct;
import com.cliffc.aa.type.TypeTuple;

import static com.cliffc.aa.AA.MEM_IDX;

// Proj memory
public class MProjNode extends ProjNode {

  public MProjNode( Node head ) { super(head, MEM_IDX); }
  public MProjNode( Node head, int idx ) { super(head,idx); }
  @Override public String xstr() { return "MProj"+_idx; }
  @Override public boolean is_mem() { return true; }
  NewNode nnn() { return (NewNode)in(0); }

  @Override public Type live_use( Node def ) { return _live; }

  @Override public Node ideal_reduce() {
    // Fold dying calls
    Node mem = in(0).is_copy(MEM_IDX);
    if( mem != null )
      return mem;

    // Allocation has no ptr uses, so is dead, so drop
    if( in(0) instanceof NewNode nnn && nnn._uses._len==1 ) {
      TypeMem tnnn = (TypeMem)((TypeTuple)nnn._val).at(1);
      TypeStruct tns = tnnn.at(nnn._alias);
      // All memory has to be monotonic; easiest to require all the same
      if( tnnn==_val ) {
        if( tnnn==nnn.mem()._val && tns==TypeStruct.UNUSED ) return nnn.mem();
        else nnn.mem().deps_add(this); // Rerun self if nnn.mem upgrades
      } else in(0).deps_add(this);
    } else in(0).deps_add(this);
    return null;
  }
  
  @Override boolean assert_live(Type live) { return live instanceof TypeMem; }
  
}
