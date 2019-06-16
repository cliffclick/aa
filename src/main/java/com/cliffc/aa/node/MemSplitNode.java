package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;

public class MemSplitNode extends Node {
  private final int[] _aliases;
  MemSplitNode( Node wide_mem, int... aliases ) {
    super(OP_SPLIT,null,wide_mem);
    // Aliases to split by need to have no dups, and the input memory is
    // assumed to include all memory.  This is a total split.
    assert aliases != null && aliases.length > 0;
    assert aliases[0] > 0;
    for( int i=1; i< aliases.length; i++ )
      assert aliases[i] > 0 && aliases[i-1] < aliases[i]; // monotonically increasing
    _aliases = aliases;
  }
  
  @Override public Node ideal(GVNGCM gvn) {
    return null;
  }

  @Override public Type value(GVNGCM gvn) {
    TypeMem tmem = (TypeMem)gvn.type(in(1));
    // Return is a Tuple of TypeMem's, all with unrelated aliases.  The slot0
    // is the default and is same as the input (except that the named _aliases
    // are going to be overwritten).  All others are in alias order, but not
    // matching alias#, and contain a TypeMem with just that alias.
    return tmem.split(_aliases);
  }
  @Override public Type all_type() { return TypeMem.MEM; }
}

