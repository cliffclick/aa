package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.Ary;

// Tree-like types, used to make equivalence classes.  Tree children are lazily
// split adding layers on demand.  Splitting in a new child is useful during
// e.g. inlining, where a single Call is duplicated and RPCs to the original
// one might return to either of of the inlines.  Same for internal functions
// and allocation sites - after the inline, pointers & references to the
// original might now refer to either copy.  Each copy only refers to itself,
// so after some optimizations the ambiguious bits can be optimized away.
// i.e., its useful to make the distinction between the cloned instances, just
// might be some confusion at first.
//
// Root represents all-of-memory or all-functions or all-callsites.
// Other bits always split from the root, and can split in any pattern.
//
public class TypeTree {
  public final int _idx;
  final TypeTree _par;
  Ary<TypeTree> _kids;          // Null until split
  private boolean _closed;      // No more kids

  TypeTree(TypeTree par, int idx ) {
    _idx=idx;
    _par=par;
    if( par != null ) {
      assert !_closed;
      if( par._kids==null ) par._kids = new Ary<>(new TypeTree[1],0);
      par._kids.push(this);
    }
  }

  void close() { _closed = true; }
  boolean closed() { return _closed; }

  
  @Override public String toString() {
    throw AA.unimpl();
  }
}
