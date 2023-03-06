package com.cliffc.aa.tvar;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

/** A ptr-to-struct
 *
 */
public class TVPtr extends TV3 {
  // This has a single pointer edge to a Struct or Leaf (or Err)
  public TVPtr( TV3 rec ) { super(true,rec); }
  // Get the Struct
  public TV3 load() { return arg(0); }

  @Override int eidx() { return TVErr.XPTR; }

  // Make the leader a nilable version of 'this' child
  @Override TV3 find_nil(TVNil nil) {
    TV3 ptr = copy();
    ptr._may_nil = true;
    nil.union(ptr);
    return ptr;
  }

  // -------------------------------------------------------------
  // No subparts to union
  @Override void _union_impl(TV3 that) { }

  @Override boolean _unify_impl(TV3 that ) { return arg(0)._unify(that.arg(0),false); }

  // -------------------------------------------------------------
  @Override boolean _trial_unify_ok_impl( TV3 tv3, boolean extras ) {
    TVPtr that = (TVPtr)tv3; // Invariant when called
    // Structural trial unification on the one child
    return load()._trial_unify_ok( that.load(), extras);
  }

  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) {
    BitsAlias aliases = Env.ROOT.matching_escaped_aliases(this, dep);
    TypeStruct tstr = dep==null ? (TypeStruct)load()._as_flow(dep) : TypeStruct.ISUSED;
    return TypeMemPtr.make(false,_may_nil,aliases,tstr);
  }
  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    return _args[0]._str(sb.p("*"),visit,dups,debug).p(_may_nil ? "?" : "");
  }
}
