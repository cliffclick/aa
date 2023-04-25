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
  public TVPtr( boolean may_nil, TV3 rec ) { super(may_nil,rec); }
  public TVPtr( TV3 rec ) { this(false,rec); }
  // Get the Struct
  public TV3 load() { return arg(0); }

  @Override boolean can_progress() { return false; }

  @Override int eidx() { return TVErr.XPTR; }

  // Make the leader a nilable version of 'this' child
  @Override TV3 find_nil() {
    TV3 ptr = copy();
    ptr.add_may_nil(false);
    return ptr;
  }

  // -------------------------------------------------------------
  // No subparts to union
  @Override public boolean _union_impl(TV3 that) { return false; }

  @Override boolean _unify_impl(TV3 that ) { return arg(0)._unify(that.arg(0),false); }

  // -------------------------------------------------------------
  @Override boolean _trial_unify_ok_impl( TV3 tv3, boolean extras ) {
    TVPtr that = (TVPtr)tv3; // Invariant when called
    // Structural trial unification on the one child
    return load()._trial_unify_ok( that.load(), extras);
  }

  @Override boolean _exact_unify_impl( TV3 tv3 ) { return true; }
  
  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) {
    // Compatible escaped aliases
    BitsAlias aliases = Env.ROOT.matching_escaped_aliases(this, dep);
    TypeStruct tstr = dep==null ? (TypeStruct)load()._as_flow(dep) : TypeStruct.ISUSED;
    return TypeMemPtr.make(false,_may_nil,aliases,tstr);
  }
  @Override void _widen( byte widen ) { load().widen(widen,false); }
  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    return _args[0]._str(sb.p("*"),visit,dups,debug).p(_may_nil ? "?" : "");
  }
}
