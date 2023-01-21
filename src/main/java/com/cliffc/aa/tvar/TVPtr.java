package com.cliffc.aa.tvar;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import static com.cliffc.aa.AA.unimpl;

/** A ptr-to-struct
 *
 */
public class TVPtr extends TV3 {
  // This has a single pointer edge to a Struct or Leaf (or Err)
  public TVPtr( TV3 rec ) { super(true,rec); }
  // Get the Struct
  public TV3 load() { return arg(0); }

  // -------------------------------------------------------------
  @Override
  void _union_impl(TV3 that) {
    assert _uid > that._uid;
    // No subparts to union
  }

  @Override boolean _unify_impl(TV3 that ) { return arg(0)._unify(that.arg(0),false); }

  @Override boolean _trial_unify_ok_impl( TV3 tv3, boolean extras ) {
    TVPtr that = (TVPtr)tv3; // Invariant when called
    // Structural trial unification on the one child
    return load()._trial_unify_ok_impl( that.load(), extras);
  }

  @Override int eidx() { throw unimpl(); }

  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    return _args[0]._str(sb.p("*"),visit,dups,debug).p(_may_nil ? "?" : "");
  }
}
