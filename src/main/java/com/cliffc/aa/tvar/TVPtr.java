package com.cliffc.aa.tvar;

import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;

import static com.cliffc.aa.AA.unimpl;

/** A ptr-to-struct
 *
 */
public class TVPtr extends TVNilable {
  // This has a single pointer edge to a Struct or Leaf (or Err)
  public TVPtr( TV3 rec ) { super(true,false,rec); }
  // Get the Struct
  public TVStruct load() { return (TVStruct)_args[0]; }

  // -------------------------------------------------------------
  @Override
  void _union_impl(TV3 that) {
    if( !(that instanceof TVBase base) ) throw unimpl();
    throw unimpl();
  }

  @Override boolean _unify_impl(TV3 that ) {
    throw unimpl();
  }
  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    return _args[0]._str(sb.p("*"),visit,dups,debug).p(_may_nil ? "?" : "");
  }
}
