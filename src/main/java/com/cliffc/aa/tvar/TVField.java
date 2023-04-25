package com.cliffc.aa.tvar;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.Type;
import java.util.HashMap;

import static com.cliffc.aa.AA.unimpl;

/** Field reference from a Struct
 */
public class TVField extends TV3 {
  
  public TVField( TV3 ptr ) { super(ptr); }

  @Override boolean can_progress() { throw unimpl(); }

  @Override int eidx() { throw unimpl(); }

  // Unresolved field names; typically "&nnn" where `nnn` is the FieldNode id
  public static final HashMap<String,Resolvable> FIELDS = new HashMap<>();
  public static void reset_to_init0() { FIELDS.clear(); }

  // -------------------------------------------------------------
  @Override public boolean _union_impl(TV3 that) {
    throw unimpl();
  }
  
  @Override boolean _unify_impl(TV3 that ) { throw unimpl(); }

  // -------------------------------------------------------------

  @Override boolean _exact_unify_impl( TV3 tv3 ) { throw unimpl(); }

  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) { throw unimpl(); }
  @Override void _widen( byte widen ) { throw unimpl(); }

}
