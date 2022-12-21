package com.cliffc.aa.tvar;

import static com.cliffc.aa.AA.unimpl;

public interface Resolvable {
  boolean is_resolving();
  void resolve(String lab);
  // True if this field is still resolving: the actual field being referenced
  // is not yet known.
  static boolean is_resolving(String id) { return id.charAt(0)=='&'; }

  // Attempt to resolve an unresolved field.  No change if test, but reports progress.
  default boolean trial_resolve( TV3 pattern, TVStruct lhs, TVStruct rhs, boolean test ) {
    assert !rhs.is_open() && is_resolving();

    // Not yet resolved.  See if there is exactly 1 choice.
    String lab = null;
    for( int i=0; i<rhs.len(); i++ ) {
      String id = rhs.fld(i);
      if( !is_resolving(id) && pattern.trial_unify_ok(rhs.arg(id),false) ) {
        if( lab==null ) lab=id;   // No choices yet, so take this one
        // 2nd choice; ambiguous; either cannot resolve (yet), or too late and
        // will never resolve
        else return false;
      }
    }
    // Field can be resolved to label
    if( test ) return true;     // Will be progress to resolve
    
    throw unimpl();
  }
}
