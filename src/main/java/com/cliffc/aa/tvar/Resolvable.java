package com.cliffc.aa.tvar;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.FieldNode;
import com.cliffc.aa.util.Ary;

public interface Resolvable {
  // True if this field is still resolving: the actual field being referenced
  // is not yet known.
  boolean is_resolving();
  static boolean is_resolving(String id) { return id.charAt(0)=='&'; }
  // Resolved label; error if still resolving
  String fld();
  // Resolve to string 'lab'
  String resolve(String lab);
  // Self type var; pattern tvar
  TV3 tvar();
  // Match type tvar (as opposed to pattern)
  TV3 match_tvar();
  
  // Attempt to resolve an unresolved field.  No change if test, but reports progress.
  // Returns:
  // - 0  zero matching choices
  // - 1  exactly one choice; resolvable (and resolved if not testing)
  // - 2+ two or more choices; resolve is ambiguous
  
  // "Pattern leafs" are just any TV3 that, if it changes might effect the match outcome.
  static Ary<TVExpanding> PAT_LEAFS = new Ary<>(new TVExpanding[1],0);
  
  default boolean trial_resolve( boolean outie, TV3 pattern, TVStruct lhs, TVStruct rhs, boolean test ) {
    assert !rhs.is_open() && is_resolving();

    // Not yet resolved.  See if there is exactly 1 choice.
    PAT_LEAFS.clear();
    String lab = null;
    for( int i=0; i<rhs.len(); i++ ) {
      String id = rhs.fld(i);
      if( is_resolving(id) ) continue;
      if( pattern.trial_unify_ok(rhs.arg(id),false) ) {
        if( lab==null ) lab=id;   // No choices yet, so take this one
        else {
          // 2nd choice; ambiguous; either cannot resolve (yet), or too late
          // and will never resolve.  Record all pattern leaves in the RHS
          // delay list which may later expand and force the resolve.
          while( PAT_LEAFS._len>0 )
            PAT_LEAFS.pop().add_delay_resolve(rhs);
          return false;
        }
      }
    }
    if( lab==null ) return false; // No match, so error and never resolves
    // Field can be resolved to label
    if( test ) return true;     // Will be progress to resolve

    String old_fld = resolve(lab);      // Change field label
    boolean old = lhs.del_fld(old_fld); // Remove old label from lhs, if any
    TV3 prior = lhs.arg(lab);           // Get prior matching lhs label, if any
    if( prior==null ) {
      assert old;               // Expect an unresolved label
      //lhs.add_fld(lab,pattern); // Add label and pattern, basically replace unresolved old_fld with lab
      throw com.cliffc.aa.AA.unimpl(); // todo needs pinned
    } else {
      if( outie ) prior. unify(pattern,test); // Merge pattern and prior label in LHS
      else        prior._unify(pattern,test); // Merge pattern and prior label in LHS
    }
    return true;              // Progress
  }

  static boolean add_pat_leaf(TVExpanding leaf) {
    if( PAT_LEAFS.find(leaf)== -1 )
      PAT_LEAFS.add(leaf);
    return true;
  }
    
  // Resolve failed; if ambiguous report that; if nothing present report that;
  // otherwise force unification on all choices which will trigger an error on
  // each choice.
  default void resolve_failed() {
    FieldNode fld = (FieldNode)this;
    String msg = fld.resolve_failed_msg();
    tvar().unify_err(msg,match_tvar(),false);
    Env.GVN.add_flow(fld);
    fld.deps_work_clear();
  }
  
}
