package com.cliffc.aa.tvar;

import com.cliffc.aa.Combo;
import com.cliffc.aa.node.DynLoadNode;
import com.cliffc.aa.util.Ary;

import static com.cliffc.aa.AA.unimpl;

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
  // ( @{name:str, ... } @{ age=A } ) -vs- @{ age=B } // Ambiguous, first struct could pick up age, 2nd struct A & B could fail later
  // ( @{name:str      } @{ age=A } ) -vs- @{ age=B } // Ambiguous, first struct is a clear miss  , 2nd struct A & B could fail later
  // ( @{name:str      } @{ age=A } ) -vs- @{ age=A } // OK, A & A cannot miss
  // ( @{name:str, ... } @{ age=A } ) -vs- @{ age=A } // Ambiguous, first struct could pick up age=A
  //
  // So each match has the following 3 choices
  // - hard no , something structural is wrong
  // - hard yes, all parts match, even leaf-for-leaf.  No open struct in pattern.
  // - maybe   , all parts match, except leafs.  Leafs might expand later and fail or become a hard-yes.

  // "Pattern leafs" are just any TV3 that, if it changes might effect the match outcome.
  Ary<TVExpanding> PAT_LEAFS = new Ary<>(new TVExpanding[1],0);
  

  // Returns progress, not successful resolve
  default boolean trial_resolve( boolean outie, TV3 pattern, TVStruct rhs, boolean test ) {
    assert !rhs.is_open() && is_resolving();

    // Not yet resolved.  See if there is exactly 1 choice.
    // Hard YESes and NOs can never change, so we cache those results.
    // The good case is: 1 YES, 0 MAYBES, and any number of NOs.
    // Any number of MAYBEs implies we need to stall; they might turn into either a YES or a NO.
    PAT_LEAFS.clear();
    int yes=0, maybe=0;
    String lab=null;
    for( int i=0; i<rhs.len(); i++ ) {
      String id = rhs.fld(i);
      if( is_resolving(id) ) continue;
      TV3 rhsx = rhs.arg(id);      

      // Count YES, NO, and MAYBEs
      switch( pattern.trial_unify_ok( rhsx ) ) {
      case 7: break;                  // No.
      case 1: yes++; lab = id; break; // Track a sample YES label
      default: maybe++; break;
      };
    }

    return switch( yes ) {
        
      case 0 -> maybe==0
        // No YESes, no MAYBES, this is an error
        ? test || ((DynLoadNode)this).resolve_failed_no_match(pattern,rhs,test)
        // no YESes, but more maybes: wait.
        : (maybe==1)
        ? (test || resolve_it(outie,pattern,rhs,lab))
        : stall(rhs);

      case 1 -> maybe==0 
        // Exactly one yes and no maybes: we can resolve this now
        ? test || resolve_it(outie,pattern,rhs,lab)
        // Got a YES, but some maybe might become another hard YES, which is an error.
        : stall(rhs);
        
      default -> 
        // 2+ hard-yes.  This is a hard error, and can never resolve.
        throw unimpl();
      };
  }

  // Stall the resolve, and see if we can resolve later.
  // After HM_AMBI, it is too late, and we will never resolve.
  default boolean stall(TVStruct rhs) {
    if( Combo.HM_AMBI )
      //return ((FieldNode)this).resolve_ambiguous_msg();
      throw unimpl();
    // Not resolvable (yet).  Delay until it can resolve.
    while( PAT_LEAFS._len>0 )
      PAT_LEAFS.pop().add_delay_resolve(rhs);
    return false;
  }

  // Field can be resolved to label
  default boolean resolve_it(boolean outie, TV3 pattern, TVStruct rhs, String lab ) {
    String old_fld = resolve(lab);      // Change field label
    boolean old = rhs.del_fld(old_fld); // Remove old label from rhs, if any
    TV3 prior = rhs.arg(lab);           // Get prior matching rhs label, if any
    if( prior==null ) {
      assert old;               // Expect an unresolved label
      //rhs.add_fld(lab,pattern); // Add label and pattern, basically replace unresolved old_fld with lab
      throw unimpl(); // todo needs pinned
    } else {
      if( outie ) prior. unify(pattern,false); // Merge pattern and prior label in RHS
      else        prior._unify(pattern,false); // Merge pattern and prior label in RHS
    }
    return true;              // Progress
  }

  // Track expanding terms; this need to recheck the match if they expand.
  // Already return 0 for a "maybe".
  static int add_pat_dep(TVExpanding leaf) {
    if( PAT_LEAFS.find(leaf)== -1 )
      PAT_LEAFS.add(leaf);
    return 0;                   // Always reports a "maybe"
  }

  // Resolve failed; if ambiguous report that; if nothing present report that;
  // otherwise force unification on all choices which will trigger an error on
  // each choice.
  abstract void resolve_or_fail();

  public static void reset_to_init0() {
  }
}
