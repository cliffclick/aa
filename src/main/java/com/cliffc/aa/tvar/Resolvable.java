package com.cliffc.aa.tvar;

import com.cliffc.aa.AA;
import com.cliffc.aa.Env;
import com.cliffc.aa.node.DynLoadNode;
import com.cliffc.aa.util.Util;

import static com.cliffc.aa.AA.TODO;

public class Resolvable {

  public DynLoadNode _dyn;      // DynLoad is where match comes from
  public UQNodes _path;         // List of Fresh + Dyn involved
  TVStruct _match;
  TV3 _pat;                     // Pattern from deep inside Fresh's TVar
  public String _label;         // Resolved label
  
  public Resolvable( DynLoadNode dyn, UQNodes path, TVStruct match, TV3 pat ) {
    _dyn = dyn;
    _path = path;
    _match = match;
    _pat = pat;
  }

  @Override public String toString() {
    return "resolvable Dyn"+_dyn._uid+", "+_path+", find "+_pat+" in "+_match+(_label==null ? "" : " as "+_label);
  }
  
  // Pattern to match
  private TV3 pattern() { return _pat.unified() ? (_pat=_pat.find()) : _pat; }
  private TVStruct match() { return _match.unified() ? (_match=(TVStruct)_match.find()) : _match; }
  
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

  // Returns progress, not successful resolve
  public boolean trial_resolve( boolean test ) {
    TVStruct match = match();
    // Immediate fail if match is open; since more fields may appear best we
    // can do is hard-fail for 2+ yes.  Might as well wait
    if( match.is_open() ) return false;
    TV3 pattern = pattern();
    
    // Not yet resolved.  See if there is exactly 1 choice.
    // The good case is: 1 YES, 0 MAYBES, and any number of NOs.
    // Any number of MAYBEs implies we need to stall; they might turn into either a YES or a NO.
    int yes=0, maybe=0;
    String lab=null;
    for( int i=0; i<match.len(); i++ ) {
      String id = match.fld(i);
      TV3 rhsx = match.arg(id);      
    
      // Count YES, NO, and MAYBEs
      switch( pattern.trial_unify_ok( rhsx ) ) {
      case 7: break;                    // No.  Don't lose label tracking
      case 3: maybe++; lab = id; break; // Track a sample MAYBE label
      case 1: yes++  ; lab = id; break; // Track a sample YES   label
      default: throw AA.TODO();
      };
    }
    
    return switch( yes ) {
        
      case 0 -> maybe==0
        // No YESes, no MAYBES, this is an error
        ? test || _dyn.resolve_failed_no_match(pattern,match,test)
        // no YESes, but more maybes:
        : (maybe==1)            // One maybe can move to a yes, but no more maybes will appear
        ? resolve_it(lab,test)
        : stall(match);  // Too many maybes: wait
    
      case 1 -> maybe==0 
        // Exactly one yes and no maybes: we can resolve this now
        ? resolve_it(lab,test)
        // Got a YES, but some maybe might become another hard YES, which is an error.
        : stall(match);
        
      default -> 
        // 2+ hard-yes.  This is a hard error, and can never resolve.
        throw TODO();
      };
  }

  // Field can be resolved to label
  boolean resolve_it( String lab, boolean test ) {
    if( Util.eq(lab,_label) ) return false; // Already resolved this way, no progress
    assert _label==null;
    if( test ) return TV3.ptrue();
    Env.GVN.add_flow(_dyn);     // Value call makes progress
    _label = lab;    
    TV3 prior = match().arg(lab); // Get prior matching match label, if any
    if( prior==null ) {
      throw TODO(); // todo needs pinned
    } else {
      prior.unify(pattern(),false); // Merge pattern and prior label in MATCH
    }
    return TV3.ptrue();             // Progress
  }

  // Stall the resolve, and see if we can resolve later.
  // After HM_AMBI, it is too late, and we will never resolve.
  boolean stall(TVStruct match) {
    return false;
  }
}
