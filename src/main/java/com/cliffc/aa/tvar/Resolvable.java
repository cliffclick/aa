package com.cliffc.aa.tvar;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.NonBlockingHashMapLong;
import com.cliffc.aa.node.DynLoadNode;
import com.cliffc.aa.node.FreshNode;

import static com.cliffc.aa.AA.unimpl;

abstract public class Resolvable {

//public static NonBlockingHashMapLong<Resolvable> RESOLVINGS  = new NonBlockingHashMapLong<>();
//public static NonBlockingHashMapLong<Resolvable> RESOLVEDS   = new NonBlockingHashMapLong<>();
//
//public DynLoadNode _dyn;      // DynLoad is where match comes from
//public FreshNode _frsh;       // Fresh makes new patterns
//TV3 _pat;                     // Pattern from deep inside Fresh's TVar
//public String _lab;           // Resolved label
//
//Resolvable( DynLoadNode dyn, FreshNode frsh, TV3 pat ) {
//  _dyn = dyn;
//  _frsh = frsh;
//  _pat = pat;
//}
//
//@Override public String toString() {
//  return "resolvable Dyn"+_dyn._uid+", pat "+_pat+(_frsh==null ? "" : " from Fresh"+_frsh._uid);
//}
//
//public static Resolvable make(DynLoadNode dyn) {
//  Resolvable r = new Resolvable(dyn,null,dyn.tvar());
//  Resolvable old = RESOLVINGS.put(r.key(),r);
//  assert old==null;
//  return r;
//}
//
//// Collect delayed-resolve requests
//public static void fresh_add(TV3 pat, TV3 newpat, FreshNode fresh) {
//  assert !pat.unified();
//  for( Resolvable r : RESOLVEDS.values() )
//    if( r.pattern()==pat )
//      throw unimpl();
//  for( Resolvable r : RESOLVINGS.values() )
//    if( r.pattern()==pat )
//      r.add_copy(fresh,newpat);
//}
//
//private static Resolvable FREE=null;
//private void add_copy( FreshNode fresh, TV3 newpat ) {
//  assert _frsh != fresh;       // New pattern 'that' for a new FreshNode
//  Resolvable r = FREE == null ? new Resolvable(_dyn,fresh,newpat) : FREE.init(_dyn,fresh,newpat);
//  if( RESOLVEDS.containsKey(r.key()) ) return; // Already got this and resolved it
//  Resolvable old = RESOLVINGS.putIfAbsent(r.key(),r);
//  if( old!=null ) FREE = r.free();
//}
//private Resolvable init( DynLoadNode dyn, FreshNode fresh, TV3 newpat ) { _dyn = dyn; _frsh=fresh; _pat=newpat; FREE=null; return this; }
//private Resolvable free() { _dyn=null; _frsh=null; _pat=null; _lab=null; return this; }
//
//
//// Pattern to match
//private TV3 pattern() { return _pat.unified() ? (_pat=_pat.find()) : _pat; }
  
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
  public boolean trial_resolve( TVStruct match, TV3 pattern, boolean test ) {
    //TVStruct match = ((TVPtr)_dyn.adr().tvar()).load();
    // Immediate fail if match is open; since more fields may appear best we
    // can do is hard-fail for 2+ yes.  Might as well wait
    if( match.is_open() ) return false;
    //TV3 pattern = pattern();
    
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
      default: throw AA.unimpl();
      };
    }
    
    return switch( yes ) {
        
      case 0 -> maybe==0
        // No YESes, no MAYBES, this is an error
        ? test || _dyn.resolve_failed_no_match(pattern,match,test)
        // no YESes, but more maybes:
        : (maybe==1)            // One maybe can move to a yes, but no more maybes will appear
        ? (test || resolve_it(pattern,match,lab))
        : stall(match);  // Too many maybes: wait
    
      case 1 -> maybe==0 
        // Exactly one yes and no maybes: we can resolve this now
        ? test || resolve_it(pattern, match, lab)
        // Got a YES, but some maybe might become another hard YES, which is an error.
        : stall(match);
        
      default -> 
        // 2+ hard-yes.  This is a hard error, and can never resolve.
        throw unimpl();
      };
  }

  // Field can be resolved to label
  boolean resolve_it( TV3 pattern, TVStruct match, String lab ) {
    Resolvable old = RESOLVINGS.remove(key()     ); assert old==this;
    Resolvable add = RESOLVEDS .put   (key(),this); assert add==null;
    _dyn.add_flow();            // Value call makes progress
    _lab = lab;    
    TV3 prior = match.arg(lab); // Get prior matching match label, if any
    if( prior==null ) {
      throw unimpl(); // todo needs pinned
    } else {
      prior.unify(pattern,false); // Merge pattern and prior label in MATCH
    }
    return true;              // Progress
  }

  // Stall the resolve, and see if we can resolve later.
  // After HM_AMBI, it is too late, and we will never resolve.
  boolean stall(TVStruct match) {
    return false;
  }

  //public long key() { return ((long)_dyn._uid<<32) | (_frsh==null ? 0 : _frsh._uid); }
  //@Override public int hashCode() {
  //  return (_dyn._uid<<16) ^ (_frsh==null ? 0 : _frsh._uid);
  //}
  //
  //@Override public boolean equals(Object o) {
  //  if( this==o ) return true;
  //  if( !(o instanceof Resolvable r) ) return false;
  //  return _dyn==r._dyn && _frsh==r._frsh;
  //}
  //
  //public static void reset_to_init0() {
  //  RESOLVINGS.clear();
  //  RESOLVEDS.clear();
  //}
}
