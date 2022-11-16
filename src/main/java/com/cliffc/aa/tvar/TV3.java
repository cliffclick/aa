package com.cliffc.aa.tvar;

import com.cliffc.aa.util.*;

import static com.cliffc.aa.AA.unimpl;

/** Type variable base class
 *
 * Type variables can unify (ala Tarjan Union-Find), and can have structure
 * such as "{ A -> B }" or "@{ x = A, y = A }".  Type variables includes
 * polymorphic structures and fields (structural typing not duck typing),
 * polymorphic nil-checking, an error type, and fully supports recursive types.
 *
 * Type variables can be "is_copy", meaning the concrete vars are
 * value-equivalent and not just type equivalent.
 *
 * Field labels can be inferred, and are used to implement a concrete form of
 * overloads or adhoc-polymorphism.  E.g. the blank Field in "(123,"abc")._"
 * will infer either field ".0" or ".1" according to which field types.
 *
 * Bases include anything from the GCP lattice, and are generally sharper than
 * e.g. 'int'.  Bases with values of '3' and "abc" are fine.
 *
 * See HM.java for a simplified complete implementation.  The HM T2 class uses
 * a "soft class" implementation notion: Strings are used to denote java-like
 * classes.  This implementation uses concrete Java classes.
 */

abstract public class TV3 {
  private static int CNT=1;
  final int _uid=CNT++;         // Unique dense int, used in many graph walks for a visit bit

  // Disjoint Set Union set-leader.  Null if self is leader.  Not-null if not a
  // leader, but pointing to a chain leading to a leader.  Rolled up to point
  // to the leader in many, many places.  Classic U-F cost model.
  private TV3 _uf=null;

  // Outgoing edges for structural recursion.
  TV3[] _args = null;
  
  // True if this a set member not leader.  Asserted for in many places.
  public boolean unified() { return _uf!=null; }
  // True if this is a normal Leaf Type Variable
  public boolean is_leaf() { return false; }
  // True if this is a ground term from GCP, e.g. int, flt, string
  public boolean is_base() { return false; }
  // True if this is a function
  public boolean is_fun() { return false; }
  // True if this is a struct
  public boolean is_obj() { return false; }
  // True if this term contains type errors
  public boolean is_err () { return false; }
  
  
  // Find the leader, without rollup.  Used during printing.
  public TV3 debug_find() {
    if( _uf==null ) return this; // Shortcut
    TV3 u = _uf._uf;
    if( u==null ) return _uf; // Unrolled once shortcut
    while( u._uf!=null ) u = u._uf;
    return u;
  }

  // Find the leader, with rollup.  Used in many many places.
  public TV3 find() {
    if( _uf    ==null ) return this;// Shortcut, no rollup
    if( _uf._uf==null ) return _uf; // Unrolled once shortcut, no rollup
    TV3 leader = _find();           // No shortcut\
    // Additional read-barrier for TVNil to collapse nil-of-something
    return leader instanceof TVNil tnil ? tnil.find_nil() : leader;
  }
  // Long-hand lookup of leader, 
  private TV3 _find() {
    TV3 leader = _uf._uf.debug_find();    // Leader
    TV3 u = this;
    while( u!=leader ) { TV3 next = u._uf; u._uf=leader; u=next; }
    return leader;
  }

  // -----------------
  // Classic Hindley-Milner structural unification.
  // Returns false if no-change, true for change.
  // If test, does not actually change anything, just reports progress.
  // If test and change, unifies 'this' into 'that' (changing both), and
  // updates the worklist.
  public boolean unify( TV3 that, boolean test ) {
    throw unimpl();
  }
  

  public boolean fresh_unify( TV3 that, TV3[] nongen, boolean test ) {
    throw unimpl();
  }

  
  // -----------------
  public void add_deps_flow() {
    throw unimpl();
  }
  public void add_deps_work() {
    throw unimpl();
  }
  
  // -----------------
  // Glorious Printing

  // Look for dups, in a tree or even a forest (which Syntax.p() does).  Does
  // not rollup edges, so that debug printing does not have any side effects.
  public VBitSet get_dups() { return _get_dups(new VBitSet(),new VBitSet()); }
  public VBitSet _get_dups(VBitSet visit, VBitSet dups) {
    if( visit.tset(_uid) ) {
      dups.set(debug_find()._uid);
    } else {
      if( _args != null )
        for( TV3 tv3 : _args )  // Edge lookup does NOT 'find()'
          tv3._get_dups(visit,dups);
    }
    return dups;
  }

  public String p() { VCNT=0; VNAMES.clear(); return str(new SB(), new VBitSet(), get_dups(), false ).toString(); }
  private static int VCNT;
  private static final NonBlockingHashMapLong<String> VNAMES = new NonBlockingHashMapLong<>();
  
  @Override public String toString() { return str(new SB(), null, null, true ).toString(); }
  
  public SB str(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    if( visit==null ) {
      dups = get_dups();
      visit = new VBitSet();
    }
    return _str(sb,visit,dups,debug);
  }
  
  // Fancy print for Debuggers - includes explicit U-F re-direction.
  // Does NOT roll-up U-F, has no side-effects.
  SB _str(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    boolean dup = dups.get(_uid);
    if( !debug && unified() ) return find().str(sb,visit,dups,false);
    if( unified() || is_leaf() ) {
      vname(sb,debug);
      return unified() ? _uf.str(sb.p(">>"), visit, dups, debug) : sb;
    }

    // Dup printing for all but bases (which are short, just repeat them)
    if( dup && (debug || !is_base() || is_err()) ) {
      vname(sb,debug);        // Leading V123
      if( visit.tset(_uid) ) return sb; // V123 and nothing else
      sb.p(':');              // V123:followed_by_type_descr
    }
    throw unimpl();
  }
  
  // Pick a nice tvar name.  Generally: "A" or "B" or "V123" for leafs,
  // "X123" for unified but not collapsed tvars.
  private void vname( SB sb, boolean debug) {
    final boolean vuid = debug && (unified()||is_leaf());
    sb.p(VNAMES.computeIfAbsent((long) _uid,
                                (k -> (vuid ? ((is_leaf() ? "V" : "X") + k) : ((++VCNT) - 1 + 'A' < 'V' ? ("" + (char) ('A' + VCNT - 1)) : ("V" + VCNT))))));
  }
  
  // Debugging tool
  TV3 find(int uid) { return _find(uid,new VBitSet()); }
  private TV3 _find(int uid, VBitSet visit) {
    if( visit.tset(_uid) ) return null;
    if( _uid==uid ) return this;
    //if( _args==null ) return null;
    //for( T2 arg : _args.values() )
    //  if( (arg=arg._find(uid,visit)) != null )
    //    return arg;
    //return null;
    throw unimpl();
  }
  static void reset() { CNT=0; }
}
