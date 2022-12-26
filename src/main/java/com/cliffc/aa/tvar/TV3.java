package com.cliffc.aa.tvar;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.ConNode;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.util.NonBlockingHashMapLong;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

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
 *
 * BNF for the "core AA" pretty-printed types:
 *    T = Vnnn               | // Leaf number nnn
 *        Xnnn>>T            | // Unified; lazily collapsed with 'find()' calls
 *        base               | // any lattice element, all are nilable
 *        { T* -> Tret }     | // Lambda, arg count is significant
 *        *T0                | // Ptr-to-struct; T0 is either a leaf, or unified, or a struct
 *        @{ (label = T;)* } | // ';' is a field-separator not a field-end
 *        @{ (_nnn = T;)* }  | // Some field labels are inferred; nnn is the Field uid, and will be inferred to the actual label
 *        [Error base* T0*]  | // A union of base and not-nil, lambda, ptr, struct
 *
 */

abstract public class TV3 {
  private static int CNT=1;
  public final int _uid=CNT++; // Unique dense int, used in many graph walks for a visit bit

  // Disjoint Set Union set-leader.  Null if self is leader.  Not-null if not a
  // leader, but pointing to a chain leading to a leader.  Rolled up to point
  // to the leader in many, many places.  Classic U-F cost model.
  private TV3 _uf=null;

  // Outgoing edges for structural recursion.
  TV3[] _args;

  // All uses of this type-var are value-equivalent to the def.
  // Makes a one-shot transition from true to false.
  boolean _is_copy = true;

  // Nodes to put on a worklist, if this TV3 is modified.
  UQNodes _deps = null;
  
  //
  TV3() { _args=null; }
  TV3( boolean is_copy, TV3... args ) { _is_copy = is_copy; _args=args; }
  
  // True if this a set member not leader.  Asserted for in many places.
  public boolean unified() { return _uf!=null; }
  
  // Find the leader, without rollup.  Used during printing.
  public TV3 debug_find() {
    if( _uf==null ) return this; // Shortcut
    TV3 u = _uf._uf;
    if( u==null ) return _uf; // Unrolled once shortcut
    while( u._uf!=null ) u = u._uf;
    return u;
  }

  // Find the leader, with rollup.  Used in many, many places.
  public TV3 find() {
    if( _uf    ==null ) return this;// Shortcut, no rollup
    if( _uf._uf==null ) return _uf; // Unrolled once shortcut, no rollup
    TV3 leader = _find();           // No shortcut
    // Additional read-barrier for TVNil to collapse nil-of-something
    return leader instanceof TVNil tnil ? tnil.find_nil() : leader;
  }
  // Long-hand lookup of leader, with rollups
  private TV3 _find() {
    TV3 leader = _uf._uf.debug_find();    // Leader
    TV3 u = this;
    while( u!=leader ) { TV3 next = u._uf; u._uf=leader; u=next; }
    return leader;
  }

  // Fetch a specific arg index, with rollups
  public TV3 arg( int i ) {
    assert !unified();          // No body nor outgoing edges in non-leaders
    TV3 arg = _args[i], u = arg.find();
    return u==arg ? u : (_args[i]=u);
  }

  // Fetch a specific arg index, withOUT rollups
  public TV3 debug_arg( int i ) { return _args[i].debug_find(); }

  public int len() { return _args.length; }  

  private long dbl_uid(TV3 t) { return dbl_uid(t._uid); }
  private long dbl_uid(long uid) { return ((long)_uid<<32)|uid; }

  // -----------------
  // U-F union; this becomes that; returns 'that'.
  // No change if only testing, and reports progress.
  boolean union(TV3 that) {
    assert !unified() && !that.unified(); // Cannot union twice
    if( this==that ) return false;
    that._is_copy &= _is_copy;  // Both must be is_copy to keep is_copy
    _union_impl(that);          // Merge subclass specific bits
    this._deps_work_clear();    // This happens before the unification
    that._deps_work_clear();
    _uf = that;                 // U-F union
    return true;
  }

  // Merge subclass specific bits
  abstract void _union_impl(TV3 that);
  
  // -------------------------------------------------------------
  // Classic Hindley-Milner structural unification.
  // Returns false if no-change, true for change.
  // If test, does not actually change anything, just reports progress.
  // If test and change, unifies 'this' into 'that' (changing both), and
  // updates the worklist.

  // Supports iso-recursive types, nilable, overload field resolution, and the
  // normal HM structural recursion.
  static private final NonBlockingHashMapLong<TV3> DUPS = new NonBlockingHashMapLong<>();
  public boolean unify( TV3 that, boolean test ) {
    if( this==that ) return false;
    assert DUPS.isEmpty();
    boolean progress = _unify(that,test);
    DUPS.clear();
    return progress;
  }
  
  // Structural unification, 'this' into 'that'.  No change if just testing and
  // returns a progress flag.  If updating, both 'this' and 'that' are the same
  // afterwards.
  boolean _unify(TV3 that, boolean test) {
    assert !unified() && !that.unified();
    if( this==that ) return false;
    
    // Any leaf immediately unifies with any non-leaf; triangulate
    if( !(this instanceof TVLeaf) && that instanceof TVLeaf ) return test || that._unify_impl(this);
    if( !(that instanceof TVLeaf) && this instanceof TVLeaf ) return test || this._unify_impl(that);

    // Nil can unify with a non-nil anything, typically
    if( !(this instanceof TVNil) && that instanceof TVNil ) throw unimpl();
    if( !(that instanceof TVNil) && this instanceof TVNil ) throw unimpl();
    
    // If 'this' and 'that' are different classes, unify both into an error
    if( getClass() != that.getClass() )
      throw unimpl();

    // Cycle check
    long luid = dbl_uid(that);    // long-unique-id formed from this and that
    TV3 rez = DUPS.get(luid);
    if( rez==that ) return false; // Been there, done that
    assert rez==null;
    DUPS.put(luid,that);        // Close cycles
    
    
    if( test ) return true;     // Always progress from here
    // Same classes.   Swap to keep uid low.
    // Do subclass unification.
    if( _uid > that._uid ) { this._unify_impl(that);  find().union(that.find()); }
    else                   { that._unify_impl(this);  that.find().union(find()); }
    return true;
  }

  // Must always return true; used in flow-coding in many places
  abstract boolean _unify_impl(TV3 that);
  
  // -------------------------------------------------------------
  public boolean fresh_unify( TV3 that, TV3[] nongen, boolean test ) {
    if( this==that ) return false;
    throw unimpl();
  }

  // Do a trial unification between this and that.
  // Report back false if any error happens, or true if no error.
  // No change to either side, this is a trial only.
  private static final NonBlockingHashMapLong<TV3> TDUPS = new NonBlockingHashMapLong<>();
  boolean trial_unify_ok(TV3 that, boolean extras) {
    TDUPS.clear();
    return _trial_unify_ok(that, extras);
  }
  boolean _trial_unify_ok(TV3 that, boolean extras) {
    assert !unified() && !that.unified();
    long duid = dbl_uid(that._uid);
    if( TDUPS.putIfAbsent(duid,this)!=null )
      return true;              // Visit only once, and assume will resolve
    if( this==that )             return true; // No error
    if( this instanceof TVLeaf ) return true; // No error
    if( that instanceof TVLeaf ) return true; // No error
    
    // Different classes always fail
    if( getClass() != that.getClass() )
      throw unimpl();
    // Subclasses check subparts
    return _trial_unify_ok_impl(that, extras);
  }

  // Sub-classes specify on sub-parts
  boolean _trial_unify_ok_impl( TV3 that, boolean extras ) {
    throw unimpl();
  }
  
  // -----------------
  
  // Recursively add 'n' to 'this' and all children.
  
  // Stops when it sees 'n'; this closes cycles and short-cuts repeated adds of
  // 'n'.  Requires internal changes propagate internal _deps.
  public Node deps_add_deep( Node n ) {
    if( !_dep_add(n) ) return n;
    if( _args!=null )
      for( int i=0; i<len(); i++ )
        if( _args[i]!=null )
          arg(i).deps_add_deep(n);
    return n;
  }
  // Add n to _deps.  Returns true if added, false if already there
  private boolean _dep_add( Node n ) {
    if( _deps==null ) _deps = UQNodes.make(n);
    else if( _deps.containsKey(n._uid) ) return false;
    else _deps = _deps.add(n);
    return true;
  }

  // Something changed; add the deps to the worklist and clear.
  private void _deps_work_clear() {
    if( _deps == null ) return;
    Env.GVN.add_flow(_deps);
    for( Node n : _deps.values() ) if( n instanceof ConNode) n.unelock(); // hash changes
    _deps = null;
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
          if( tv3!=null )
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
    if( unified() || this instanceof TVLeaf ) {
      vname(sb,debug,true);
      return unified() ? _uf.str(sb.p(">>"), visit, dups, debug) : sb;
    }

    // Dup printing for all but bases (which are short, just repeat them)
    if( dup && (debug || !(this instanceof TVBase) ) ) {
      vname(sb,debug,false);            // Leading V123
      if( visit.tset(_uid) ) return sb; // V123 and nothing else
      sb.p(':');                        // V123:followed_by_type_descr
    }
    if( !_is_copy ) sb.p('%');

    return _str_impl(sb,visit,dups,debug);    
  }

  // Generic structural TV3
  SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    sb.p(getClass().getSimpleName()).p("( ");
    if( _args!=null )
      for( TV3 tv3 : _args )
        tv3._str(sb,visit,dups,debug).p(" ");
    return sb.unchar().p(")");    
  }
  
  // Pick a nice tvar name.  Generally: "A" or "B" or "V123" for leafs,
  // "X123" for unified but not collapsed tvars.
  private void vname( SB sb, boolean debug, boolean uni_or_leaf) {
    final boolean vuid = debug && uni_or_leaf;
    sb.p(VNAMES.computeIfAbsent((long) _uid,
                                (k -> (vuid ? ((unified() ? "X" : "V") + k) : ((++VCNT) - 1 + 'A' < 'V' ? ("" + (char) ('A' + VCNT - 1)) : ("V" + VCNT))))));
  }
  
  // Debugging tool
  TV3 f(int uid) { return _find(uid,new VBitSet()); }
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

  public static void reset_to_init0() { CNT=0; TVField.reset_to_init0(); }
}
