package com.cliffc.aa.tvar;

import com.cliffc.aa.Env;
import com.cliffc.aa.Parse;
import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;

import java.util.IdentityHashMap;

import static com.cliffc.aa.AA.TODO;

/** Type variable base class
 * <p>
 * Type variables can unify (ala Tarjan Union-Find), and can have structure
 * such as "{ A -> B }" or "@{ x = A, y = A }".  Type variables includes
 * polymorphic structures and fields (structural typing not duck typing),
 * polymorphic nil-checking, an error type, and fully supports recursive types.
 * <p>
 * Type variables can be "is_copy", meaning the concrete vars are
 * value-equivalent and not just type equivalent.
 * <p>
 * Field labels can be inferred, and are used to implement a concrete form of
 * overloads or adhoc-polymorphism.  E.g. the blank Field in "(123,"abc")._"
 * will infer either field ".0" or ".1" according to which field types.
 * <p>
 * Bases include anything from the GCP lattice, and are generally sharper than
 * e.g. 'int'.  Bases with values of '3' and "abc" are fine.
 * <p>
 * See HM.java for a simplified complete implementation.  The HM T2 class uses
 * a "soft class" implementation notion: Strings are used to denote java-like
 * classes.  This implementation uses concrete Java classes.
 * <p>
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

abstract public class TV3 implements Cloneable {
  public static final boolean WIDEN = true;

  private static int CNT=1;
  static int TV3UID = -1;
  private int uid() {
    if( CNT==TV3UID )
      System.out.println();
    return CNT++;
  }
  public int _uid=uid(); // Unique dense int, used in many graph walks for a visit bit

  // Disjoint Set Union set-leader.  Null if self is leader.  Not-null if not a
  // leader, but pointing to a chain leading to a leader.  Rolled up to point
  // to the leader in many, many places.  Classic U-F cost model.
  TV3 _uf;

  // Outgoing edges for structural recursion.  For Struct, its the fields.  For
  // Ptr, its the Struct.  For Lambda, its the args and return.
  TV3[] _args;

  // True if this type can be specified by some generic Root argument.
  // Forces all Bases to widen.
  byte _widen;

  // Might be a nil (e.g. mixed in with a 0 or some unknown ptr)
  boolean _may_nil;
  // Cannot NOT be a nil (e.g. used as ptr.fld)
  boolean _use_nil;

  // Nodes to put on a worklist, if this TV3 is modified.
  UQNodes _deps;

  //
  TV3() { this((TV3[])null); }
  TV3( TV3... args ) { _args = args; }
  TV3( boolean may_nil, TV3... args ) { _args = args; _may_nil = may_nil; }

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
  public <T extends TV3> T find() {
    T leader = (T)_find0();
    return leader;
    //// Additional read-barrier for TVNil to collapse nil-of-something
    //if( !(leader instanceof TVNil tnil) ) return leader;
    //TV3 nnn = leader.arg(0);
    //if( nnn instanceof TVLeaf ) return leader; // No change
    //nnn = nnn.find_nil();
    //leader.union(nnn);
    //return nnn;
  }
  public TV3 _find0() {
    if( _uf    ==null ) return this;// Shortcut, no rollup
    if( _uf._uf==null ) return _uf; // Unrolled once shortcut, no rollup
    return _find();                 // No shortcut
  }
  // Long-hand lookup of leader, with rollups
  private TV3 _find() {
    TV3 leader = _uf._uf.debug_find();    // Leader
    TV3 u = this;
    // Rollup.  Critical to the O(lg lg n) running time of the UF algo.
    while( u!=leader ) { TV3 next = u._uf; u._uf=leader; u=next; }
    return leader;
  }

  // Bases return the not-nil base; pointers return the not-nil pointer.
  // Nested nils collapse.
  //TV3 find_nil() { throw TODO(); }

  // Fetch a specific arg index, with rollups
  public TV3 arg( int i ) {
    assert !unified();          // No body nor outgoing edges in non-leaders
    TV3 arg = _args[i];
    if( arg==null ) return null;
    TV3 u = arg.find();
    return u==arg ? u : (_args[i]=u);
  }
  public void arg( int i, TV3 arg ) {
    assert !unified();
    _args[i] = arg;
  }

  // Fetch a specific arg index, withOUT rollups
  public TV3 debug_arg( int i ) { return _args[i].debug_find(); }

  public int len() { return _args.length; }

  abstract int eidx();
  public TVStruct as_struct() { throw TODO(); }
  public TVLambda as_lambda() { throw TODO(); }
  //public TVNil    as_nil   () { throw TODO(); }
  public TVPtr    as_ptr   () { throw TODO(); }
  public TVDynTable as_dyn () { throw TODO(); }

  public  long dbl_uid( TV3 t ) { assert !t.unified(); return dbl_uid(t._uid); }
  private long dbl_uid(long uid) {  assert !unified(); return ((long)_uid<<32)|uid; }

  public boolean may_nil() { return _may_nil; }

  // Set may_nil flag.  Return progress flag.
  // Set an error if both may_nil and use-nil.
  public void add_may_nil( boolean test) {
    if( _may_nil ) return;   // No change
    if( test ) return;       // Will be progress
    if( _use_nil )
      _unify_err("May be nil",null,null,false);
    _may_nil = ptrue();
  }
  // Set use_nil flag. Set an error if both may_nil and use-nil.
  public void add_use_nil() {
    if( !_use_nil ) {
      _use_nil=true;                 // Progress
      if( _may_nil ) throw TODO(); // unify_errs("May be nil",work);
    }
  }

  public static boolean HALT_IF_PROGRESS = false;
  public static boolean ptrue() {
    if( HALT_IF_PROGRESS ) {
      System.err.println("progress ");
    }
    return true;
  }

  // -----------------
  // U-F union; this becomes that; returns 'that'.
  // Reports progress.
  final boolean union(TV3 that) {
    if( this==that ) return false;
    ptrue();
    assert !unified() && !that.unified(); // Cannot union twice
    if( _may_nil ) that.add_may_nil(false);
    if( _use_nil ) that.add_use_nil();
    if( that._may_nil && that._use_nil )
      { that=that.find(); }
    _union_impl(that); // Merge subclass specific bits into that
    that.widen(_widen,false);

    // Move delayed-fresh & delay-resolve updates onto the not-delayed list
    _union_delay(that);
    // Add Node updates to _work_flow list
    that._union_deps(this);
    // Actually make "this" into a "that"
    _uf = that;                 // U-F union
    return true;
  }

  // Merge subclass specific bits
  abstract public void _union_impl(TV3 that);

  public void _union_delay(TV3 that) { }

  // Push all dependent nodes onto the worklist
  public void _union_deps(TV3 that) {
    this._deps_work_clear();    // This happens before the unification
    that._deps_work_clear();
  }

  void merge_delay_fresh(Ary<TVExpanding.DelayFresh>dfs) {
    if( dfs==null || dfs.len()==0 ) return;
    if( _args==null ) return;
    for( int i=0; i<len(); i++ )
      if( arg(i) != null )
        arg(i).merge_delay_fresh(dfs);
  }

  // -------------------------------------------------------------
  // Classic Hindley-Milner structural unification.
  // Returns false if no-change, true for change.
  // If test, does not actually change anything, just reports progress.
  // If test and change, unifies 'this' into 'that' (changing both), and
  // updates the worklist.

  // Supports iso-recursive types, nilable, overload field resolution, and the
  // normal HM structural recursion.
  public static final NonBlockingHashMapLong<TV3> DUPS = new NonBlockingHashMapLong<>();
  public boolean unify( TV3 that, boolean test ) {
    if( this==that ) return false;
    assert DUPS.isEmpty();
    boolean progress = _unify(that,test);
    DUPS.clear();
    return progress;
  }

  // Structural unification, 'this' into 'that'.  No change if just testing and
  // returns a progress flag.  If updating, both 'this' and 'that' are the same
  // afterward.
  final boolean _unify(TV3 that, boolean test) {
    assert !unified() && !that.unified();
    if( this==that ) return false;

    // Any leaf immediately unifies with any non-leaf; triangulate
    if( !(this instanceof TVLeaf) && that instanceof TVLeaf ) return test || that._unify_impl(this);
    if( !(that instanceof TVLeaf) && this instanceof TVLeaf ) return test || this._unify_impl(that);

    //// Nil can unify with a non-nil anything, typically
    //if( !(this instanceof TVNil) && that instanceof TVNil nil ) return nil._unify_nil(this,test);
    //if( !(that instanceof TVNil) && this instanceof TVNil nil ) return nil._unify_nil(that,test);

    // If 'this' and 'that' are different classes, unify both into an error
    if( getClass() != that.getClass() )
      return test ||
        (that instanceof TVErr
         ? that._unify_err(this)
         : this._unify_err(that));

    // Cycle check
    long luid = dbl_uid(that);    // long-unique-id formed from this and that
    TV3 rez = DUPS.get(luid);
    if( rez==that ) return false; // Been there, done that
    assert rez==null;
    DUPS.put(luid,that);        // Close cycles

    if( test ) return ptrue();  // Always progress from here
    // Same classes.   Swap to keep uid low.
    // Do subclass unification.
    if( _uid > that._uid ) { this._unify_impl(that);  find().union(that.find()); }
    else                   { that._unify_impl(this);  that.find().union(find()); }
    return ptrue();
  }

  // Must always return true; used in flow-coding in many places
  abstract boolean _unify_impl(TV3 that);

  // Make this tvar an error
  public boolean unify_err(String msg, TV3 extra, Parse bad, boolean test) {
    if( test ) return ptrue();
    assert DUPS.isEmpty();
    TVErr err = new TVErr();
    err._unify_err(this);
    err.err(msg,extra,bad,false);
    DUPS.clear();
    return ptrue();
  }

  public void _unify_err( String msg, TV3 extra, Parse bad, boolean test) {
    if( test ) return;
    TVErr err = new TVErr();
    err._unify_err(this);
    err.err(msg,extra,bad,false);
  }

  // Neither side is a TVErr, so make one
  boolean _unify_err(TV3 that) {
    assert !(this instanceof TVErr) && !(that instanceof TVErr);
    TVErr terr = new TVErr();
    return terr._unify_err(this) | terr._unify_err(that);
  }

  // -------------------------------------------------------------
  // Make a (lazy) fresh copy of 'this' and unify it with 'that'.  This is
  // the same as calling 'fresh' then 'unify', without the clone of 'this'.
  // Returns progress.

  // This is a cycle-aware recursive descent structure walker, done in a
  // tik-tok style.  Common work is in _fresh_unify, which then calls subclass
  // specific work in _fresh_unify_impl, which recursively calls back into
  // _fresh_unify.
  
  // Example: 'this' == { A B -> A }, 'that' = { X Y -> Y }
  // After fresh unify 'this' is ALWAYS unchanged, but X and Y are forced to be
  // unified because 'this' return is the same as arg0, and 'that' return is
  // the same as arg1.  SO 'that' == { XY XY -> XY }
  //
  // Also, future changes to either A or B have to be reflected in XY, which is
  // the job of delay_fresh.

  
  static private final IdentityHashMap<TV3,TV3> VARS = new IdentityHashMap<>();
  // A per-fresh-unify DelayFresh
  static TVExpanding.DelayFresh FRESH_ROOT;

  public boolean fresh_unify( FreshNode frsh, TV3[] nongen, TV3 that, boolean test ) {
    if( this==that ) return false;
    assert VARS.isEmpty() && DUPS.isEmpty() && FRESH_ROOT ==null;
    FRESH_ROOT = new TVExpanding.DelayFresh(this,that,frsh,nongen);
    boolean progress = _fresh_unify(that,test);
    VARS.clear();  DUPS.clear();
    FRESH_ROOT = null;
    return progress;
  }

  boolean _fresh_unify( TV3 that, boolean test ) {
    assert !unified() && !that.unified();

    // Check for cycles
    TV3 prior = vget();
    if( prior!=null )                 // Been there, done that
      return prior._unify(that,test); // Also, 'prior' needs unification with 'that'

    // Must check this after the cyclic check, in case the 'this' is cyclic
    if( this==that ) return false;

    // Famous 'occurs-check': In the non-generative set, so do a hard unify,
    // not a fresh-unify.
    if( nongen_in() ) return vput(that,_unify(that,test));

    // LHS leaf, RHS is unchanged but goes in the VARS
    if( this instanceof TVLeaf lf ) {
      if( !test ) lf.add_delay_fresh();
      return vput(that,false);
    }
    if( that instanceof TVLeaf ) { // RHS is a tvar; union with a deep copy of LHS
      if( test ) return true;
      // Must call _fresh first to trigger vcrisscross.
      // This handles the case where 'that' is a Leaf and appears inside of 'this'.
      TV3 frsh = _fresh();
      that.vcrisscross(test);
      return that.union(frsh);
    }

    //// Special handling for nilable
    //if( !(that instanceof TVNil) && this instanceof TVNil nil ) return vput(that,nil._unify_nil_l(that,test));
    //if( !(this instanceof TVNil) && that instanceof TVNil nil ) return vput(nil._unify_nil_r(this,test),ptrue());

    // Two unrelated classes usually make an error
    if( getClass() != that.getClass() )
      return that instanceof TVErr terr
        ? terr._fresh_unify_err_fresh(this,test)
        : this._fresh_unify_err      (that,test);

    // Progress on parts
    boolean progress = false;
    if( _may_nil && !that._may_nil ) {
      if( test ) return ptrue();
      progress = that._may_nil = ptrue();
    }

    // Early set, to stop cycles
    vput(that,progress);

    // Do subclass unification.
    return _fresh_unify_impl(that,test) | progress;
  }

  // Generic field by field
  boolean _fresh_unify_impl(TV3 that, boolean test) {
    assert !unified() && !that.unified();
    boolean progress = false;
    if( _args != null ) {
      for( int i=0; i<_args.length; i++ ) {
        if( _args[i]==null ) continue; // Missing LHS is no impact on RHS
        assert this.getClass()==that.getClass();
        assert !unified();      // If LHS unifies, VARS is missing the unified key
        TV3 lhs = arg(i);
        if( i<that._args.length ) {
          TV3 rhs = that.arg(i);  // Never null
          // Check for a cycle from the Fresh side to the That side.
          // If found, need to unify (not fresh).
          progress |= rhs.vcrisscross(test);
          progress |= lhs._fresh_unify(rhs,test);
        } else {
          progress |= _fresh_missing_rhs(that,i,test);
        }
        that = that.find();
      }
      if( progress && test ) return progress;
      // Extra args in RHS
      for( int i=_args.length; i<that._args.length; i++ )
        throw TODO();
    } else assert that._args==null;
    return progress;
  }

  private boolean vput(TV3 that, boolean progress) {
    VARS.put(this,that);
    VARS.put(that,that);
    return progress;
  }

  TV3 vget() {
    assert !unified();
    TV3 val = VARS.get(this);
    if( val!=null && val.unified() )
      VARS.put(this,val=val.find());
    return val;
  }
  
  boolean vcrisscross(boolean test) {
    // Check for a cycle from the Fresh side to the That side.
    // If found, need to unify (not fresh).
    TV3 cyclic = vget();
    return cyclic !=null && this != cyclic && cyclic._unify(this,test);
  }
  
  // This is fresh, and neither is a TVErr, and they are different classes
  boolean _fresh_unify_err(TV3 that, boolean test) {
    assert !(this instanceof TVErr) && !(that instanceof TVErr);
    assert this.getClass() != that.getClass();
    if( test ) return ptrue();
    TVErr terr = new TVErr();
    return terr._fresh_unify_err_fresh(this,test) | terr._unify_err(that);
  }

  // This is fresh, and RHS is missing.  Possibly Lambdas with missing arguments
  boolean _fresh_missing_rhs(TV3 that, int i, boolean test) {
    if( test ) return ptrue();

    //if( !that.unify_miss_fld(key,work) )
    //  return false;
    //add_deps_work(work);
    //return true;
    throw TODO();
  }

  // -----------------
  // Return a fresh copy of 'this'
  public TV3 fresh() {
    assert VARS.isEmpty();
    assert FRESH_ROOT ==null;
    TV3 rez = _fresh();
    VARS.clear();
    return rez;
  }

  public TV3 fresh(FreshNode ignore, TV3[] nongen) {
    assert VARS.isEmpty();
    assert FRESH_ROOT ==null;
    FRESH_ROOT = new TVExpanding.DelayFresh(this,null,null,nongen);
    TV3 rez = _fresh();
    VARS.clear();
    FRESH_ROOT = null;
    return rez;
  }
  
  TV3 _fresh() {
    assert !unified();
    TV3 rez = vget();
    if( rez!=null ) return rez; // Been there, done that
    // Unlike the original algorithm, to handle cycles here we stop making a
    // copy if it appears at this level in the nongen set.  Otherwise, we'd
    // clone it down to the leaves - and keep all the nongen leaves.
    // Stopping here preserves the cyclic structure instead of unrolling it.
    if( nongen_in() || this==TVPtr.PTRCLZ ) {
      vput(this,true);
      return this;
    }

    // Structure is deep-replicated
    // BUGS:
    // top-level will fresh-deps unify correctly
    // nested ones tho, will need a new fresh-deps from old to new
    TV3 t = copy();
    add_delay_fresh();          // Related via fresh, so track updates
    vput(t,true);               // Stop cyclic structure looping

    if( _args!=null )
      for( int i=0; i<t.len(); i++ )
        if( _args[i]!=null )
          t._args[i] = arg(i)._fresh();
    assert !t.unified();
    return t;
  }

  void add_delay_fresh(){}          // Related via fresh, so track updates

  // -----------------
  static final VBitSet ODUPS = new VBitSet();
  boolean nongen_in() {
    if( FRESH_ROOT ==null || FRESH_ROOT._nongen==null ) return false;
    ODUPS.clear();
    TV3[] nongen = FRESH_ROOT._nongen;
    for( int i=0; i<nongen.length; i++ ) {
      TV3 tv3 = nongen[i];
      if( tv3.unified() ) nongen[i] = tv3 = tv3.find();
      if( _occurs_in_type(tv3) )
        return true;
    }
    return false;
  }

  // Does 'this' occur anywhere inside the nested 'x' ?
  boolean _occurs_in_type(TV3 x) {
    assert !unified() && !x.unified();
    if( x==this ) return true;
    if( ODUPS.tset(x._uid) ) return false; // Been there, done that
    if( x._args!=null )
      for( int i=0; i<x.len(); i++ )
        if( x._args[i]!=null && _occurs_in_type(x.arg(i)) )
          return true;
    return false;
  }


  // -------------------------------------------------------------

  // Do a trial unification between this and that.
  // Report back 7 for hard-no, 1 for hard-yes, and 3 for maybe.
  // No change to either side, this is a trial only.
  private static final NonBlockingHashMapLong<String> TDUPS = new NonBlockingHashMapLong<>();
  public int trial_unify_ok(TV3 pat) {
    TDUPS.clear();
    LEAFS.clear();
    return _trial_unify_ok(pat);
  }
  int _trial_unify_ok(TV3 pat) {
    if( this==pat ) return 1; // hard-yes
    assert !unified() && !pat.unified();
    
    // Symmetric test for trial on a pair; only do the trial once (lest we
    // endlessly recurse), and assume a YES here and let the fail happen
    // elsewhere (if any).  Means trials of matching cycles will be a YES.
    long duid = _uid < pat._uid ? dbl_uid(pat) : pat.dbl_uid(this);
    if( TDUPS.putIfAbsent(duid,"")!=null )
      return 1;                 // Visit only once, and assume will resolve

    // Leafs never fail
    if( this instanceof TVLeaf leaf && !(pat  instanceof TVErr) ) return leaf._trial_leaf(pat );
    if( pat  instanceof TVLeaf leaf && !(this instanceof TVErr) ) return leaf._trial_leaf(this);
    // Different classes will also fail
    if( getClass() != pat.getClass() )
      return 7;
    // Subclasses check sub-parts
    return _trial_unify_ok_impl(pat);
  }

  // Subclasses specify on sub-parts
  abstract int _trial_unify_ok_impl( TV3 pat );

  // Leafs get a "free pass" against unrelated classes, but if the same leaf
  // shows up twice, each "free pass" match has to resolve against each other.
  private static final NonBlockingHashMapLong<Ary<TV3>> LEAFS = new NonBlockingHashMapLong<>();
  int _trial_leaf(TV3 pat) {
    Ary<TV3> priors = LEAFS.get(_uid);
    if( priors == null ) {      // No priors?
      LEAFS.put(_uid,new Ary<>(new TV3[]{pat}));
      return 3;                 // Leafs always a maybe
    }
    // Also prior and pattern must unify
    if( priors._len> 1 )
      throw TODO();             // Really?
    return priors.at(0)._trial_unify_ok(pat);
  }

  // -------------------------------------------------------------
  // Debug-only test that 2 types are equivalent up to a UID renaming.
  public static boolean eq(TV3 good, TV3 bad) {
    assert DUPS.isEmpty();
    boolean rez = _eq(good,bad);
    DUPS.clear();
    return rez;
  }

  private static boolean _eq(TV3 good, TV3 bad) {
    assert !good.unified() && !bad.unified();
    if( good == bad ) return true;
    TV3 prior = DUPS.get(good._uid);
    if( prior == bad )
      return true;              // Been there, done that
    if( prior != null )
      return false;             // Mapped wrong way
    DUPS.put(good._uid,bad);
    if( good.getClass() != bad.getClass() )
      return false;             // Wrong mix
    if( good._args== null ) {
      if( bad._args != null ) return false;
    } else {
      int len = good.len();
      if( len!=bad.len() ) return false;
      for( int i=0; i<len; i++ ) {
        if( (good.arg(i)==null && bad.arg(i)==null) )
          continue;
        // Probably need tik-tok to include TVStruct field lookup
        if( !_eq(good.arg(i),bad.arg(i)) )
          return false;
      }
    }
    return true;
  }
  
  // -----------------

  // Recursively add 'n' to 'this' and all children.

  // Stops when it sees 'n'; this closes cycles and short-cuts repeated adds of
  // 'n'.  Requires internal changes propagate internal _deps.
  private static final VBitSet DEPS_VISIT = new VBitSet();
  public boolean deps_add_deep(Node n ) { DEPS_VISIT.clear(); _deps_add_deep(n); return false; }
  public void _deps_add_deep(Node n ) {
    // no progress during bulk testing
    if( NodeUtil.mid_work_assert() ) return;
    if( DEPS_VISIT.tset(_uid) ) return;
    if( _deps==null ) _deps = UQNodes.make(n);
    _deps = _deps.add(n);
    if( _args!=null )
      for( int i=0; i<len(); i++ )
        if( _args[i]!=null )
          arg(i)._deps_add_deep(n);
  }
  public void deps_add(Node n ) {
    // no progress during bulk testing*
    if( n==null ) return;
    if( NodeUtil.mid_work_assert() ) return;
    if( _deps==null ) _deps = UQNodes.make(n);
    _deps = _deps.add(n);
  }

  // Something changed; add the deps to the worklist and clear.
  void _deps_work_clear() {
    if( _deps == null ) return;
    Env.GVN.add_flow(_deps);
    for( Node n : _deps.values() ) if( n instanceof ConNode) n.unelock(); // hash changes
    _deps = null;
  }

  public void reset_deps() { DEPS_VISIT.clear(); _reset_deps(); }
  private void _reset_deps() {
    if( DEPS_VISIT.tset(_uid) ) return;
    if( _deps!=null ) _deps = null;
    if( _args!=null )
      for( int i=0; i<len(); i++ )
        if( _args[i]!=null )
          _args[i]._reset_deps();
  }

  // -----------------
  public static TV3 from_flow(Type t) { return from_flow(t,0); }
  private static TV3 from_flow(Type t, int d) {
    assert d<1000;  d++;        // Stack overflow?
    return switch( t ) {
    case TypeFunPtr tfp ->  tfp.is_full() ? new TVLeaf() // Generic Function Ptr
      : new TVLambda(tfp.nargs(),from_flow(tfp.dsp(),d),from_flow(tfp._ret,d));
    case TypeMemPtr tmp -> {
      if( tmp==TypeMemPtr.STRPTR ) yield new TVBase(tmp);
      TVStruct ts = tmp.is_simple_ptr() ? new TVStruct(true) : (TVStruct)from_flow(tmp._obj,d);
      StoreXNode.unify(tmp._aliases,ts,false);
      yield new TVPtr(tmp._aliases,ts);
    }
    case TypeStruct ts -> {
      int len = ts.len();
      String[] ss = new String[len];
      TV3[] tvs = new TV3[len];
      for( int i=0; i<ts.len(); i++ ) {
        ss [i] = ts.fld(i)._fld;
        tvs[i] = from_flow(ts.fld(i)._t,d);
      }
      yield new TVStruct(ss,tvs,ts._def==Type.ALL);
    }
    case TypeInt ti -> new TVBase(ti);
    case TypeFlt tf -> new TVBase(tf);

    case TypeNil tn -> new TVPtr( BitsAlias.make0(0), new TVStruct(true) );
    case Type tt -> {
      if( tt == Type.ANY || tt == Type.ALL ) yield new TVLeaf();
      throw TODO();
    }
    };

  }

  // Convert a TV3 to a flow Type
  static final NonBlockingHashMapLong<Type> ADUPS = new NonBlockingHashMapLong<>();
  public Type as_flow( Node dep ) {
    ADUPS.clear();
    return Cyclic.install(_as_flow(dep),null);
  }
  abstract Type _as_flow( Node dep );

  // -----------------
  // Args to external functions are widened by root callers.
  // States are: never visited & no_widen, visited & no_widen, visited & widen
  // Root is set to visited & no widen.
  public boolean widen( byte widen, boolean test ) {
    assert !unified();
    if( !WIDEN ) return false;
    if( _widen>=widen )  return false;
    if( test ) return ptrue();
    _widen = widen;
    _widen(widen);
    return ptrue();
  }
  // Used to initialize primitives
  public void set_widen() { _widen=2; }
  abstract void _widen( byte widen );

  // -----------------
  // True if these two can exactly unify and never not-unify (which means:
  // no-Leafs, as these can expand differently
  static final NonBlockingHashMapLong<String> EXHIT = new NonBlockingHashMapLong<>();
  public boolean exact_unify_ok(TV3 tv3) {
    EXHIT.clear();
    return _exact_unify_ok(tv3);
  }
  boolean _exact_unify_ok(TV3 tv3) {
    if( this==tv3 ) return true;
    assert !unified() && !tv3.unified();
    long duid = dbl_uid(tv3);
    if( EXHIT.get(duid) != null ) return true;
    EXHIT.put(duid,"");
    if( getClass() != tv3.getClass() ) return false;
    if( !_exact_unify_impl(tv3) ) return false;
    if( _args==tv3._args ) return true;
    if( _args==null || tv3._args==null ) return false;
    if( len()!=tv3.len() ) return false;
    for( int i=0; i<len(); i++ )
      if( arg(i)!=null && !arg(i)._exact_unify_ok(tv3.arg(i)) )
        return false;
    return true;
  }
  abstract boolean _exact_unify_impl(TV3 tv3);

  // -----------------
  // Glorious Printing

  // Look for dups, in a tree or even a forest (which Syntax.p() does).  Does
  // not rollup edges, so that debug printing does not have any side effects.
  public final VBitSet get_dups(boolean debug) { return _get_dups(new VBitSet(),new VBitSet(),debug,false); }
  public final VBitSet _get_dups(VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    // Skip dups checks inside common primitives
    if( _uf==null && this instanceof TVStruct clzz && !prims &&
        (clzz.is_int_clz() || clzz.is_flt_clz() || clzz.is_str_clz()) )
      return dups;
    if( visit.tset(_uid) )
      { dups.set(debug_find()._uid); return dups; }
    // Dup count unified and not the args
    return _uf==null
      ? _get_dups_impl(visit,dups,debug,prims) // Subclass specific dup counting
      : _uf._get_dups (visit,dups,debug,prims);
  }
  public VBitSet _get_dups_impl(VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    if( _args != null )
      for( TV3 tv3 : _args )  // Edge lookup does NOT 'find()'
        if( tv3!=null )
          tv3._get_dups(visit,dups,debug,prims);
    return dups;
  }

  public final String p() { VCNT=0; VNAMES.clear(); return str(new SB(), null, null, false, false ).toString(); }
  private static int VCNT;
  private static final NonBlockingHashMapLong<String> VNAMES = new NonBlockingHashMapLong<>();

  @Override public final String toString() { return str(new SB(), null, null, true, false ).toString(); }

  public final SB str(SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    if( visit==null ) {
      assert dups==null;
      _get_dups(visit=new VBitSet(),dups=new VBitSet(),debug,prims);
      visit.clear();
    }
    return _str(sb,visit,dups,debug,prims);
  }

  // Fancy print for Debuggers - includes explicit U-F re-direction.
  // Does NOT roll-up U-F, has no side effects.
  SB _str(SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    boolean dup = dups.get(_uid);
    if( !debug && unified() ) return find()._str(sb,visit,dups,debug,prims);
    if( unified() || this instanceof TVLeaf ) {
      vname(sb,debug,true);
      return unified() ? _uf._str(sb.p(">>"), visit, dups, debug, prims) : sb;
    }
    // Dup printing for all but bases (which are short, just repeat them)
    boolean is_base = this instanceof TVBase;
    if( dup && (debug || !is_base) ) {
      vname(sb,debug,false);           // Leading V123
      if( visit.tset(_uid) && !is_base ) return sb; // V123 and nothing else
      sb.p(':');                        // V123:followed_by_type_descr
    } else {
      //if( visit.tset(_uid) ) return sb;  // Internal missing dup bug?
    }
    if( debug && _widen==1 ) sb.p('+');
    if( debug && _widen==2 ) sb.p('!');
    return _str_impl(sb,visit,dups,debug,prims);
  }

  // Generic structural TV3
  SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    sb.p(getClass().getSimpleName()).p("( ");
    if( _args!=null )
      for( TV3 tv3 : _args )
        tv3._str(sb,visit,dups,debug,prims).p(" ");
    return sb.unchar().p(")");
  }

  // Pick a nice tvar name.  Generally: "A" or "B" or "V123" for leafs,
  // "X123" for unified but not collapsed tvars.
  private void vname( SB sb, boolean debug, boolean uni_or_leaf) {
    final boolean vuid = debug && uni_or_leaf;
    sb.p(VNAMES.computeIfAbsent((long) _uid,
                                (k -> (vuid ? ((unified() ? "X" : "V") + k) : ((++VCNT) - 1 + 'A' < 'V' ? ("" + (char) ('A' + VCNT - 1)) : ("Z" + VCNT))))));
  }

  // Debugging tool
  TV3 f(int uid) { return _find(uid,new VBitSet()); }
  private TV3 _find(int uid, VBitSet visit) {
    if( visit.tset(_uid) ) return null;
    if( _uid==uid ) return this;
    if( _uf!=null ) return _uf._find(uid,visit);
    if( _args==null ) return null;
    for( TV3 arg : _args )
      if( arg!=null && (arg=arg._find(uid,visit)) != null )
        return arg;
    return null;
  }

  // Shallow clone of fields & args.
  public TV3 copy() {
    try {
      assert !unified();
      TV3 tv3 = (TV3)clone();
      tv3._uid = uid();
      tv3._args = _args==null ? null : _args.clone();
      return tv3;
    } catch(CloneNotSupportedException cnse) {throw TODO();}
  }

  // Initial state after loading e.g. primitives.
  public static int _INIT0_CNT = 99999;
  public static void init0() {
    _INIT0_CNT = CNT;
  }
  public static void reset_to_init0() {
    CNT=_INIT0_CNT;
    TVStruct.reset_to_init0();
    TVExpanding.reset_to_init0();
  }
}
