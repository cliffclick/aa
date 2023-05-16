package com.cliffc.aa.tvar;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.ConNode;
import com.cliffc.aa.node.FreshNode;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;

import java.util.IdentityHashMap;

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

abstract public class TV3 implements Cloneable {
  public static final boolean WIDEN = true, WIDEN_FRESH=false; // WIDEN currently turned off
  
  private static int CNT=1;
  public int _uid=CNT++; // Unique dense int, used in many graph walks for a visit bit

  // Disjoint Set Union set-leader.  Null if self is leader.  Not-null if not a
  // leader, but pointing to a chain leading to a leader.  Rolled up to point
  // to the leader in many, many places.  Classic U-F cost model.
  TV3 _uf;

  // Outgoing edges for structural recursion.
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
  public TV3 find() {
    TV3 leader = _find0();
    // Additional read-barrier for TVNil to collapse nil-of-something
    if( !(leader instanceof TVNil tnil) ) return leader;
    TV3 nnn = leader.arg(0);
    if( nnn instanceof TVLeaf ) return leader; // No change
    nnn = nnn.find_nil();
    leader.union(nnn);
    return nnn;
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
    while( u!=leader ) { TV3 next = u._uf; u._uf=leader; u=next; }
    return leader;
  }

  // Bases return the not-nil base; pointers return the not-nil pointer.
  // Nested nils collapse.
  TV3 find_nil() { throw unimpl(); }

  // Fetch a specific arg index, with rollups
  public TV3 arg( int i ) {
    assert !unified();          // No body nor outgoing edges in non-leaders
    TV3 arg = _args[i];
    if( arg==null ) return null;
    TV3 u = arg.find();
    return u==arg ? u : (_args[i]=u);
  }

  // Fetch a specific arg index, withOUT rollups
  public TV3 debug_arg( int i ) { return _args[i].debug_find(); }

  public int len() { return _args.length; }

  abstract int eidx();
  public TVStruct as_struct() { throw unimpl(); }
  public TVLambda as_lambda() { throw unimpl(); }
  public TVBase   as_int   () { throw unimpl(); }
  public TVBase   as_flt   () { throw unimpl(); }
  public TVNil    as_nil   () { throw unimpl(); }

  private long dbl_uid(TV3 t) { return dbl_uid(t._uid); }
  private long dbl_uid(long uid) { return ((long)_uid<<32)|uid; }

  TV3 strip_nil() { _may_nil = false; return this; }

  // Set may_nil flag.  Return progress flag.
  // Set an error if both may_nil and use-nil.
  boolean add_may_nil(boolean test) {
    if( _may_nil ) return false;   // No change
    if( test ) return true;        // Will be progress
    if( _use_nil ) throw unimpl(); // unify_errs("May be nil",work);
    return (_may_nil=true);        // Progress
  }
  // Set use_nil flag. Set an error if both may_nil and use-nil.
  void add_use_nil() {
    if( !_use_nil ) {
      _use_nil=true;                 // Progress
      if( _may_nil ) throw unimpl(); // unify_errs("May be nil",work);
    }
  }

  // -----------------
  // U-F union; this becomes that; returns 'that'.
  // No change if only testing, and reports progress.
  final boolean union(TV3 that) {
    if( this==that ) return false;
    assert !unified() && !that.unified(); // Cannot union twice
    if( _may_nil ) that.add_may_nil(false);
    if( _use_nil ) that.add_use_nil();
    if( that._may_nil && that._use_nil ) throw unimpl();
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
  static NonBlockingHashMapLong<TV3> DUPS = new NonBlockingHashMapLong<>();
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

    // Nil can unify with a non-nil anything, typically
    if( !(this instanceof TVNil) && that instanceof TVNil nil ) return nil._unify_nil(this,test);
    if( !(that instanceof TVNil) && this instanceof TVNil nil ) return nil._unify_nil(that,test);

    // If 'this' and 'that' are different classes, unify both into an error
    if( getClass() != that.getClass() ) {
      if( test ) return true;
      return that instanceof TVErr
        ? that._unify_err(this)
        : this._unify_err(that);
    }

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

  // Make this tvar an error
  public boolean unify_err(String msg, TV3 extra, boolean test) {
    if( test ) return true;
    assert DUPS.isEmpty();
    TVErr err = new TVErr();
    err._unify_err(this);
    err.err(msg,extra,false);
    DUPS.clear();
    return true;
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
  static private final IdentityHashMap<TV3,TV3> VARS = new IdentityHashMap<>();
  // A per-fresh-unify DelayFresh
  static TVExpanding.DelayFresh FRESH_ROOT;

  public boolean fresh_unify( FreshNode frsh, TV3 that, TV3[] nongen, boolean test ) {
    if( this==that ) return false;
    assert VARS.isEmpty() && DUPS.isEmpty() && FRESH_ROOT ==null;
    FRESH_ROOT = new TVExpanding.DelayFresh(this,that,nongen,frsh);
    boolean progress = _fresh_unify(that,test);
    VARS.clear();  DUPS.clear();
    FRESH_ROOT = null;
    return progress;
  }

  boolean _fresh_unify( TV3 that, boolean test ) {
    assert !unified() && !that.unified();

    // Check for cycles
    TV3 prior = VARS.get(this);
    if( prior!=null )                        // Been there, done that
      return prior.find()._unify(that,test); // Also, 'prior' needs unification with 'that'

    // Must check this after the cyclic check, in case the 'this' is cyclic
    if( this==that ) return false;

    // Famous 'occurs-check': In the non-generative set, so do a hard unify,
    // not a fresh-unify.
    if( nongen_in() ) return vput(that,_unify(that,test));

    // LHS leaf, RHS is unchanged but goes in the VARS
    if( this instanceof TVLeaf lf ) { if( !test ) lf.add_delay_fresh(); return vput(that,false); }
    if( that instanceof TVLeaf lf ) // RHS is a tvar; union with a deep copy of LHS
      return test || vput(that,that.union(_fresh()));

    // Special handling for nilable
    if( !(that instanceof TVNil) && this instanceof TVNil nil ) return vput(that,nil._unify_nil_l(that,test));
    if( !(this instanceof TVNil) && that instanceof TVNil nil ) return vput(nil._unify_nil_r(this,test),true);

    // Two unrelated classes make an error
    if( getClass() != that.getClass() )
      return that instanceof TVErr terr
        ? terr._fresh_unify_err_fresh(this,test)
        : this._fresh_unify_err      (that,test);

    boolean progress = false;

    // Progress on parts
    if( _may_nil && !that._may_nil ) {
      if( test ) return true;
      progress = that._may_nil = true;
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
        TV3 lhs = arg(i);
        TV3 rhs = i<that._args.length ? that.arg(i) : null;
        progress |= rhs == null // Missing RHS?
          ? _fresh_missing_rhs(that,i,test)
          : lhs._fresh_unify(rhs,test);
        assert !unified();      // If LHS unifies, VARS is missing the unified key
        that = that.find();
      }
      if( progress && test ) return true;
      // Extra args in RHS
      for( int i=_args.length; i<that._args.length; i++ )
        throw unimpl();
    } else assert that._args==null;
    return progress;
  }

  private boolean vput(TV3 that, boolean progress) { VARS.put(this,that); return progress; }

  // This is fresh, and neither is a TVErr, and they are different classes
  boolean _fresh_unify_err(TV3 that, boolean test) {
    assert !(this instanceof TVErr) && !(that instanceof TVErr);
    assert this.getClass() != that.getClass();
    if( test ) return true;
    TVErr terr = new TVErr();
    return terr._fresh_unify_err_fresh(this,test) | terr._unify_err(that);
  }

  // This is fresh, and RHS is missing.  Possibly Lambdas with missing arguments
  boolean _fresh_missing_rhs(TV3 that, int i, boolean test) {
    if( test ) return true;

    //if( !that.unify_miss_fld(key,work) )
    //  return false;
    //add_deps_work(work);
    //return true;
    throw unimpl();
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

  TV3 _fresh() {
    assert !unified();
    TV3 rez = VARS.get(this);
    if( rez!=null ) return rez.find(); // Been there, done that
    // Unlike the original algorithm, to handle cycles here we stop making a
    // copy if it appears at this level in the nongen set.  Otherwise, we'd
    // clone it down to the leaves - and keep all the nongen leaves.
    // Stopping here preserves the cyclic structure instead of unrolling it.
    if( nongen_in() ) {
      VARS.put(this,this);
      return this;
    }

    // Structure is deep-replicated
    // BUGS:
    // top-level will fresh-deps unify correctly
    // nested ones tho, will need a new fresh-deps from old to new
    TV3 t = copy();
    add_delay_fresh();          // Related via fresh, so track updates
    VARS.put(this,t);           // Stop cyclic structure looping
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
  // Report back false if any error happens, or true if no error.
  // No change to either side, this is a trial only.
  // Collect leafs and bases on the pattern (this).
  private static final NonBlockingHashMapLong<TV3> TDUPS = new NonBlockingHashMapLong<>();
  public boolean trial_unify_ok(TV3 that, boolean extras) {
    TDUPS.clear();
    return _trial_unify_ok(that, extras);
  }
  boolean _trial_unify_ok(TV3 that, boolean extras) {
    if( this==that )             return true; // No error
    assert !unified() && !that.unified();
    long duid = dbl_uid(that._uid);
    if( TDUPS.putIfAbsent(duid,this)!=null )
      return true;              // Visit only once, and assume will resolve
    if( this instanceof TVLeaf leaf ) return Resolvable.add_pat_leaf(leaf); // No error
    if( that instanceof TVLeaf leaf ) return Resolvable.add_pat_leaf(leaf); // No error
    // Nil can unify with ints,flts,ptrs
    if( this instanceof TVNil ) return this._trial_unify_ok_impl(that,extras);
    if( that instanceof TVNil ) return that._trial_unify_ok_impl(this,extras);
    // Different classes always fail
    if( getClass() != that.getClass() ) return false;
    // Subclasses check sub-parts
    return _trial_unify_ok_impl(that, extras);
  }

  // Subclasses specify on sub-parts
  boolean _trial_unify_ok_impl( TV3 that, boolean extras ) { throw unimpl(); }

  // -----------------

  // Recursively add 'n' to 'this' and all children.

  // Stops when it sees 'n'; this closes cycles and short-cuts repeated adds of
  // 'n'.  Requires internal changes propagate internal _deps.
  private static final VBitSet DEPS_VISIT = new VBitSet();
  public boolean deps_add_deep(Node n ) { DEPS_VISIT.clear(); _deps_add_deep(n); return false; }
  public void _deps_add_deep(Node n ) {
    if( DEPS_VISIT.tset(_uid) ) return;
    if( _deps==null ) _deps = UQNodes.make(n);
    _deps = _deps.add(n);
    if( _args!=null )
      for( int i=0; i<len(); i++ )
        if( _args[i]!=null )
          arg(i)._deps_add_deep(n);
  }
  public void deps_add(Node n ) {
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

  // -----------------
  public static TV3 from_flow(Type t) {
    return switch( t ) {
    case TypeFunPtr tfp -> {
      if( !tfp.is_full() ) throw unimpl(); //return new TVLeaf(); // TODO
      yield new TVLeaf(); // Generic Function Ptr
    }
    case TypeMemPtr tmp -> new TVPtr(tmp._aliases,(TVStruct)from_flow(tmp._obj));
    case TypeStruct ts -> {
      // need to handle CLZ in slot 0
      int len = ts.len();
      TypeFld fclz = ts.get(".");
      if( fclz==null ) len++;
      
      String[] ss = new String[len];
      TV3[] tvs = new TV3[len];
      ss [0] = ".";
      tvs[0] = fclz==null ? new TVLeaf() : from_flow(fclz._t);
      for( int i=0,j=1; i<ts.len(); i++ ) {
        TypeFld fld = ts.fld(i);
        if( !Util.eq(fld._fld,".") ) {
          ss [j  ] = fld._fld;
          tvs[j++] = from_flow(fld._t);
        }
      }
      yield new TVStruct(ss,tvs,ts._def==Type.ANY);
    }
    case TypeInt ti -> TVBase.make(ti);
    case TypeFlt tf -> TVBase.make(tf);
    case TypeNil tn -> tn == TypeNil.NIL
      ? new TVNil( new TVLeaf() )
      : TVBase.make(tn);
    case Type tt -> {
      if( tt == Type.ANY || tt == Type.ALL ) yield new TVLeaf();
      throw unimpl();
    }
    };

  }

  // Convert a TV3 to a flow Type
  static final NonBlockingHashMapLong<Type> ADUPS = new NonBlockingHashMapLong<>();
  public Type as_flow( Node dep ) {
    ADUPS.clear();
    return _as_flow(dep);
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
    if( test ) return true;
    _widen = widen;
    _widen(widen);
    return true;
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
  public VBitSet get_dups(boolean debug) { return _get_dups(new VBitSet(),new VBitSet(),debug,false); }
  public VBitSet _get_dups(VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
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
  // Does NOT roll-up U-F, has no side-effects.
  SB _str(SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    boolean dup = dups.get(_uid);
    if( !debug && unified() ) return find()._str(sb,visit,dups,debug,prims);
    if( debug && !unified() && _widen==1 ) sb.p('+');
    if( debug && !unified() && _widen==2 ) sb.p('!');
    if( unified() || this instanceof TVLeaf ) {
      vname(sb,debug,true);
      return unified() ? _uf._str(sb.p(">>"), visit, dups, debug, prims) : sb;
    }
    // Dup printing for all but bases (which are short, just repeat them)
    if( dup && (debug || !(this instanceof TVBase)) ) {
      vname(sb,debug,false);           // Leading V123
      if( visit.tset(_uid) && !(this instanceof TVBase ) ) return sb; // V123 and nothing else
      sb.p(':');                        // V123:followed_by_type_descr
    } else {
      //if( visit.tset(_uid) ) return sb;  // Internal missing dup bug?
    }
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
      TV3 tv3 = (TV3)clone();
      tv3._uid = CNT++;
      tv3._args = _args==null ? null : _args.clone();
      return tv3;
    } catch(CloneNotSupportedException cnse) {throw unimpl();}
  }

  public static void reset_to_init0() {
    CNT=0;
    TVField.reset_to_init0();
    TVStruct.reset_to_init0();
    TVExpanding.reset_to_init0();
  }
}
