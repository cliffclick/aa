package com.cliffc.aa.tvar;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;
import org.jetbrains.annotations.NotNull;

import java.util.*;

import static com.cliffc.aa.AA.*;

/** Hindley-Milner based type variables.
 *
 * TV2s unify (ala Tarjan Union-Find), and can have structure such as "{ A -> B
 * }" or "@{ x = A, y = A }".  TV2s includes polymorphic structures and fields
 * (structural typing not duck typing), polymorphic nil-checking and an error
 * type.  TV2 types fully support recursive types.
 *
 * TV2 Bases include anything from the GCP lattice, and are generally sharper
 * than e.g. 'int'.  Bases with values of '3' and "abc" are fine.  These are
 * widened to the normal HM types if passed to any function; they remain sharp
 * if returned or passed to primitives.  Functions include the set of FIDXs
 * used in the unification; this set is generally less precise than that from
 * GCP.  Function arguments that escape have their GCP type widened "as if"
 * called from the most HM-general legal call site; otherwise GCP assumes
 * escaping functions are never called and their arguments have unrealistic
 * high flow types.
 *
 * Unification typically makes many temporary type-vars and immediately unifies
 * them.  For efficiency, this algorithm checks to see if unification requires
 * an allocation first, instead of just "allocate and unify".  The major place
 * this happens is identifiers, which normally make a "fresh" copy of their
 * type-var, then unify.  I use a combined "make-fresh-and-unify" unification
 * algorithm there.  It is a structural clone of the normal unify, except that
 * it lazily makes a fresh-copy of the left-hand-side on demand only; typically
 * discovering that no fresh-copy is required.
 *
 * To engineer and debug the algorithm, the unification step includes a flag to
 * mean "actually unify, and report a progress flag" vs "report if progress".
 * The report-only mode is aggressively asserted for in the main loop; all
 * Syntax elements that can make progress are asserted as on the worklist.
 *
 * See HM.java for the prototype this is based from.
 *
 *
 * Mapping from a classic lambda-calculus AST to Sea-of-Nodes
 *
 * - Ids: HM identifiers are SSA edges in the Sea-of-Nodes.  A 'FreshNode' is
 *   used explicitly, for a id reference needing a 'fresh_unify'.  These appear
 *   for each display reference and reading ParmNodes to init the display.
 *   Other typical 'aa' ids are actually Loads agains the display.
 * - Lambda: FunPtrNodes (not FunNodes), which includes the display argument.
 * - Apply: CallEpiNodes (not CallNodes)
 * - Let: Strictly used to make new Displays at function headers and the parse
 *   start.  Normal 'aa' variables are field loads against the display.
 * - Struct: NewObjNode
 * - Field: Loads and Stores.
 * - If: IfNode
 * - NotNil: Cast of not-nil.  Cast is used for other operations but is only
 *   polymorphic for nil.
 */


public class TV2 {
  // Unique ID
  private static int UID=1;
  public final int _uid;
  // - "Args", "Ret", "Fun", "Obj", "@{}".  A structural tag for the H-M
  // "type", these have to be equal during unification; their Keys in _args are
  // unioned and equal keys are unified
  // - "Nil", with argument "?"
  // - "Base" - some constant Type, Base Types MEET when unified.
  // - "Err": a dead Node or a Type.ANY ConNode, and a dead TV2.  Unifies with
  // everything, wins all unifications, and has no structure.
  private String _name;


  // Structural parts to unify with, or null.
  // If Leaf or Error, then null.
  // If unified, contains the single key ">>".
  // If Base   , contains the single key "Base".
  // If Nil    , contains the single key "?"
  // If Lambda , contains keys "0","1","2" for args or "ret" for return.
  // If Apply  , contains keys "fun" and "0","1","2" for args
  // If Struct , contains keys for the field labels.  No display.  Is null if no fields.
  NonBlockingHashMap<String,TV2> _args;

  // A dataflow type or null.
  // If Leaf, or unified or Nil or Apply, then null.
  // If Base, then the flow type.
  // If Lambda, then a TFP and the BitsFun   matters.
  // If Struct, then a TMP and the BitsAlias matters.
  // If Error, then a TypeStr with the error (not a TMP to a TS).
  public Type _type;

  private boolean _open; // Structs allow more fields.  Not quite the same as TypeStruct._open field.

  // Theory: when positive polarity and negative polarity, bases need to widen.
  //private boolean _is_func_input;

  // U-F algo.  Only set when unified, monotonic null->unification_target.
  // Can change again to shorten unification changes.
  private TV2 _unified;

  // Set of dependent CallEpiNodes, to be re-worklisted if the called function changes TV2.
  private UQNodes _deps;

  // Debug only.  Set of unioned Nodes.  null for empty.  Helpful to track where TV2s come from.
  private UQNodes _ns;     //
  private @NotNull final String _alloc_site; // Creation site; used to track excessive creation.

  // Track allocation statistics
  static private class ACnts { int _malloc, _unified, _free; }
  static private final HashMap<String,ACnts> ALLOCS = new HashMap<>(); // Counts at alloc sites

  // Common constructor
  private TV2(@NotNull String name, NonBlockingHashMap<String,TV2> args, Type type, UQNodes ns, @NotNull String alloc_site) {
    _uid = UID++;
    _name = name;
    _args = args;
    _type = type;
    _deps = null;               // Lazy added
    _ns = ns;
    _alloc_site = alloc_site;
    ACnts ac = ALLOCS.computeIfAbsent(alloc_site,e -> new ACnts());
    ac._malloc++;
  }

  // Accessors
  public boolean is_unified() { return _unified!=null; }
  public boolean isa(String s){ return Util.eq(_name,s); }
  public boolean is_tvar   () { return _args!=null; } // Excludes unified,base,dead,free; includes nil,fun,struct
  // Flat TV2s; no args.
  public boolean is_free   () { return isa("Free"   ); } // Allocated and then freed.  TBD if this pays off
  public boolean is_err    () { return isa("Err"    ); } // Error; exciting if not eventually dead
  public boolean is_base   () { return isa("Base"   ); } // Some base constant (no internal TV2s)
  public boolean is_leaf   () { return isa("Leaf"   ); } // Classic H-M leaf type variable, probably eventually unifies
  // Structural TV2s; has args
  public boolean is_nil() { return isa("Nil"    ); } // Some nilable TV2
  public boolean is_fun    () { return isa("->"     ); } // A function, arg keys are numbered from ARG_IDX, and the return key is "ret"
  public boolean is_struct () { return isa("@{}"    ); } // A struct, keys are field names
  public boolean is_ary    () { return isa("Ary"    ); } // A array, key elem is element type
  public boolean is_str    () { return isa("Str"    ); } // A string
  //public TV2 get_unified() { assert is_unified(); return _unified; }
  public String name() { return _name; }

  // Get at a key, withOUT U-F rollup.  Used for debug printing.
  TV2 _get( String key ) { return _args==null ? null : _args.get(key); }
  // Get at a key, with U-F rollup
  public TV2 get( String key ) {
    TV2 tv = _get(key);
    if( tv==null ) return null;
    TV2 tv2 = tv.find();
    return tv==tv2 ? tv : args_put(key,tv2);
  }
  TV2 debug_get( String key ) {
    TV2 tv = _get(key);
    return tv==null ? null : tv.find();
  }

  // When inserting a new key, propagate deps
  public TV2 args_put(String key, TV2 tv) {
    _args.put(key,tv);          // Pick up a key->tv mapping
    merge_deps(tv);             // tv gets all deps that 'this' has
    return tv;
  }

  // Unify-at a key.  Expect caller already has args
  public boolean unify_at(Node n, String key, TV2 tv2, Work work ) {
    if( is_err() ) return unify(tv2,work);// if i am dead, all my parts are dead, so tv2 is unifying with a dead part
    assert is_tvar() && !tv2.is_unified();
    TV2 old = get(key);
    if( old!=null )
      return old.unify(tv2,work); // This old becomes that
    if( work==null ) return true; // Would add part
    args_put(key,tv2);
    work.add(_deps);
    _ns = _ns.add(n);
    return true;
  }

  // Open to new fields or not
  public boolean open() {
    return _open;
  }

  public Set<String> args() { return _args.keySet(); }
  public int len() { return _args==null ? 0 : _args.size(); }

  // --------------------------------------------
  // Public factories
  // Make a new TV2 attached to a Node.
  public static TV2 make_leaf(Node n, @NotNull String alloc_site) {
    UQNodes ns = n==null ? null : UQNodes.make(n);
    return make_leaf_ns(ns,alloc_site);
  }
  public static TV2 make_leaf_ns(UQNodes ns, @NotNull String alloc_site) {
    TV2 tv2 = new TV2("Leaf",null,null,ns,alloc_site);
    assert tv2.is_leaf() && !tv2.is_base();
    return tv2;
  }
  // Make a new primitive base TV2
  public static TV2 make_base(Node n, Type type, @NotNull String alloc_site) {
    UQNodes ns = n==null ? null : UQNodes.make(n);
    return new TV2("Base",null,type,ns,alloc_site);
  }
  public void set_as_base(Type t) { assert is_leaf(); _name="Base"; _type=t; }
  // Make a new Nil
  public static TV2 make_nil(TV2 notnil, @NotNull String alloc_site) {
    NonBlockingHashMap<String,TV2> args = new NonBlockingHashMap<String,TV2>(){{ put("?",notnil); }};
    return new TV2("Nil",args,Type.XNIL,notnil._ns,alloc_site);
  }
  // Make a new function
  public static TV2 make_fun(Node n, TypeFunPtr fptr, TypeFunSig sig, @NotNull String alloc_site) {
    assert fptr._disp==TypeMemPtr.NO_DISP; // Just for fidxs, arg counts
    assert fptr._nargs==sig.nargs();
    return new TV2("->",new NonBlockingHashMap<String,TV2>(),fptr,UQNodes.make(n),alloc_site);
  }
  public static TV2 make_fun(Node n, Type fptr, NonBlockingHashMap<String,TV2> args, @NotNull String alloc_site) {
    return new TV2("->",args,fptr,UQNodes.make(n),alloc_site);
  }

  // Make a new primitive base TV2
  public static TV2 make_err(Node n, String msg, @NotNull String alloc_site) {
    UQNodes ns = n==null ? null : UQNodes.make(n);
    TV2 tv2 = new TV2("Err",null,TypeStr.con(msg.intern()),ns,alloc_site);
    assert tv2.is_err() && !tv2.is_leaf() && !tv2.is_base();
    return tv2;
  }
  public TV2 miss_field(Node n,String fld,@NotNull String alloc_site) {
    return make_err(n,"Missing field "+fld+" in "+this,alloc_site);
  }

  // Structural constructor, empty
  public static TV2 make(@NotNull String name, Node n, @NotNull String alloc_site ) { return make(name,n,alloc_site,new NonBlockingHashMap<>()); }
  // Structural constructor
  public static TV2 make(@NotNull String name, Node n, @NotNull String alloc_site, NonBlockingHashMap<String,TV2> args) {
    assert args!=null;          // Must have some structure
    TV2 tv2 = new TV2(name,args,null,UQNodes.make(n),alloc_site);
    assert !tv2.is_base() && !tv2.is_leaf();
    return tv2;
  }
  // Structural constructor with address
  public static TV2 make(@NotNull String name, Node n, Type t, @NotNull String alloc_site, NonBlockingHashMap<String,TV2> args) {
    TV2 tv2 = new TV2(name,args,t,UQNodes.make(n),alloc_site);
    assert !tv2.is_base() && !tv2.is_leaf();
    return tv2;
  }
  // Structural constructor from array of TVs
  public static TV2 make(@NotNull String name, Node n, @NotNull String alloc_site, Node... ntvs) {
    assert ntvs!=null;          // Must have some structure
    NonBlockingHashMap<String,TV2> args = new NonBlockingHashMap<>();
    for( int i=0; i<ntvs.length; i++ )
      if( ntvs[i]!=null && ntvs[i].has_tvar() )
        args.put((""+i).intern(),ntvs[i].tvar());
    return make(name,n,alloc_site,args);
  }

  public static TV2 make(@NotNull String name, UQNodes ns, @NotNull String alloc_site ) {
    TV2 tv2 = new TV2(name, new NonBlockingHashMap<>(),null,ns,alloc_site);
    assert !tv2.is_base() && !tv2.is_leaf();
    return tv2;
  }

  // A new struct from a NewObj
  public static TV2 make_struct(NewObjNode n, @NotNull String alloc_site) {
    TV2 tv2 = new TV2("@{}",new NonBlockingHashMap<>(),null,UQNodes.make(n),alloc_site);
    tv2._open = true;           // Start out open
    return tv2;
  }
  // Make a new struct for a field load/store.  Could be an array or struct
  public static TV2 make_open_struct(String name, Node n, Type t, @NotNull String alloc_site, NonBlockingHashMap<String,TV2> args) {
    TV2 tv2 = new TV2(name,args,t,UQNodes.make(n),alloc_site);
    tv2._open = true;           // Start out open
    return tv2;
  }
  // Structural constructor from an array of nodes and keys from a TypeStruct
  public static TV2 make_struct(NewObjNode n, @NotNull String alloc_site, TypeStruct ts, Ary<Node> ntvs) {
    NonBlockingHashMap<String,TV2> args = new NonBlockingHashMap<>();
    for( int i=0; i<ntvs._len; i++ )
      if( ntvs.at(i)!=null )
        args.put(ts.fld_idx(i)._fld,ntvs.at(i).tvar());
    TV2 tv2 = make("@{}",n,alloc_site,args);
    tv2._open = false;          // Closed now; no more fields
    tv2._type = n._tptr;        // Pick up alias info
    return tv2;
  }

  TV2 copy(String alloc_site) {
    TV2 t = new TV2(_name,_args==null ? null : new NonBlockingHashMap<>(),_type,_ns,alloc_site);
    t._deps = _deps;
    t._open = _open;
    return t;
  }

  public static void reset_to_init0() {
    UID=1;
  }
  public void reset(Node n) { if( _ns!=null ) _ns.remove(n._uid); }

  public void free() {
    if( !is_unified() ) ALLOCS.get(_alloc_site)._free++;
    _name = "Free";
    _args = null;
    _type = null;
    _open = false;
    _deps = null;
    _ns   = null;
  }

  // --------------------------------------------
  // Tarjan U-F find, without the roll-up.  Used for debug printing and asserts
  public TV2 debug_find() {
    if( !is_unified() ) return this;
    TV2 top = _unified;
    if( !top.is_unified() ) return top; // Shortcut
    // U-F search, no fixup
    int cnt=0;
    while( top.is_unified() && cnt++<100 ) top = top._unified;
    assert cnt<100;             // Infinite roll-up loop
    return top;
  }

  // Classic Tarjan U-F with rollup
  public TV2 find() {
    TV2 top = _find0();
    return top.is_nil() ? top._find_nil() : top;
  }

  private TV2 _find0() {
    TV2 top = debug_find();
    if( top == this ) return top;
    if( top == _unified ) return top;
    TV2 v = this;               // Rerun, rolling up to top
    while( v != top ) { TV2 next = v._unified; v._unified=top; v = next; }
    return top;
  }

  // Nilable fixup.  nil-of-leaf is OK.  nil-of-anything-else folds into a
  // nilable version of the anything-else.
  @SuppressWarnings("unchecked")
  private TV2 _find_nil() {
    TV2 n = get("?");
    switch( n._name ) {
    case "Leaf":   return this; // Normal default, no change
    case "Nil":                 // Nested nilable; collapse the layer
      _args.put("?",n.get("?"));
      break;

    case "Base":
    case "@{}":
    case "Str":
      // Nested nilable-and-not-leaf, need to fixup the nilable.
      // "this" becomes a shallow copy of the leaf 'n' with XNIL.
      _type = n._type.meet_nil(Type.XNIL);
      _args = n._args==null ? null : (NonBlockingHashMap<String,TV2>)n._args.clone();  // Shallow copy the TV2 fields
      _open = n._open;
      _name = n._name;
      break;
    case "Ary":
    default:
      throw unimpl();
    }

    n.merge_deps(this);         // Copy n._deps into _deps
    n.merge_ns  (this);
    return this;
  }


  // U-F union; 'this' becomes 'that'.  No change if only testing, and reports
  // progress.  If progress and not testing, adds _deps to worklist.
  public boolean union(TV2 that, Work work) {
    assert !is_unified() && !that.is_unified() && !is_err();
    assert !is_err() || that.is_err(); // Become the error, not error become that
    if( this==that ) return false;
    if( work==null ) return true; // All remaining paths make progress
    // Keep the merge of all base types, and add _deps.
    if( !that.is_err() ) {
      if( that._type==null ) that._type = _type;
      else if( _type!=null ) {
        if( _type.getClass()!=that._type.getClass() ) {
          union(make_err(null,"Cannot unify "+this.p()+" and "+that.p(),"union"),work);
          return that.union(find(),work);
        }
        that._type = _type.meet(that._type);
        that._open &= _open;
      }
    }
    //if( _is_func_input ) that.widen_bases();

    // Work all the deps
    that.add_deps_work(work);
    this.add_deps_work(work);      // Any progress, revisit deps
    // Hard union this into that, no more testing.
    return _union(that);
  }
  // Union this into that; this can already be unified (if rolling up).
  // Crush all the extra fields in this, to avoid accidental usage.
  private boolean _union(TV2 that) {
    assert !that.is_unified();
    _unified=that;
    assert is_unified();
    ALLOCS.get(_alloc_site)._unified++;
    merge_deps(that);           // Merge update lists, for future unions
    merge_ns  (that);           // Merge Node list, for easier debugging
    _name = "X"+_uid;
    _args = null;               // Clean out extra state from 'this'
    _open = false;
    _type = null;
    _deps = null;
    _ns   = null;
    return true;
  }

  // U-F union; this is nilable and becomes that.
  // No change if only testing, and reports progress.
  @SuppressWarnings("unchecked")
  boolean unify_nil(TV2 that, Work work) {
    assert is_nil() && !that.is_nil();
    if( work==null ) return true; // Will make progress
    // Clone the top-level struct and make this nilable point to the clone;
    // this will collapse into the clone at the next find() call.
    // Unify the nilable leaf into that.
    TV2 leaf = get("?");  assert leaf.is_leaf();
    TV2 copy = that.copy("unify_nil");
    if( that.is_base() ||
        that.is_struct() ||
        that.isa("Str") ) {
      copy._type = copy._type.join(Type.NSCALR);
      copy._args = that._args==null ? null : (NonBlockingHashMap<String, TV2>)that._args.clone();
    } else
      throw unimpl();
    return leaf._union(copy) | that._union(find());
  }

  // --------------------------------------------
  // Cyclic (structural) equals
  static private final HashMap<TV2,TV2> CDUPS = new HashMap<>();
  public final boolean eq( TV2 that ) {
    assert CDUPS.isEmpty();
    boolean eq = _eq(that);
    CDUPS.clear();
    return eq;
  }
  private boolean _eq( TV2 that) {
    assert !is_unified() && !that.is_unified();
    if( this==that ) return true;
    if( _type != that._type ) return false; // Base types, if present, must match
    if( !Util.eq(_name,that._name) ) return false; // Mismatched tvar names
    if( is_leaf() && that.is_leaf() ) return false; // Mismatched leafs
    if( _args==that._args ) return true; // Same arrays (generally both null)
    if( _args.size() != that._args.size() ) return false;

    // Cycles stall the equal/unequal decision until we see a difference.
    TV2 tc = CDUPS.get(this);
    if( tc!=null )  return tc==that; // Cycle check; true if both cycling the same
    CDUPS.put(this,that);

    // Structural recursion
    for( String key : _args.keySet() ) {
      TV2 lhs =      get(key);  assert lhs!=null;
      TV2 rhs = that.get(key);
      if( rhs==null || !lhs._eq(rhs) ) return false;
    }
    return true;
  }

  // --------------------------------------------
  // Used in the recursive unification process.  During unify detects cycles,
  // to allow cyclic unification.
  private static final NonBlockingHashMapLong<TV2> DUPS = new NonBlockingHashMapLong<>();
  private long dbl_uid(TV2 t) { return dbl_uid(t._uid); }
  private long dbl_uid(long uid) { return ((long)_uid<<32)|uid; }

  // Structural unification.  Both 'this' and that' are the same afterwards.
  // Returns True if progressed.
  public boolean unify(TV2 that, Work work) {
    if( this==that ) return false;
    assert DUPS.isEmpty();
    boolean progress = _unify(that,work);
    DUPS.clear();
    return progress;
  }

  // Classic structural unification, no "fresh".  Unifies 'this' into 'that'.
  // Both 'this' and 'that' are the same afterwards.  Returns true if progress.
  private boolean _unify(TV2 that, Work work) {
    assert !is_unified() && !that.is_unified();
    if( this==that ) return false;

    // Check for simple, non-recursive, unification.
    if( this._args==null && that._args==null ) {
      TV2 lhs=this, rhs=that;
      // Err beats Base beats Leaf
      if(        is_err () ||              // Error beats Base
          (!that.is_err () && is_base()) ) // Base  beats Leaf
        { rhs=this; lhs=that; }            // Swap
      // If tied, keep lower uid
      if( Util.eq(lhs._name,rhs._name) && _uid<that._uid ) { rhs=this; lhs=that; }
      return lhs.union(rhs,work);
    }
    // Any leaf immediately unifies with any non-leaf
    if( this.is_leaf() || that.is_err() ) return this.union(that,work);
    if( that.is_leaf() || this.is_err() ) return that.union(this,work);
    // Special case for nilable union something
    if( this.is_nil() && !that.is_nil() ) return this.unify_nil(that,work);
    if( that.is_nil() && !this.is_nil() ) return that.unify_nil(this,work);

    // Cycle check.
    long luid = dbl_uid(that);  // long-unique-id formed from this and that
    TV2 rez = DUPS.get(luid);
    assert rez==null || rez==that;
    if( rez!=null ) return false; // Been there, done that
    DUPS.put(luid,that);          // Close cycles

    if( work==null ) return true; // Here we definitely make progress; bail out early if just testing

    // Check for mismatched, cannot unify
    if( !Util.eq(_name,that._name) ) {
      TV2 err = make_err(null,"Cannot unify "+this+" and "+that,"unify_fail");
      return union(err,work) & that.union(err,work);
    }
    assert _args!=that._args; // Not expecting to share _args and not 'this'

    // Structural recursion unification, this into that.  Aligned keys unify
    // directly.  Fields in one TV2 and not in the other are put in the result
    // if the other is open, and dropped otherwise.
    NonBlockingHashMap<String,TV2> args = _args;
    for( String key : args.keySet() ) {
      TV2 vthis = get(key); assert vthis!=null;
      TV2 vthat = that.get(key);
      if( vthat==null ) {
        if( that.open() ) that.add_fld(key,vthis,work);
      } else vthis._unify(vthat,work); // Matching fields unify
      if( this.find() != this ) throw unimpl();
      if( that.find() != that ) throw unimpl();
      assert this._args==args;
    }
    // Fields on the RHS are aligned with the LHS also
    for( String key : that._args.keySet() )
      if( args.get(key)==null )
        if( this.open() )  this.add_fld(key,that.get(key),work); // Add to LHS
        else               that.del_fld(key, work);              // Drop from RHS

    if( find().is_err() && !that.is_err() )
      throw unimpl(); // TODO: Check for being equal, cyclic-ly, and return a prior if possible.
    return find().union(that,work);
  }

  // Insert a new field
  public boolean add_fld( String id, TV2 fld, Work work) {
    assert is_struct();
    if( _args==null ) _args = new NonBlockingHashMap<>();
    _args.put(id,fld);
    fld.push_deps(_deps);
    add_deps_work(work);
    return true;
  }
  // Delete a field
  private void del_fld( String fld, Work work) {
    assert is_struct() || is_ary();
    _args.remove(fld);
    if( _args.size()==0 )  _args=null;
    add_deps_work(work);
  }

  // Used in the recursive unification process.  During fresh_unify tracks the
  // mapping from LHS TV2s to RHS TVs.
  private static final HashMap<TV2,TV2> VARS = new HashMap<>();

  // Make a (lazy) fresh copy of 'this' and unify it with 'that'.  This is
  // the same as calling 'fresh' then 'unify', without the clone of 'this'.
  // The TV2[] is used when making the 'fresh' copy for the occurs_check.

  // Returns progress.
  // If work==null, we are testing only and make no changes.
  public boolean fresh_unify(TV2 that, TV2[] vs, Work work) {
    assert VARS.isEmpty() && DUPS.isEmpty();
    boolean progress = _fresh_unify(that,vs,work);
    VARS.clear();  DUPS.clear();
    return progress;
  }

  // Apply 'this' structure on 'that'; no modifications to 'this'.  VARS maps
  // from the cloned LHS to the RHS replacement.
  private boolean _fresh_unify(TV2 that, TV2[] nongen, Work work ) {
    assert !is_unified() && !that.is_unified();

    // Check for cycles
    TV2 prior = VARS.get(this);
    if( prior!=null )         // Been there, done that
      return prior.find()._unify(that,work);  // Also 'prior' needs unification with 'that'
    // Check for equals (internally checks this==that)
    if( eq(that) ) return vput(that,false);

    // Several trivial cases that do not really do any work
    if( that.is_err() ) return vput(that,false); // That is an error, ignore 'this' and no progress
    if( this.is_err() ) return vput(that,_unify(that,work));

    // Famous 'occurs-check', switch to normal unify
    if( nongen_in( nongen ) ) return vput(that,_unify(that,work));

    // LHS leaf, RHS is unchanged but goes in the VARS
    if( this.is_leaf() ) return vput(that,false);
    if( that.is_leaf() )  // RHS is a tvar; union with a deep copy of LHS
      return work==null || vput(that,that.union(_fresh(nongen),work));

    // Bases MEET cons in RHS
    if( is_base() && that.is_base() ) {
      Type mt = _type.meet(that._type);
      if( mt==that._type ) return vput(that,false);
      if( work == null ) return true;
      that._type = mt;
      return vput(that,true);
    }

    // Special handling for nilable
    if( this.is_nil() && !that.is_nil() ) {
      Type mt = that._type.meet_nil(Type.XNIL);
      if( mt == that._type ) return false;
      if( work==null ) return true;
      throw unimpl();
    }

    // That is nilable and this is not
    if( that.is_nil() && !this.is_nil() ) {
      assert is_base() || is_struct();
      if( work==null ) return true;
      TV2 copy = this;
      if( _type.must_nil() ) { // Make a not-nil version
        copy = copy("fresh_unify_vs_nil");
        copy._type = _type.join(Type.NSCALR);
        if( _args!=null ) throw unimpl(); // shallow copy
      }
      boolean progress = copy._fresh_unify(that.get("?"),nongen,work);
      return _type.must_nil() ? vput(that,progress) : progress;
    }

    // Check for being the same structure
    if( !Util.eq(_name,that._name) )
      throw unimpl();

    // Structural recursion unification, lazy on LHS.  Fields in both sides are
    // directly unified.  Fields on one side check to see if the other side is
    // open; if open the field is copied else deleted
    boolean progress = vput(that,false); // Early set, to stop cycles
    for( String key : _args.keySet() ) {
      TV2 lhs =      get(key);  assert lhs!=null;
      TV2 rhs = that.get(key);
      if( rhs==null ) {         // No RHS to unify against
        if( that.open() ) {     // If RHS is open, copy field into it
          if( work==null ) return true; // Will definitely make progress
          progress |= that.add_fld(key,lhs._fresh(nongen), work);
        } // If closed, no copy
      } else {
        progress |= lhs._fresh_unify(rhs,nongen,work);
      }
      if( (that=that.find()).is_err() ) return true;
      if( progress && work==null ) return true;
    }
    // Fields in RHS and not the LHS are also merged; if the LHS is open we'd
    // just copy the missing fields into it, then unify the structs (shortcut:
    // just skip the copy).  If the LHS is closed, then the extra RHS fields
    // are removed.
    if( !open() )
      for( String id : that.args() )      // For all fields in RHS
        if( get(id)==null ) {             // Missing in LHS
          if( work == null ) return true; // Will definitely make progress
          { that._args.remove(id); progress=true; } // Extra fields on both sides are dropped
        }
    that._open &= this._open;

    return progress;
  }

  private boolean vput(TV2 that, boolean progress) { VARS.put(this,that); return progress; }
  private TV2 vput(TV2 that) { VARS.put(this,that); return that; }

  private TV2 fresh(TV2[] nongen) {
    assert VARS.isEmpty();
    TV2 tv2 = _fresh(nongen);
    VARS.clear();
    return tv2;
  }
  private TV2 _fresh(TV2[] nongen) {
    assert !is_unified();       // Already chased these down
    TV2 rez = VARS.get(this);
    if( rez!=null ) return rez; // Been there, done that
    // Unlike the original algorithm, to handle cycles here we stop making a
    // copy if it appears at this level in the nongen set.  Otherwise we'd
    // clone it down to the leaves - and keep all the nongen leaves.  Stopping
    // here preserves the cyclic structure instead of unrolling it.
    if( nongen_in(nongen) )  return vput(this);
    // New leaf
    if( is_leaf() ) return vput(make_leaf_ns(_ns,"_fresh_leaf"));

    TV2 t = copy("_fresh_copy");
    VARS.put(this,t);       // Stop cyclic structure looping
    if( _args!=null )
      for( String key : _args.keySet() )
        t._args.put(key,get(key)._fresh(nongen));
    return t;
  }

  // --------------------------------------------
  private static final VBitSet ODUPS = new VBitSet();
  public boolean nongen_in(TV2[] vs) {
    if( vs==null ) return false;
    ODUPS.clear();
    for( TV2 t2 : vs )
      // Cannot do the U-F hack on 'vs' because it shows up in FreshNode hashCode.
      if( _occurs_in_type(t2.find()) )
        return true;
    return false;
  }

  // Does 'this' type occur in any scope, mid-definition (as a forward-ref).
  // If not, then return false (and typically make a fresh copy).
  // If it does, then 'this' reference is a recursive self-reference
  // and needs to keep the self-type instead of making fresh.
  boolean _occurs_in(TV2[] vs) {
    // Can NOT modify 'vs' for U-F, because blows FreshNode hash.
    for( TV2 v : vs )
      if( _occurs_in_type(v.find()) )
        return true;
    return false;
  }

  boolean _occurs_in_type(TV2 x) {
    assert !is_unified() && !x.is_unified();
    if( x==this ) return true;
    if( ODUPS.tset(x._uid) ) return false; // Been there, done that
    if( x.is_tvar() && x._args!=null )
      for( TV2 tv2 : x._args.values() )
        if( _occurs_in_type(tv2) )
          return true;
    return false;
  }

  // --------------------------------------------
  // Attempt to lift a GCP call result, based on HM types.  Walk the input HM
  // type and GCP flow type in parallel and create a mapping.  Then walk the
  // output HM type and GCP flow type in parallel, and join output GCP types
  // with the matching input GCP type.
  public static final NonBlockingHashMap  <TV2,Type> T2MAP = new NonBlockingHashMap<>();
  public static final NonBlockingHashMapLong<String> WDUPS = new NonBlockingHashMapLong<>();
  public Type walk_types_in(TypeMem tmem, Type t) {
    assert !is_unified();
    long duid = dbl_uid(t._uid);
    if( WDUPS.putIfAbsent(duid,"")!=null ) return t;
    if( is_err() ) return fput(Type.SCALAR); //
    // Base variables (when widened to an HM type) might force a lift.
    if( is_base() ) return fput(_type.meet(t));
    // Free variables keep the input flow type.
    if( is_leaf() ) return fput(t);
    // Nilable
    if( is_nil() )
      return get("?").walk_types_in(tmem,fput(t.join(Type.NSCALR)));

    // Functions being called or passed in can have their return types appear
    // in the call result.
    if( is_fun() ) {
      if( !(t instanceof TypeFunPtr) ) return t; // Typically, some kind of error situation
      fput(t);                     // Recursive types put themselves first
      TypeFunPtr tfp = (TypeFunPtr)t;
      TV2 ret = get(" ret");
      if( tfp._fidxs==BitsFun.FULL        ) return t;
      if( tfp._fidxs==BitsFun.FULL.dual() ) return t;
      for( int fidx : tfp._fidxs ) {
        FunNode fun = FunNode.find_fidx(fidx);
        if( fun.fptr().tvar().is_err() ) throw unimpl();
        Type tret = ((TypeTuple)fun.ret()._val).at(REZ_IDX);
        ret.walk_types_in(tmem,tret);
      }
      return t;
    }

    if( is_struct() ) {
      fput(t);                // Recursive types need to put themselves first
      if( !(t instanceof TypeMemPtr) )  return t;
      TypeMemPtr tptr = (TypeMemPtr)(t.simple_ptr()==t ? tmem.sharptr(t) : t);
      if( !(tptr._obj instanceof TypeStruct) ) return tptr;
      TypeStruct ts = (TypeStruct)tptr._obj; // Always a TypeStruct here
      if( _args!=null )
        for( String id : _args.keySet() ) {
          TypeFld fld = ts.fld_find(id);
          get(id).walk_types_in(tmem,fld==null ? Type.XSCALAR : fld._t);
        }
      return tptr.make_from(ts);
    }

    if( isa("Ary") ) {
      fput(t);                // Recursive types need to put themselves first
      if( !(t instanceof TypeMemPtr) )  return t;
      TypeMemPtr tptr = (TypeMemPtr)tmem.sharptr(t);
      if( !(tptr._obj instanceof TypeAry) ) return t;
      TypeAry tary = (TypeAry)tptr._obj;
      TV2 elem = get("elem");
      if( elem == null ) return t;
      return elem.walk_types_in(tmem,tary.elem());
    }

    if( isa("Str") )
      return fput(_type.meet(t));

    throw unimpl();
  }
  // Gather occurs of each TV2, and MEET all the corresponding Types.
  private Type fput(final Type t) {
    T2MAP.merge(this, t, Type::meet);
    return t;
  }

  public Type walk_types_out(Type t, CallEpiNode cepi) {
    assert !is_unified();
    if( t == Type.XSCALAR ) return t;  // No lift possible
    Type tmap = T2MAP.get(this);
    if( is_leaf() || is_err() ) { // If never mapped on input, leaf is unbound by input
      if( tmap==null ) return t;
      push_dep(cepi);           // Re-run apply if this leaf re-maps
      return tmap.join(t);
    }
    if( is_base() ) return tmap==null ? _type : tmap.join(t);
    if( is_nil() ) return t; // nil is a function wrapping a leaf which is not-nil
    if( is_fun() ) return t; // No change, already known as a function (and no TFS in the flow types)
    if( is_struct() ) {
      if( !(t instanceof TypeMemPtr) ) {
        if( tmap==null ) throw unimpl(); // return tmap == null ? as_flow().join(t) : tmap;  // The most struct-like thing you can be
        return tmap;
      }
      TypeStruct ts = (TypeStruct)((TypeMemPtr)t)._obj;
      throw unimpl();
    }
    if( is_ary() ) {
      if( !(t instanceof TypeMemPtr) ) {
        if( tmap==null ) throw unimpl(); // return tmap == null ? as_flow().join(t) : tmap;  // The most struct-like thing you can be
        return tmap;
      }

      throw unimpl();
    }
    if( is_str() ) return tmap==null ? _type : tmap.join(t);
    throw unimpl();
  }

  // --------------------------------------------
  // Recursively build a conservative flow type from an HM type.

  // No function arguments, just function returns.
  static final NonBlockingHashMapLong<TypeStruct> ADUPS = new NonBlockingHashMapLong<>();
  public Type as_flow() {
    assert ADUPS.isEmpty();
    Type t = _as_flow();
    ADUPS.clear();
    return t;
  }
  Type _as_flow() {
    assert !is_unified();
    if( is_base() ) return _type;
    if( is_leaf() ) return Type.SCALAR;
    if( is_err()  ) throw unimpl(); // return _type;
    if( is_fun()  ) return TypeFunPtr.make(((TypeFunPtr)_type)._fidxs,_args.size()-1,Type.ANY);
    if( is_nil() ) return Type.SCALAR;
    if( is_struct() ) {
      TypeStruct tstr = ADUPS.get(_uid);
      if( tstr==null ) {
        Type.RECURSIVE_MEET++;
        tstr = TypeStruct.malloc("",false,false).add_fld(TypeFld.NO_DISP);
        if( _args!=null )
          for( String id : _args.keySet() )
            tstr.add_fld(TypeFld.malloc(id));
        tstr.set_hash();
        ADUPS.put(_uid,tstr); // Stop cycles
        if( _args!=null )
          for( String id : _args.keySet() )
            tstr.fld_find(id).setX(get(id)._as_flow()); // Recursive
        if( --Type.RECURSIVE_MEET == 0 )
          // Shrink / remove cycle dups.  Might make new (smaller)
          // TypeStructs, so keep RECURSIVE_MEET enabled.
          tstr = tstr.install();
      } else {
        tstr._cyclic=true;    // Been there, done that, just mark it cyclic
      }
      // The HM is_struct wants to be a TypeMemPtr, but the recursive builder
      // is built around TypeStruct.
      return ((TypeMemPtr)_type).make_from(tstr);
    }

    throw unimpl();
  }


  // --------------------------------------------
  // This is a TV2 function that is the target of 'fresh', i.e., this function
  // might be fresh-unified with some other function.  Push the application
  // down the function parts; if any changes the fresh-application may make
  // progress.
  static final VBitSet DEPS_VISIT  = new VBitSet();
  public void push_deps( UQNodes deps) { if( deps!=null ) for( Node dep : deps.values() ) push_dep(dep);}
  public TV2 push_dep(Node dep) {
    assert DEPS_VISIT.isEmpty();
    _push_update(dep);
    DEPS_VISIT.clear();
    return this;
  }
  private void _push_update(Node dep) {
    assert !is_unified();
    if( DEPS_VISIT.tset(_uid) ) return;
    if( _deps!=null && _deps.get(dep._uid)!=null ) return; // Already here and in all children
    if( dep.is_dead() ) return;
    _deps = _deps==null ? UQNodes.make(dep) : _deps.add(dep);
    if( _args!=null )
      for( TV2 arg : _args.values() ) // Structural recursion on a complex TV2
        arg.debug_find()._push_update(dep);
  }

  // Recursively add-deps to worklist
  public void add_deps_work( Work work ) { assert DEPS_VISIT.isEmpty(); add_deps_work_impl(work); DEPS_VISIT.clear(); }
  private void add_deps_work_impl( Work work ) {
    work.add(_deps);
    if( DEPS_VISIT.tset(_uid) ) return;
    if( _args != null )
      for( TV2 tv2 : _args.values() )
        tv2.add_deps_work_impl(work);
  }

  // Merge Dependent Node lists, 'this' into 'that'.  Required to trigger
  // CEPI.unify_lift when types change structurally, or when structures are
  // unifing on field names.
  private void merge_deps( TV2 that ) { that.push_deps(_deps); }
  // Merge Node lists, 'this' into 'that', for easier debugging.
  // Lazily remove dead nodes on the fly.
  private void merge_ns( TV2 that ) { that._ns = that._ns == null ? _ns : that._ns.addAll(_ns); }

  // --------------------------------------------
  // Pretty print
  boolean is_prim() { return is_struct() && _args!=null && _args.containsKey("!_"); }
  boolean is_math() { return is_struct() && _args!=null && _args.containsKey("pi"); }

  // Look for dups, in a tree or even a forest (which Syntax.p() does)
  public VBitSet get_dups() { return _get_dups(new VBitSet(),new VBitSet()); }
  public VBitSet _get_dups(VBitSet visit, VBitSet dups) {
    if( visit.tset(_uid) ) {
      dups.set(debug_find()._uid);
    } else {
      if( _args!=null )
        for( TV2 t : _args.values() )
            t._get_dups(visit,dups);
      if( _unified!=null )
        _unified._get_dups(visit,dups);
    }
    return dups;
  }

  // Fancy print for Debuggers - includes explicit U-F re-direction.
  // If debug is on, does NOT roll-up - no side effects.
  @Override public String toString() { return str(new SB(), new VBitSet(), get_dups(), true ).toString(); }
  public String p() { VCNT=0; VNAMES.clear(); return str(new SB(), new VBitSet(), get_dups(), false ).toString(); }
  private static int VCNT;
  private static final HashMap<TV2,String> VNAMES = new HashMap<>();
  public SB str(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    boolean dup = dups.get(_uid);
    if( !debug && is_unified() ) return find().str(sb,visit,dups,debug);
    if( is_unified() || is_leaf() ) {
      sb.p(VNAMES.computeIfAbsent(this,( k ->  debug ? ("V"+k._uid) : ((++VCNT)-1+'A' < 'V' ? (""+(char)('A'+VCNT-1)) : ("V"+VCNT)))));
      return is_unified() ? _unified.str(sb.p(">>"), visit, dups, debug) : sb;
    }
    if( is_err () )  return sb.p(_type);
    if( is_base() )  return sb.p(_type);

    if( dup ) sb.p("$V").p(_uid);
    if( visit.tset(_uid) && dup ) return sb;
    if( dup ) sb.p(':');

    // Special printing for functions
    if( is_fun() ) {
      if( _type==null ) sb.p("[?]"); // Should always have an alias
      else {
        if( _type instanceof TypeFunPtr ) ((TypeFunPtr)_type)._fidxs.clear(0).str(sb);
        else _type.str(sb,visit,null,debug); // Weirdo type printing
      }
      sb.p("{ ");
      for( String fld : sorted_flds() )
        if( !Util.eq(" ret",fld) ) {
          if( Util.eq("2",fld) ) sb.p("^=");
          str0(sb,visit,_args.get(fld),dups,debug).p(' ');
        }
      return str0(sb.p("-> "),visit,_args.get(" ret"),dups,debug).p(" }");
    }

    // Special printing for structures
    if( is_struct() ) {
      if( is_prim() ) return sb.p("@{PRIMS}");
      if( is_math() ) return sb.p("@{MATH}");
      final boolean is_tup = is_tup(); // Distinguish tuple from struct during printing
      if( _type==null ) sb.p("[?]"); // Should always have an alias
      else {
        if( _type instanceof TypeMemPtr ) ((TypeMemPtr)_type)._aliases.clear(0).str(sb);
        else _type.str(sb,visit,null,debug); // Weirdo type printing
      }
      sb.p(is_tup ? "(" : "@{");
      if( _args==null ) sb.p("_ ");
      else
        for( String fld : sorted_flds() ) // Skip field names in a tuple
          str0(is_tup ? sb.p(' ') : sb.p(' ').p(fld).p(" = "),visit,_args.get(fld),dups,debug).p(',');
      if( open() ) sb.p(" ...,");
      sb.unchar().p(!is_tup ? "}" : ")");
      if( _type!=null && _type.must_nil() ) sb.p("?");
      return sb;
    }

    if( is_nil() )
      return sb.p("0?");

    if( is_str() )
      return sb.p("str").p(_type.must_nil()?"?":"");

    // Generic structural T2
    sb.p("(").p(_name).p(" ");
    if( _args!=null )
      for( String s : _args.keySet() )
        str0(sb.p(s).p(':'),visit,_args.get(s),dups,debug).p(" ");
    sb.unchar().p(")");
    if( _type!=null && _type.must_nil() ) sb.p('?');
    return sb;
  }
  static private SB str0(SB sb, VBitSet visit, TV2 t, VBitSet dups, boolean debug) { return t==null ? sb.p("_") : t.str(sb,visit,dups,debug); }
  private boolean is_tup() {  return _args==null || _args.isEmpty() || _args.containsKey("0"); }
  private Collection<String> sorted_flds() { return new TreeMap<>(_args).keySet(); }
}
