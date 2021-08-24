package com.cliffc.aa.tvar;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;
import org.jetbrains.annotations.NotNull;

import java.util.*;

import static com.cliffc.aa.AA.unimpl;

// Type Variable.  TVars unify (ala Tarjan Union-Find), and can have structure
// (such as "{ A -> B }").  TVars are tied to a TNode to enforce Type structure
// on Types.  TVars with no structure either refer to a plain Node, or get
// unioned into another TVar.  TVars with structure have to match structure to
// be unified, but then can be recursively unified.

// See HM.java for the prototype this is based from.

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
  // - "Free": Nothing points to it, can be re-used.
  private String _name;
  // Set of structural H-M parts.  Can be null if empty.
  NonBlockingHashMap<String,TV2> _args;
  private boolean _open;        // Can be extended

  // U-F algo.  Only set when unified, monotonic null->unification_target.
  // Can change again to shorten unification changes.
  private TV2 _unified;

  // Base primitive types, not really tied to any Node.  TypeInt, TypeFlt.
  public Type _type;

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
  public boolean isa(String s){ return !is_unified() && Util.eq(_name,s); }
  public boolean is_tvar   () { return !is_unified() && _args!=null; } // Excludes unified,base,dead,free; includes nil,fun,struct
  // Flat TV2s; no args.
  public boolean is_free   () { return !is_unified() && isa("Free"   ); } // Allocated and then freed.  TBD if this pays off
  public boolean is_err    () { return !is_unified() && isa("Err"    ); } // Error; exciting if not eventually dead
  public boolean is_base   () { return !is_unified() && isa("Base"   ); } // Some base constant (no internal TV2s)
  public boolean is_leaf   () { return !is_unified() && isa("Leaf"   ); } // Classic H-M leaf type variable, probably eventually unifies
  // Structural TV2s; has args
  public boolean is_nilable() { return !is_unified() && isa("Nil"    ); } // Some nilable TV2
  public boolean is_fun    () { return !is_unified() && isa("->"     ); } // A function, arg keys are numbered from ARG_IDX, and the return key is "ret"
  public boolean is_struct () { return !is_unified() && isa("@{}"    ); } // A struct, keys are field names
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

  // Unify-at a selected key.
  public boolean unify_at(int key, TV2 tv2, Work work ) { return unify_at(""+key,tv2,work); }
  // Unify-at a key.  Expect caller is already a tvar.
  public boolean unify_at(String key, TV2 tv2, Work work ) {
    if( is_err() ) return unify(tv2,work);// if i am dead, all my parts are dead, so tv2 is unifying with a dead part
    assert is_tvar() && !tv2.is_unified();
    TV2 old = get(key);
    if( old!=null )
      return old.unify(tv2,work); // This old becomes that
    if( work==null ) return true; // Would add part
    args_put(key,tv2);
    work.add(_deps);
    return true;
  }

  // Open to new fields or not
  public boolean open() {
    return _open;
  }

  public Set<String> args() { return _args.keySet(); }

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
    // Make a new Nil
  public static TV2 make_nil(Node n, Type type, TV2 leaf, @NotNull String alloc_site) {
    NonBlockingHashMap<String,TV2> args = new NonBlockingHashMap<String,TV2>(){{ put("?",leaf); }};
    return new TV2("Nil",args,type,UQNodes.make(n),alloc_site);
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
    assert args!=null;          // Must have some structure
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
        args.put(""+i,ntvs[i].tvar());
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
  private TV2 _find0() {
    TV2 top = debug_find();
    if( top == this ) return top;
    TV2 v = this;               // Rerun, rolling up to top
    while( v != top ) { TV2 next = v._unified; v._union(top); v = next; }
    return top;
  }

  public TV2 find() {
    TV2 top = _find0();
    return top.is_nilable() ? top._find_nil() : top;
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
    if( !that.is_err() ) {
      // Keep the merge of all base types, and add _deps.
      if( _type != that._type )  Env.GVN.add_flow(_deps);
      if( _type!=null && that._type!=null && _type!=Type.XNIL && !_type.widen().isa(that._type.widen()) )
        throw unimpl();      // Error, mismatched base types, e.g. int and string
      if( that._type==null ) that._type = _type;
      else if( _type!=null ) that._type = _type.meet(that._type);
      if( is_struct() ) that._open &= _open; // Most conservative answer
    }
    work.add(_deps);            // Revisit
    // Hard union this into that, no more testing
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
    assert is_nilable() && !that.is_nilable();
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

  // True if args are equal
  public boolean eq(Node[] args) {
    //for( int i=0; i<args.length; i++ )
    //  if( args[i]!=null && args[i].tvar()!=get(""+i) )
    //    return false;
    //return true;
    throw unimpl();
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
    if( this.is_nilable() && !that.is_nilable() ) return this.unify_nil(that,work);
    if( that.is_nilable() && !this.is_nilable() ) return that.unify_nil(this,work);

    // Cycle check.
    long luid = dbl_uid(that);  // long-unique-id formed from this and that
    TV2 rez = DUPS.get(luid);
    assert rez==null || rez==that;
    if( rez!=null ) return false; // Been there, done that
    DUPS.put(luid,that);          // Close cycles

    // Check for mismatched, cannot unify
    if( !Util.eq(_name,that._name) ) {
      if( work==null ) return true;
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

    // Only common fields end up in the result
    for( String key : that._args.keySet() )
      if( args.get(key)==null )
        if( !this.open() )
          that.del_fld(key, work);  // Drop from RHS

    if( find().is_err() && !that.is_err() )
      throw unimpl(); // TODO: Check for being equal, cyclic-ly, and return a prior if possible.
    return find().union(that,work);
  }

  // Insert a new field
  private void add_fld( String id, TV2 fld, Work work) {
    assert is_struct();
    _args.put(id,fld);
    fld.push_deps(_deps);
    work.add(_deps);
  }
  // Delete a field
  private void del_fld( String fld, Work work) {
    assert is_struct();
    _args.remove(fld);
    work.add(_deps);
  }

//private boolean union_err(TV2 that, String msg) {
//  union(that);
//  return that.union(make_err(null,msg,"TV2.unify_err"));
//}
//
//private boolean unify_base(TV2 that) {
//  that._type = _type.meet(that._type);
//  return union(that);
//}

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
    if( is_base() && that.is_base() ) throw unimpl();

    // Special handling for nilable
    if( this.is_nilable() && !that.is_nilable() ) {
      Type mt = that._type.meet_nil(Type.XNIL);
      if( mt == that._type ) return false;
      if( work==null ) return true;
      throw unimpl();
    }
    
    // That is nilable and this is not
    if( that.is_nilable() && !this.is_nilable() ) {
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
          throw unimpl();
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
    // are an error.
    if( !open() )
      for( String id : that.args() ) // For all fields in RHS
        if( get(id)==null ) {       // Missing in LHS
          if( work == null ) return true; // Will definitely make progress
          //progress |= that.del_fld(i--, work);     // Extra fields on both sides are dropped
          throw unimpl();
        }
    that._open &= this._open;

    return progress;
  }

  private boolean vput(TV2 that, boolean progress) { VARS.put(this,that); return progress; }
  private TV2 vput(TV2 that) { VARS.put(this,that); return that; }

  //// Return a fresh copy of 'this'
  //T2 fresh() {
  //  assert VARS.isEmpty();
  //  T2 rez = _fresh(null);
  //  VARS.clear();
  //  return rez;
  //}

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


//// --------------------------------------------
//
//// Used by Loads and Stores.  Unify tv against all aliases at this field
//// only.  Aliases are either produced by the Parser (so very generic) or from
//// forwards-flow from News and very specific.  Ignore the generic ones until
//// they refine.  TODO: As aliases further refine, need to undo-redo prior
//// unifies against larger/weaker aliases.
//public boolean unify_alias_fld(Node ldst, BitsAlias aliases, String fld, TV2 tv, boolean test, String alloc_site) {
//  assert isa("Mem");
//  assert !tv.is_unified();
//  boolean progress=false;
//  for( int alias : aliases ) {
//    // TODO: Probably wrong, as no reason to believe that as soon as alias
//    // sharpens above AARY that it has hit its best sane value.
//    if( alias <= BitsAlias.AARY ) return false; // No unify on parser-specific values
//    TV2 tobj = get(alias);
//    if( tobj == null ) {      // Missing, act as a fresh TV2 and lazily manifest
//      if( test ) return true; // Definitely will be progress
//      progress = true;
//      TV2 tvo = make("Obj",ldst,alloc_site);
//      args_put(alias,tvo);
//      tvo.args_put(fld,tv);
//    } else if( tobj.isa("Obj") ) {
//      progress = tobj.unify_at(fld,tv.find(),test);
//    } else if( tobj.is_dead() || tobj.isa("Err") ) {
//      tobj.unify(tv.find(),test);
//    } else
//      throw com.cliffc.aa.AA.unimpl();
//    if( progress && test ) return progress; // Shortcut
//  }
//  return progress;
//}


//// --------------------------------------------
//// Find instances of 'tv' inside of 'this' via structural recursion.  Walk
//// the matching Type at the same time.  Report the first one found, and
//// assert all the others have the same Type.
//public Type find_tvar(Type t, TV2 tv) {
//  assert DUPS.isEmpty();
//  Type rez = _find_tvar(t,tv,Type.ALL);
//  DUPS.clear();
//  return rez;
//}
//private Type _find_tvar(Type t, TV2 tv, Type rez) {
//  if( tv.is_dead() ) return rez;
//  if( t==Type.ALL ) return rez; // Join against 'ALL' never changes anything
//  if( tv==this ) {
//    rez = rez.join(t);
//    return rez;
//  }
//  switch(_name) {
//  case "Mem":
//    if( t ==Type.ANY ) return rez; // No substructure in type
//    TypeMem tmem = (TypeMem)t;
//    for( Comparable key : _args.keySet() ) {
//      TypeObj to = tmem.at((Integer) key);
//      TV2 obj = get(key);
//      if( obj!=null )
//        rez = obj._find_tvar(to,tv,rez);
//    }
//    return rez;
//  case "Obj":
//    if( t==TypeObj.UNUSED || t==TypeObj.ISUSED )
//      return rez; // No substructure in type
//    if( t instanceof TypeStr || t instanceof TypeAry )
//      return rez; // TODO: Handle These
//    TypeStruct ts = (TypeStruct)t; //
//    for( Comparable key : _args.keySet() ) {
//      //int idx = ts.find((String)key);
//      //if( idx!= -1 )          // If field exists
//      //  rez = get(key)._find_tvar(ts.at(idx),tv,rez);
//      throw unimpl();
//    }
//    return rez;
//  case "Fun":
//    if( t.is_forward_ref() ) return rez;
//    if( !(t instanceof TypeFunPtr) ) return rez;
//    // TypeFunPtrs carry only a set of FIDXS & a DISPLAY.
//    // Hence no other Type is available here for lifting.
//    return rez;
//  case "Ret":
//    TypeTuple tt = (TypeTuple)t;
//    for( int i=0; i<tt.len(); i++ )
//      rez = get(i)._find_tvar(tt.at(i),tv,rez);
//    return rez;
//  case "Ptr":
//    if( !(t instanceof TypeMemPtr) ) return rez;
//    return get(0)._find_tvar(((TypeMemPtr)t)._obj,tv,rez);
//  case "Base":
//  case "Dead":
//  case "Err":
//  case "Leaf":
//  case "Nil":
//    return rez; // No substructure in TV2 and not equal already
//
//  default: throw com.cliffc.aa.AA.unimpl();
//  }
//}
//
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

//// Get TV2 from array, with U-F rollup
//public static TV2 get(TV2[] vs, int i) {
//  TV2 tv = vs[i].find();
//  return vs[i]==tv ? tv : (vs[i]=tv); // U-F rollup
//}


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
      for( String key : _args.keySet() ) // Structural recursion on a complex TV2
        get(key)._push_update(dep);
  }

  // Merge Dependent Node lists, 'this' into 'that'.  Required to trigger
  // CEPI.unify_lift when types change structurally, or when structures are
  // unifing on field names.
  private void merge_deps( TV2 that ) { that._deps = that._deps == null ? _deps : that._deps.addAll(_deps); }
  // Merge Node lists, 'this' into 'that', for easier debugging.
  // Lazily remove dead nodes on the fly.
  private void merge_ns  ( TV2 that ) { that._ns   = that._ns   == null ? _ns   : that._ns  .addAll(_ns  ); }

  // Recursively add-deps to worklist
  public void add_deps_work( Work work ) { assert DEPS_VISIT.isEmpty(); add_deps_work_impl(work); DEPS_VISIT.clear(); }
  private void add_deps_work_impl( Work work ) {
    if( _args==null ) {
      work.add(_deps);
    } else {
      if( DEPS_VISIT.tset(_uid) ) return;
      if( _args != null )
        for( TV2 tv2 : _args.values() )
          tv2.add_deps_work_impl(work);
    }
  }

  // --------------------------------------------
  // Pretty print
  boolean is_prim() {
    return is_struct() && _args!=null && _args.containsKey("!");
  }

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
  public SB str(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    boolean dup = dups.get(_uid);
    if( is_unified() || is_leaf() ) {
      if( !debug ) throw unimpl();
      sb.p("V").p(_uid);
      return is_unified() ? _unified.str(sb.p(">>"), visit, dups, debug) : sb;
    }
    if( is_err () )  return sb.p(_type);
    if( is_base() )  return sb.p(_type);

    if( dup ) sb.p("$V").p(_uid);
    if( visit.tset(_uid) && dup ) return sb;
    if( dup ) sb.p(':');

    // Special printing for functions
    if( is_fun() ) {
      sb.p("{");
      _type.str(sb,visit,null,debug); // Probably want a custom printer
      sb.p(' ');
      //for( int i=0; i<_args.length-1; i++ )
      //  str(sb,visit,_args[i],dups,debug).p(" ");
      //return str(sb.p("-> "),visit,_args[_args.length-1],dups).p(" }");
      return sb.p("FIX FUNCTION PRINTING");
    }

    // Special printing for structures
    if( is_struct() ) {
      if( is_prim() ) return sb.p("@{PRIMS}");
      sb.p("@{");
      if( _type!=null ) _type.str(sb,visit,null,debug); // Probably want a custom printer
      sb.p(' ');
      if( _args==null ) sb.p("_ ");
      else for( String fld : _args.keySet() )
             str0(sb.p(' ').p(fld).p(" = "),visit,_args.get(fld),dups,debug).p(',');
      if( open() ) sb.p(" ...,");
      return sb.unchar().p("}");
    }

    // Generic structural T2
    sb.p("(").p(_name).p(" ");
    if( _args!=null )
      for( String s : _args.keySet() )
        str0(sb.p(s).p(':'),visit,_args.get(s),dups,debug).p(" ");
    return sb.unchar().p(")");
  }
  static private SB str0(SB sb, VBitSet visit, TV2 t, VBitSet dups, boolean debug) { return t==null ? sb.p("_") : t.str(sb,visit,dups,debug); }
}
