package com.cliffc.aa.tvar;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.CallEpiNode;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.node.FreshNode;
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
  // - "Args", "Ret", "Fun", "Mem", "Obj", "If".  A structural tag for the H-M
  // "type", these have to be equal during unification; their Keys in _args are
  // unioned and equal keys are unified
  // - "Base" - some constant Type, Base Types MEET when unified.
  // - "Nil" - The XNIL/NIL Type.  Always loses all unifications.
  // - "Fresh": A one-off indirection to another TV2 which needs to be fresh-
  // unified instead of normal-unification of this TV2.  The freshable TV2 is
  // under the solo key "Fresh".
  // - "Dead": a dead Node or a Type.ANY ConNode, and a dead TV2.  Unifies with
  // everything, wins all unifications, and has no structure.
  // - "Free": Nothing points to it, can be re-used.
  private String _name;
  // Set of structural H-M parts.  Can be null if empty.  
  public NonBlockingHashMap<String,TV2> _args;

  // U-F algo.  Only set when unified, monotonic null->unification_target.
  // Can change again to shorten unification changes.
  private TV2 _unified;

  // Base primitive types, not really tied to any Node.  TypeInt, TypeFlt.
  public Type _type;

  // Set of dependent CallEpiNodes, to be re-worklisted if the called function changes TV2.
  private UQNodes _deps;

  // Debug only.  Set of unioned Nodes.  null for empty.  Helpful to track where TV2s come from.
  private UQNodes _ns;     //
  private @NotNull String _alloc_site; // Creation site; used to track excessive creation.

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
  public boolean is_dead   () { return !is_unified() && isa("Dead"   ); } // Dead, type is not interesting
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
  public boolean unify_at(String key, TV2 tv2, boolean test ) {
    if( is_dead() ) return unify(tv2,test);
    assert is_tvar() && _args!=null && !tv2.is_unified();
    TV2 old = get(key);
    if( old!=null )
      return old.unify(tv2,test);
    if( test ) return true;
    args_put(key,tv2);
    Env.GVN.add_flow(_deps);    // Re-CallEpi
    return true;
  }

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
    if( type instanceof TypeObj ) { // Constant object?
      return make("Obj",n,alloc_site); // Empty object constant
    }
    UQNodes ns = n==null ? null : UQNodes.make(n);
    type = type.widen();
    TV2 tv2 = new TV2("Base",null,type,ns,alloc_site);
    assert tv2.is_base() && !tv2.is_leaf();
    return tv2;
  }
  // Make a new primitive base TV2
  public static TV2 make_err(Node n, String msg, @NotNull String alloc_site) {
    UQNodes ns = n==null ? null : UQNodes.make(n);
    TV2 tv2 = new TV2("Err",null,TypeStr.con(msg.intern()),ns,alloc_site);
    assert tv2.is_err() && !tv2.is_leaf() && !tv2.is_base();
    return tv2;
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
  // Structural constructor from array of TVs
  public static TV2 make(@NotNull String name, Node n, @NotNull String alloc_site, Node... ntvs) {
    assert ntvs!=null;          // Must have some structure
    NonBlockingHashMap<String,TV2> args = new NonBlockingHashMap<>();
    for( int i=0; i<ntvs.length; i++ )
      if( ntvs[i]!=null )
        args.put(""+i,ntvs[i].tvar());
    return make(name,n,alloc_site,args);
  }
  public static TV2 make(@NotNull String name, UQNodes ns, @NotNull String alloc_site ) {
    TV2 tv2 = new TV2(name, new NonBlockingHashMap<>(),null,ns,alloc_site);
    assert !tv2.is_base() && !tv2.is_leaf();
    return tv2;
  }

  // Structural constructor for new memory
  public static TV2 make_mem(Node n, @NotNull String alloc_site) { return make("Mem",n,alloc_site,new NonBlockingHashMap<>()); }

  public static TV2 DEAD = new TV2("Dead",null,null,null,"static");

  public static void reset_to_init0() {
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
  // Tarjan U-F find, without the roll-up.  Used for debug printing.
  TV2 debug_find() {
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
    while( v != top ) v = v._union(top);
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
    case "Leaf":   return this;   //
    case "Base": 
      // Nested nilable-and-not-leaf, need to fixup the nilable.
      // "this" becomes a base+XNIL
      _type = n._type.meet_nil(Type.XNIL);
      _args = null;             // TODO: Free /recycle the args
      _name = "Base";
      break;
    case "@{}":
      _type = n._type.meet_nil(Type.XNIL); // Add a nil alias
      _args = (NonBlockingHashMap<String,TV2>)n._args.clone();  // Shallow copy the TV2 fields
      break;
    case "Nil":                 // Nested nilable; collapse the layer
      _args.put("?",n.get("?"));
      break;
    default: 
      throw unimpl();
    }

    n.merge_deps(this);         // Copy n._deps into _deps
    n.merge_ns  (this);
    return this;
  }

  
  // U-F union; 'this' becomes 'that'.  No change if only testing, and reports
  // progress.  If progress and not testing, adds _deps to worklist.  
  public boolean union(TV2 that, boolean test) {
    assert !is_unified() && !that.is_unified() && !is_dead();
    if( this==that ) return false;
    if( test ) return true;     // All remaining paths make progress
    // Keep the merge of all base types, and add _deps.
    if( _type != that._type )  Env.GVN.add_flow(_deps);
    if( !_type.widen().isa(that._type.widen()) )
      throw unimpl();      // Error, mismatched base types, e.g. int and string
    that._type = _type.meet(that._type);
    // Hard union this into that, no more testing
    _union(that);
    return true;
  }
  private TV2 _union(TV2 that) {
    assert !is_unified() && !that.is_unified();
    _unified=that;
    assert is_unified();
    ALLOCS.get(_alloc_site)._unified++;
    merge_deps(that);           // Merge update lists, for future unions
    merge_ns  (that);           // Merge Node list, for easier debugging
    _args = null;               // Clean out extra state from 'this'
    _type = null;
    _deps = null;
    _ns   = null;
    return that;
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

//// --------------------------------------------
//// Used in the recursive unification process.  During unify detects cycles,
//// to allow cyclic unification.
//private static final NonBlockingHashMapLong<TV2> DUPS = new NonBlockingHashMapLong<>();
//
//// Structural unification.  Both 'this' and that' are the same afterwards.
//// Returns True if progress.
  public boolean unify(TV2 that, boolean test) {
//  //assert !this.is_unified() && !that.is_unified();
//  //if( this==that ) return false;
//  //assert DUPS.isEmpty();
//  //boolean progress = _unify(that,test);
//  //DUPS.clear();
//  //return progress;
    throw unimpl();
  }
//
//// Classic structural unification, no "fresh".  Unifies 'this' into 'that'.
//// Both 'this' and 'that' are the same afterwards.  Returns true if progress.
//private boolean _unify(TV2 that, boolean test) {
//  assert !is_unified() && !that.is_unified();
//  if( this==that ) return false;
//
//  // Check for simple, non-recursive, unification.
//  // NIL always loses and makes no progress (no structure implications)
//  if( this.is_nil () ) return false;
//  if( that.is_nil () ) return false;
//  // All remaining paths make progress and return true.
//  if( test ) return true;
//  // Dead wins all
//  if( this.is_dead() ) return that.union(this);
//  if( that.is_dead() ) return this.union(that);
//  // two errs union in either order, so keep lower uid (actually should merge error strings)
//  if( is_err() && that.is_err() && _uid<that._uid ) return that.union(this);
//  if(      is_err() ) return that.union(this);
//  if( that.is_err() ) return      union(that);
//  // Two leafs union in either order, so keep lower uid
//  if( this.is_leaf() && that.is_leaf() && _uid < that._uid ) return that.union(this);
//  if( this.is_leaf() ) return this.union(that);
//  if( that.is_leaf() ) return that.union(this);
//  // Bases unify constants also
//  if( this.is_base() && that.is_base() ) return unify_base(that);
//
//  // Cycle check.
//  long luid = ((long)_uid<<32)|that._uid; // Make a unique id for the pair
//  TV2 rez = DUPS.get(luid);
//  if( rez!=null ) return false; // Been there, done that
//  DUPS.put(luid,that);          // Close cycles
//
//  // Errors
//  if( !Util.eq(_name,that._name) )
//    return union_err(that,"Cannot unify "+this+" and "+that);
//  assert _args!=that._args; // Efficiency hack elsewhere if this is true here
//
//
//  // Structural recursion unification, this into that.
//  for( Comparable key : _args.keySet() ) {
//    TV2 vthis =       get(key);  assert vthis!=null;
//    TV2 vthat =  that.get(key);
//    if( vthat==null ) that.args_put(key,vthis);
//    else              { vthis._unify(vthat,test); that = that.find(); }
//    assert !that.is_unified();
//  }
//
//  // TODO: Check for being equal, cyclic-ly, and return a prior if possible.
//  return find().union(that);
//}
//private boolean union_err(TV2 that, String msg) {
//  union(that);
//  return that.union(make_err(null,msg,"TV2.unify_err"));
//}
//
//private boolean unify_base(TV2 that) {
//  that._type = _type.meet(that._type);
//  return union(that);
//}
//private boolean fresh_base(TV2 that, boolean test) {
//  Type con = _type.meet(that._type);
//  if( con==that._type ) return false; // No progress
//  if( !test ) that._type = con;  // Yes progress, but no update if testing
//  return true;
//}
//
//// Used in the recursive unification process.  During fresh_unify tracks the
//// mapping from LHS TV2s to RHS TVs.
//private static final HashMap<TV2,TV2> VARS = new HashMap<>();
//
//// Make a (lazy) fresh copy of 'this' and unify it with 'that'.  This is
//// the same as calling 'fresh' then 'unify', without the clone of 'this'.
//// The TV2[] is used when making the 'fresh' copy for the occurs_check.
//
//// Returns progress.
//// If test, we are testing only and make no changes.
//public boolean fresh_unify(TV2 that, TV2[] vs, boolean test) {
//  //assert VARS.isEmpty() && DUPS.isEmpty();
//  //boolean progress = _fresh_unify(that,vs,test);
//  //VARS.clear();  DUPS.clear();
//  //return progress;
//  throw unimpl();
//}
//
//// Apply 'this' structure on 'that'; no modifications to 'this'.  VARS maps
//// from the cloned LHS to the RHS replacement.
//private boolean _fresh_unify(TV2 that, TV2[] vs, boolean test) {
//  assert !is_unified() && !that.is_unified();
//
//  // Several trivial cases that do not really do any work
//  if( this==that ) return false;
//  if( that.is_dead() ) return false;
//  if( this.is_dead() ) return that.union(this); // Kill 'that', same as LHS
//  if( this.is_nil() || that.is_nil() ) return false;
//
//  // Check for closing cycles
//  TV2 prior = VARS.get(this);
//  if( prior!=null )           // Been there, done that?  Return prior mapping
//    return prior.find()._unify(that, test);
//  if( cycle_equals(that) ) return vput(that,false);
//
//  if( that.is_err() ) return vput(that,false); // That is an error, ignore 'this' and no progress
//  if( this.is_err() ) return vput(that,_unify(that,test));
//
//  // Famous 'occurs-check', switch to normal unify
//  if( occurs_in( vs ) ) return vput(that,_unify(that,test));
//  // Either side is a Leaf, unify to the other (perhaps with a fresh copy)
//  if( this.is_leaf() ) return vput(that,false); // Lazy map LHS tvar to RHS
//  if( that.is_leaf() )          // RHS is a leaf tvar; union with a copy of LHS
//    return test || vput(that,that.union(repl(vs)));
//  // Bases MEET cons in RHS
//  if( is_base() && that.is_base() ) return vput(that,fresh_base(that,test));
//
//  // Should be structurally equal now
//  if( !Util.eq(_name,that._name) )
//    throw com.cliffc.aa.AA.unimpl(); // unification error
//
//  // Structural recursion unification, lazy on LHS
//  boolean progress = vput(that,false); // Early set, to stop cycles
//  for( Comparable key : _args.keySet() ) {
//    TV2 lhs =      get(key);  assert lhs!=null;
//    TV2 rhs = that.get(key);
//    if( rhs==null ) {         // No RHS to unify against
//      if( !test ) {           // RHS is a fresh copy of the LHS
//        that.args_put(key,lhs.repl(vs));
//        Env.GVN.add_flow(that._deps); // Re-CallEpi
//      }
//      progress = true;
//    } else {
//      progress |= lhs._fresh_unify(rhs,vs,test);
//    }
//    if( progress && test ) return true;
//  }
//  return progress;
//}
//
//private boolean vput(TV2 that, boolean progress) { VARS.put(this,that); return progress; }
//private TV2 vput(TV2 that) { VARS.put(this,that); return that; }
//
//// Replicate LHS, including structure and cycles, replacing leafs as they appear
//private TV2 repl(TV2[] vs) {
//  assert !is_unified();        // Already chased these down
//  if( is_dead() ) return this; // Dead always unifies and wins
//  TV2 t = VARS.get(this);      // Prior answer?
//  if( t!=null ) return t;      // Been there, done that, return prior answer
//
//  if( is_leaf() ) // If occurs_in lexical scope, keep same variable, else make a new leaf
//    return vput( occurs_in(vs) ? this : make_leaf_ns(null,"TV2_repl_leaf") );
//
//  // Must replicate Base's, like a Mem or Obj.
//  if( is_base() ) return vput(make_base(null,_type,"TV2_repl_base"));
//  // A few no-arg variants (Nil, Fresh)
//  if( _args==null ) return vput(new TV2(_name,null,null,null,"TV2_repl_shallow"));
//
//  // Structural recursion replicate
//  TV2 rez = new TV2(_name, new NonBlockingHashMap<>(),null,null,"TV2_repl_deep");
//  VARS.put(this,rez); // Insert in dups BEFORE structural recursion, to stop cycles
//  for( Comparable key : _args.keySet() )
//    rez.args_put(key,get(key).repl(vs));
//  return rez;
//}
//
//// Do a repl, then rename all _ns lists.
//public TV2 repl_rename(TV2[]vs, HashMap<Node,Node> map) {
//  assert VARS.isEmpty() && DUPS.isEmpty();
//  TV2 tv = repl(vs);
//  _rename(tv,map);
//  VARS.clear();  DUPS.clear();
//  return tv;
//}
//private void _rename(TV2 tv, HashMap<Node,Node> map) {
//  if( DUPS.get(_uid) != null ) return; // Been there, remapped this
//  DUPS.put(_uid,this);                 // Only remap once
//  if( this==tv ) return;               // Using the same TVar
//  assert tv._ns==null && tv._deps==null;
//  tv._deps= _deps==null ? null : _deps.rename(map);
//  tv._ns  = _ns  ==null ? null : _ns  .rename(map);
//  if( _args != null )
//    for( Comparable key : _args.keySet() )
//      _args.get(key)._rename(tv.get(key),map);
//}
//
//
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
//
//// Unify the two memories only at the given aliases
//public boolean unify_alias(BitsAlias aliases, TV2 mem, boolean test) {
//  if( this==mem ) return false; // Already unified, no progress
//  assert (isa("Mem") || is_dead()) && mem.isa("Mem");
//  boolean progress = false;
//  TV2 tobj=null;              // For asserts
//  for( int alias : aliases ) {
//    TV2 tv = mem.get(alias);  // Get prior mem idea of this alias
//    if( tv==null ) continue;  // No idea (yet) from prior mem, nothing to unify
//    if( tobj==null ) tobj=tv; // All objects in this set of aliases are already unified
//    else assert tobj==tv;
//    progress |= unify_at(alias,tv,test); // Overwrite the default for alias
//    if( progress && test ) return true;
//  }
//  return progress;
//}
//
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
//// --------------------------------------------
//private static final VBitSet ODUPS = new VBitSet();
//boolean occurs_in(TV2[] vs) {
//  if( vs==null ) return false;
//  assert ODUPS.isEmpty();
//  boolean found = _occurs_in(vs);
//  ODUPS.clear();
//  return found;
//}
//
//// Does 'this' type occur in any scope, mid-definition (as a forward-ref).
//// If not, then return false (and typically make a fresh copy).
//// If it does, then 'this' reference is a recursive self-reference
//// and needs to keep the self-type instead of making fresh.
//boolean _occurs_in(TV2[] vs) {
//  // Can NOT modify 'vs' for U-F, because blows FreshNode hash.
//  for( TV2 v : vs )
//    if( _occurs_in_type(v.find()) )
//      return true;
//  return false;
//}
//
//boolean _occurs_in_type(TV2 x) {
//  assert !is_unified() && !x.is_unified();
//  if( x==this ) return true;
//  if( ODUPS.tset(x._uid) ) return false; // Been there, done that
//  if( !x.is_leaf() && x._args!=null )
//    for( Comparable key : x._args.keySet() )
//      if( _occurs_in_type(x.get(key)) )
//        return true;
//  return false;
//}
//
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
  public TV2 push_dep(CallEpiNode dep) {
    assert DEPS_VISIT.isEmpty();
    _push_update(dep);
    DEPS_VISIT.clear();
    return this;
  }
  private void _push_update(CallEpiNode dep) {
    assert !is_unified();
    if( DEPS_VISIT.tset(_uid) ) return;
    if( _deps!=null && _deps.get(dep._uid)!=null ) return; // Already here and in all children
    if( isa("Dead") ) return;
    _deps = _deps==null ? UQNodes.make(dep) : _deps.add(dep);
    if( _args!=null )
      for( String key : _args.keySet() ) // Structural recursion on a complex TV2
        get(key)._push_update(dep);
  }

  // Merge Dependent CallEpiNode lists, 'this' into 'that'.  Required to
  // trigger CEPI.unify_lift when types change structurally.
  private void merge_deps( TV2 that ) { if( !that.isa("Dead") ) that._deps = that._deps==null ? _deps : that._deps.addAll(_deps); }
  // Merge Node lists, 'this' into 'that', for easier debugging.
  // Lazily remove dead nodes on the fly.
  private void merge_ns  ( TV2 that ) { if( !that.isa("Dead") ) that._ns   = that._ns  ==null ? _ns   : that._ns  .addAll(_ns  ); }


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
    } else
      if( _args!=null )
        for( TV2 t : _args.values() )
          if( t!=null )
            t._get_dups(visit,dups);
    return dups;
  }

  // Fancy print for Debuggers - includes explicit U-F re-direction.
  // If debug is on, does NOT roll-up - no side effects.
  @Override public String toString() { return str(new SB(), new VBitSet(), get_dups(), true ).toString(); }
  public SB str(SB sb, VBitSet visit, VBitSet dups, boolean debug) {

    if( is_err () )  return sb.p(_type);
    if( is_base() )  return sb.p(_type);
    boolean dup = dups.get(_uid);
    if( is_leaf() ) {
      if( !debug ) throw unimpl();
      sb.p("V").p(_uid);
      return is_unified() ? _unified.str(sb.p(">>"), visit, dups, debug) : sb;
    }
    
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
      sb.p("@{");
      _type.str(sb,visit,null,debug); // Probably want a custom printer
      sb.p(' ');
      //if( _ids==null ) sb.p("_ ");
      //else for( int i=0; i<_ids.length; i++ )
      //       str(sb.p(' ').p(_ids[i]).p(" = "),visit,_args[i],dups).p(',');
      //if( _open ) sb.p(" ...,");
      //return sb.unchar().p("}");
      return sb.p("FIX STRUCT PRINTING");
    }

    // Generic structural T2
    sb.p("(").p(_name).p(" ");
    for( TV2 t : _args.values() ) str0(sb,visit,t,dups,debug).p(" ");
    return sb.unchar().p(")");
  }
  static private SB str0(SB sb, VBitSet visit, TV2 t, VBitSet dups, boolean debug) { return t==null ? sb.p("_") : t.str(sb,visit,dups,debug); }
}
