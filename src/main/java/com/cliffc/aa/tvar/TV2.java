package com.cliffc.aa.tvar;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.CallEpiNode;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;
import org.jetbrains.annotations.NotNull;

import java.util.HashMap;

// Type Variable.  TVars unify (ala Tarjan Union-Find), and can have structure
// (such as "{ A -> B }").  TVars are tied to a TNode to enforce Type structure
// on Types.  TVars with no structure either refer to a plain Node, or get
// unioned into another TVar.  TVars with structure have to match structure to
// be unified, but then can be recursively unified.

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
  // - "Unified": a one-off indirection for Tarjan U-F.  The unified TV2 is
  // under the solo key "Unified".
  // - "Dead": a dead Node or a Type.ANY ConNode, and a dead TV2.  Unifies with
  // everything, wins all unifications, and has no structure.
  // - "Free": Nothing points to it, can be re-used.
  private String _name;
  // Set of structural H-M parts.  Indexed by dense integer for fixed-size (ala
  // Args,Ret,Fun), indexed by sparse integer alias for TMem, indexed by String
  // for Obj field names.  Can be null if empty.
  public NonBlockingHashMap<Object,TV2> _args;

  // Base primitive types, not really tied to any Node.  TypeInt, TypeFlt.
  public Type _type;

  // Set of dependent CallEpiNodes, to be re-worklisted if the called function changes TV2.
  public NonBlockingHashMapLong<CallEpiNode> _deps;

  // Debug only.  Set of unioned Nodes.  null for empty.  Helpful to track where TV2s come from.
  public NonBlockingHashMapLong<Node> _ns;     //
  public String _alloc_site;    // Creation site; used to track excessive creation.

  // Track allocation statistics
  static private class ACnts { int _malloc, _free; }
  static private final HashMap<String,ACnts> ALLOCS = new HashMap<>(); // Counts at alloc sites

  // Common constructor
  private TV2(@NotNull String name, NonBlockingHashMap<Object,TV2> args, Type type, NonBlockingHashMapLong<Node> ns, @NotNull String alloc_site) {
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
  public boolean isa(String s){ return Util.eq(_name,s); }
  public boolean is_leaf   () { return isa("Leaf"   ); }
  public boolean is_unified() { return isa("Unified"); }
  public boolean is_fresh  () { return isa("Fresh"  ); }
  public boolean is_base   () { return isa("Base"   ); }
  public boolean is_nil    () { return isa("Nil"    ); }
  public boolean is_dead   () { return isa("Dead"   ); }
  public boolean is_free   () { return isa("Free"   ); }
  public boolean is_tvar   () { return _args!=null && !is_unified() && !is_fresh(); }
  public TV2    get_unified() { assert is_unified(); return get("Unified"); }
  public TV2    get_fresh  () { assert is_fresh  (); return get("Fresh"  ); }
  public String name() { return _name; }

  // Get at a key, with U-F rollup
  public TV2 get( Object key ) {
    if( _args==null ) return null;
    TV2 tv = _args.get(key);
    if( tv==null ) return null;
    TV2 tv2 = tv.find();
    if( tv!=tv2 ) _args.put(key,tv2);
    return tv2;
  }

  // Unify-at a selected key
  public boolean unify_at(Object key, TV2 tv2, boolean test ) {
    assert is_tvar() && _args!=null;
    TV2 old = get(key);
    if( old!=null ) return tv2.unify(old,test);
    if( test ) return true;
    _args.put(key,tv2);
    merge_deps(tv2);            // Send deps about also
    Env.GVN.add_flow(_deps);    // Re-CallEpi
    return true;
  }

  // Reset-at a selected key, when a non-HM-structure change happens
  public void reset_at(Object o ) { _args.remove(o); }

  // --------------------------------------------
  // Public factories
  // Make a new TV2 attached to a Node.
  public static TV2 make_leaf(Node n, @NotNull String alloc_site) {
    return make_leaf_ns(new NonBlockingHashMapLong<Node>(){{ put(n._uid,n); }},alloc_site);
  }
  public static TV2 make_leaf_ns(NonBlockingHashMapLong<Node> ns, @NotNull String alloc_site) {
    TV2 tv2 = new TV2("Leaf",null,null,ns,alloc_site);
    assert tv2.is_leaf() && !tv2.is_fresh() && !tv2.is_base();
    return tv2;
  }
  // Make a new Fresh TV2 attached to a prior TV2
  public static TV2 make_fresh(TV2 tv, @NotNull String alloc_site) {
    assert tv.isa("Fun");
    NonBlockingHashMap<Object,TV2> args = new NonBlockingHashMap<>();
    args.put("Fresh",tv);
    TV2 fresh = new TV2("Fresh",args,null,tv._ns,alloc_site);
    assert fresh.is_fresh() && fresh._args.size()==1;
    return fresh;
  }
  // Make a new primitive base TV2
  public static TV2 make_base(Node n, Type type, @NotNull String alloc_site) {
    NonBlockingHashMapLong<Node> ns = n==null ? null : new NonBlockingHashMapLong<Node>(){{ put(n._uid,n); }};
    TV2 tv2 = new TV2("Base",null,type.widen(),ns,alloc_site);
    assert tv2.is_base() && !tv2.is_leaf() && !tv2.is_fresh();
    return tv2;
  }
  // Structural constructor, empty
  public static TV2 make(@NotNull String name, Node n, @NotNull String alloc_site ) { return make(name,n,alloc_site,new NonBlockingHashMap<>()); }
  // Structural constructor
  public static TV2 make(@NotNull String name, Node n, @NotNull String alloc_site, NonBlockingHashMap<Object,TV2> args) {
    assert args!=null;          // Must have some structure
    NonBlockingHashMapLong<Node> ns = new NonBlockingHashMapLong<>();  ns.put(n._uid,n);
    TV2 tv2 = new TV2(name,args,null,ns,alloc_site);
    assert !tv2.is_base() && !tv2.is_leaf() && !tv2.is_fresh();
    return tv2;
  }
  // Structural constructor from array of TVs
  public static TV2 make(@NotNull String name, Node n, @NotNull String alloc_site, Node... ntvs) {
    assert ntvs!=null;          // Must have some structure
    NonBlockingHashMap<Object,TV2> args = new NonBlockingHashMap<>();
    for( int i=0; i<ntvs.length; i++ )
      if( ntvs[i]!=null )
        args.put(i,ntvs[i].tvar());
    return make(name,n,alloc_site,args);
  }
  public static TV2 make(@NotNull String name, NonBlockingHashMapLong<Node> ns, @NotNull String alloc_site ) {
    TV2 tv2 = new TV2(name, new NonBlockingHashMap<>(),null,ns,alloc_site);
    assert !tv2.is_base() && !tv2.is_leaf() && !tv2.is_fresh();
    return tv2;
  }

  // Structural constructor for new memory
  public static TV2 make_mem(Node n, @NotNull String alloc_site) { return make("Mem",n,alloc_site,new NonBlockingHashMap<>()); }

  public static TV2 DEAD = new TV2("Dead",null,null,null,"static");
  public static TV2 NIL  = new TV2("Nil" ,null,null,null,"static");

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
  // Cyclic (structural) equals
  public final boolean eq( TV2 that ) {
    if( that==null ) return false;
    assert VARS.isEmpty() && DUPS.isEmpty();
    boolean eq = _eq(that);
    VARS.clear();  DUPS.clear();
    return eq;
  }
  private boolean _eq( TV2 that) {
    if( this==that ) return true;
    assert !is_unified() && !that.is_unified();
    if( !Util.eq(_name,that._name) ) return false;
    if( is_base() ) return _type==that._type; // Base types are equal if base _types are equal
    if( is_leaf() ) {                         // Leafs are equal if they always map the same
      TV2 eq2 = VARS.computeIfAbsent(this,k -> that);
      return that==eq2;
    }

    if( _args.size() != that._args.size() ) return false;
    // Cyclic check
    long luid = ((long)_uid<<32)|that._uid; // Make a unique id for the pair
    if( DUPS.get(luid)!=null ) return true; // Cyclic, wrapped.  Something else determines eq/ne
    DUPS.put(luid,this);                    // Mark for cycle

    // Structural recursion
    for( Object key : _args.keySet() )
      if( !get(key)._eq(that.get(key)) )
        return false;
    return true;
  }

  // True if args are equal
  public boolean eq(Node[] args) {
    for( int i=0; i<args.length; i++ )
      if( args[i]!=null && args[i].tvar()!=get(i) )
        return false;
    return true;
  }

  // --------------------------------------------
  // Classic Tarjan U-F with rollup
  public TV2 find() {
    if( !is_unified() ) return this;
    TV2 top = get_unified();
    if( !top.is_unified() ) return top;
    // Find U-F top
    while( top.is_unified() ) top = top.get_unified();
    TV2 v = this;               // Rerun, rolling up to top
  while( v != top ) v = v._union(top);
    return top;
  }

  // U-F union; 'this' becomes 'that'.  If 'this' was used in an CallEpi/Apply,
  // re-check the CallEpi.  Always returns true.
  public boolean union(TV2 that) {
    if( this==that ) return true;
    assert !is_unified() && !is_dead();
    // Worklist: put updates on the worklist for revisiting
    Env.GVN.add_flow(_deps); // Re-CallEpi
    if( _args==null ) _args = new NonBlockingHashMap<>();
    else _args.clear();
    _union(that);
    ALLOCS.get(_alloc_site)._free++;
    return true;
  }
  private TV2 _union(TV2 that) {
    TV2 old = _args.get("Unified");
    _args.put(_name="Unified",that);
    assert is_unified();
    merge_deps(that);           // Merge update lists, for future unions
    merge_ns  (that);           // Merge Node list, for easier debugging
    return old;
  }

  // --------------------------------------------
  // Used in the recursive unification process.  During fresh_unify tracks the
  // mapping from LHS TV2s to RHS TVs.
  private static final HashMap<TV2,TV2> VARS = new HashMap<>();
  // Used in the recursive unification process.  During unify detects cycles,
  // to allow cyclic unification.
  private static final NonBlockingHashMapLong<TV2> DUPS = new NonBlockingHashMapLong<>();

  // Structural unification.  Both 'this' and that' are the same afterwards.
  // Returns True if progress.
  public boolean unify(TV2 that, boolean test) {
    assert !this.is_unified() && !that.is_unified();
    if( this==that ) return false;
    assert DUPS.isEmpty() && VARS.isEmpty();
    // Fresh_unify does not modify the LHS 'this', but forces the RHS 'that' to
    // match structurally.
    boolean progress;
    if( this.is_fresh() ) {     // Peel off fresh lazy & do a fresh-unify
      progress = get_fresh()._fresh_unify(that,test);
    } else {
      // Normal unification, with side-effects allows both LHS and RHS
      progress = _unify(that,test);
    }
    VARS.clear();  DUPS.clear();
    return progress;
  }

  // Classic structural unification, no "fresh".  Unifies 'this' into 'that'.
  // Both 'this' and 'that' are the same afterwards.  Returns true if progress.
  private boolean _unify(TV2 that, boolean test) {
    assert !is_unified() && !that.is_unified();
    if( this==that ) return false;
    // NIL always loses and makes no progress (no structure implications)
    if( this.is_nil () ) return false;
    if( that.is_nil () ) return false;
    if( test ) return true;
    // Dead wins all
    if( this.is_dead() ) return that.union(this);
    if( that.is_dead() ) return this.union(that);
    // Already checks that inputs are not fresh and not unified.
    // Check for simple, non-recursive, unification.
    if( this.is_base() && that.is_base() ) return unify_base(that);
    // Two leafs union in either order, so keep lower uid
    if( this.is_leaf() && that.is_leaf() && _uid < that._uid ) return that.union(this);
    if( this.is_leaf() ) return this.union(that);
    if( that.is_leaf() ) return that.union(this);

    assert Util.eq(_name,that._name); // Construction error?  Might be a runtime error.
    assert _args!=that._args; // Efficiency hack elsewhere if this is true here

    // Cycle check.
    long luid = ((long)_uid<<32)|that._uid; // Make a unique id for the pair
    TV2 rez = DUPS.get(luid);
    if( rez!=null ) return true; // Been there, done that
    DUPS.put(luid,that);         // Close cycles

    // Structural recursion unification, this into that.
    for( Object key : _args.keySet() ) {
      TV2 vthis =       get(key);
      TV2 vthat =  that.get(key);
      if( vthis!=null )
        if( vthat==null ) {
          that._args.put(key,vthis);
          that.merge_deps(vthis);
        } else vthis._unify(vthat,false);
    }

    // TODO: Check for being equal, cyclic-ly, and return a prior if possible.
    return union(that);
  }

  private boolean unify_base(TV2 that) {
    that._type = _type.meet(that._type);
    return union(that);
  }
  private boolean fresh_base(TV2 that, boolean test) {
    // TODO: prototype does meet here
    assert this._type == that._type;
    return false;
  }


  // Apply 'this' structure on 'that'; no modifications to 'this'.  VARS maps
  // from the cloned LHS to the RHS replacement.
  private boolean _fresh_unify(TV2 that, boolean test) {
    assert !is_unified() && !that.is_unified();

    if( this==that ) return false;
    if( that.is_dead() ) return false;
    if( this.is_dead() ) return that.union(this); // Kill 'that', same as LHS
    if( this.is_nil() && that.is_nil() ) return false;

    TV2 prior = VARS.get(this);
    if( prior!=null )           // Been there, done that?  Return prior mapping
      return prior.find()._unify(that, test);
    VARS.put(this,that);        // Save it for next time; repeats unify the same way

    return _fresh_unify_impl( that, test );
  }
  private boolean _fresh_unify_impl(TV2 that, boolean test) {

    if( is_base() && that.is_base() ) // Will definitely make progress
      return fresh_base(that,test);
    if( is_leaf() ) return false;     // Lazy map LHS tvar to RHS
    if( that.is_leaf() || that.is_nil() )  // RHS is a leaf tvar; union with a copy of LHS
      return that.union(repl());

    // RHS is also a lazy clone, which if cloned, will not be part of any
    // other structure.  When unioned with the clone of the LHS, the result
    // is not part of anything direct... but the structures still have to
    // align for the returned T2.  Make a replica & unify (e.g. stop being lazy).
    if( that.is_fresh() && !this.is_fresh() )
      that = that.get_fresh(); //.repl();  // TODO: no repl?

    if( !Util.eq(_name,that._name) )
      throw com.cliffc.aa.AA.unimpl(); // unification error
    // Structural recursion unification, lazy on LHS
    boolean progress = false;
    for( Object key : _args.keySet() ) {
      TV2 lhs =      get(key);
      TV2 rhs = that.get(key);
      if( rhs==null ) {
        if( !test ) {
          that._args.put(key,lhs.repl());
          Env.GVN.add_flow(that._deps); // Re-CallEpi
        }
        progress = true;
      } else {
        progress |= lhs._fresh_unify(rhs,test);
      }
      if( progress && test ) return true;
    }
    return progress;
  }

  // Replicate LHS, including structure and cycles, replacing leafs as they appear
  private static final HashMap<TV2,TV2> REPL = new HashMap<>();
  TV2 repl() {
    assert REPL.isEmpty();
    TV2 repl = _repl0();
    REPL.clear();
    return repl;
  }
  private TV2 _repl0() {
    if( is_dead() ) return this; // Dead always unifies and wins
    assert !is_unified();        // Already chased these down
    TV2 t = REPL.get(this);      // Prior answer?
    if( t!=null ) return t;      // Been there, done that, return prior answer
    t = _repl1();                // Make a private copy
    REPL.put(this,t);
    return t;
  }
  private TV2 _repl1() {
    if( is_leaf() )             // LHS is a leaf, make a new one for RHS
      return make_leaf_ns(null,"TV2_repl_leaf");
    // Must replicate Base's, like a Mem or Obj.
    if( is_base() ) return make_base(null,_type,"TV2_repl_base");
    // A few no-arg variants (Nil, Fresh)
    if( _args==null ) return new TV2(_name,null,null,null,"TV2_repl_shallow");

    // Structural recursion replicate
    TV2 rez = new TV2(_name, new NonBlockingHashMap<>(),null,null,"TV2_repl_deep");
    REPL.put(this,rez); // Insert in dups BEFORE structural recursion, to stop cycles
    for( Object key : _args.keySet() )
      rez._args.put(key,get(key)._repl0());
    return rez;
  }

  // --------------------------------------------

  // Used by Loads and Stores.  Unify tv against all aliases at this field
  // only.  Aliases are either produced by the Parser (so very generic) or from
  // forwards-flow from News and very specific.  Ignore the generic ones until
  // they refine.  TODO: As aliases further refine, need to undo-redo prior
  // unifies against larger/weaker aliases.
  public boolean unify_alias_fld(Node ldst, BitsAlias aliases, String fld, TV2 tv, boolean test, String alloc_site) {
    assert isa("Mem");
    boolean progress=false;
    for( int alias : aliases ) {
      if( alias <= BitsAlias.AARY ) return false; // No unify on parser-specific values
      TV2 tobj = get(alias);
      if( tobj == null ) {
        if( test ) return true; // Definitely will be progress
        progress = true;
        TV2 tvo = make("Obj",ldst,alloc_site);
        _args.put(alias,tvo);
        tvo._args.put(fld,tv);
      } else if( !tobj.isa("Dead") ) {
        assert tobj.isa("Obj");
        progress = tobj.unify_at(fld,tv.find(),test);
      } // else dead, no progress
      if( progress && test ) return progress; // Shortcut
    }
    return progress;
  }

  // Unify the two memories only at the given aliases
  public boolean unify_alias(BitsAlias aliases, TV2 mem, boolean test) {
    if( this==mem ) return false; // Already unified, no progress
    assert isa("Mem") && mem.isa("Mem");
    boolean progress = false;
    TV2 tobj=null;              // For asserts
    for( int alias : aliases ) {
      TV2 tv = mem.get(alias);  // Get prior mem idea of this alias
      if( tv==null ) continue;  // No idea (yet) from prior mem, nothing to unify
      if( tobj==null ) tobj=tv; // All objects in this set of aliases are already unified
      else assert tobj==tv;
      progress |= unify_at(alias,tv,test); // Overwrite the default for alias
      if( progress && test ) return true;
    }
    return progress;
  }

  // --------------------------------------------
  // Find instances of 'tv' inside of 'this' via structural recursion.  Walk
  // the matching Type at the same time.  Report the first one found, and
  // assert all the others have the same Type.
  public Type find_tvar(Type t, TV2 tv) {
    assert DUPS.isEmpty();
    Type rez = _find_tvar(t,tv,null);
    DUPS.clear();
    return rez;
  }
  private Type _find_tvar(Type t, TV2 tv, Type rez) {
    if( tv.isa("Dead") ) return rez;
    if( tv==this ) {
      assert rez==null || rez==t || rez.widen()==t.widen(): "Found multiple refs to tvar with diff types, "+ t +","+ rez;
      return t;
    }
    switch(_name) {
    case "Mem":
      if( t ==Type.ANY ) return rez; // No substructure in type
      TypeMem tmem = (TypeMem)t;
      for( Object key : _args.keySet() ) {
        TypeObj to = tmem.at((Integer) key);
        TV2 obj = get(key);
        if( obj!=null )
          rez = obj._find_tvar(to,tv,rez);
      }
      return rez;
    case "Obj":
      if( t==TypeObj.UNUSED )
        return rez; // No substructure in type
      TypeStruct ts = (TypeStruct)t; //
      for( Object key : _args.keySet() ) {
        int idx = ts.find((String)key);
        if( idx!= -1 )          // If field exists
          rez = get(key)._find_tvar(ts.at(idx),tv,rez);
      }
      return rez;
    case "Fresh":
      if( t ==Type.ALL ) return rez; // No substructure in type
      //return get_fresh()._find_tvar(t,tv,rez);
      return rez;               // TODO: Not sure if should inside Fresh
    case "Fun":
      if( t ==Type.ALL ) return rez; // No substructure in type
      if( t.is_forward_ref() ) return rez;
      assert t instanceof TypeFunPtr;
      // TypeFunPtrs carry only a set of FIDXS & a DISPLAY.
      // Hence no other Type is available here for lifting.
      return rez;
    //case "Ret":
    //  TypeTuple tt = (TypeTuple)t;
    //  for( int i=0; i<tt.len(); i++ )
    //    rez = get(i)._find_tvar(tt.at(i),tv,rez);
    //  return rez;
    case "Base":
    case "Dead":
    case "Leaf":
    case "Nil":
      return rez; // No substructure in TV2 and not equal already

    default: throw com.cliffc.aa.AA.unimpl();
    }
  }

  // --------------------------------------------
  // This is a TV2 function that is the target of 'fresh', i.e., this function
  // might be fresh-unified with some other function.  Push the application
  // down the function parts; if any changes the fresh-application may make
  // progress.
  static final VBitSet DEPS_VISIT  = new VBitSet();
  public void push_dep(CallEpiNode dep) {
    if( is_fresh() )
      get_fresh().init_dep(dep);
  }
  public TV2 init_dep(CallEpiNode dep) { assert DEPS_VISIT.isEmpty(); _push_update(dep); DEPS_VISIT.clear(); return this; }
  private void _push_update(CallEpiNode dep) {
    assert !is_unified();
    if( DEPS_VISIT.tset(_uid) ) return;
    if( _deps==null ) _deps = new NonBlockingHashMapLong<>();
    _deps.put(dep._uid,dep);
    if( _args!=null )
      for( Object key : _args.keySet() ) // Structural recursion on a complex TV2
        get(key)._push_update(dep);
  }

  // Merge Dependent CallEpiNode lists, 'this' into 'that'.  Required to
  // trigger CEPI.unify_lift when types change structurally.
  @SuppressWarnings("unchecked")
  private void merge_deps( TV2 that ) {
    if( _deps == null ) return;
    if( that._deps==null && is_unified() ) { // A little linear logic
      that._deps = _deps;
      _deps = null;
      return;
    }
    if( that._deps==null ) that._deps = new NonBlockingHashMapLong<>();
    for( CallEpiNode n : _deps.values() )
      // Must filter before merge
      if( n.is_dead() ) _deps.remove(n._uid);
      else              that._deps.put(n._uid,n);
  }

  // Merge Node lists, 'this' into 'that', for easier debugging.
  // Lazily remove dead nodes on the fly.
  private void merge_ns( TV2 that) {
    if( _ns != null ) {
      if( that._ns==null ) that._ns = _ns;
      else for( Node n : _ns.values() )
             if( !n.is_dead() )    // Must filter before merge
               that._ns.put(n._uid,n);
      _ns=null;
    }
  }


  // Pretty print
  @Override public final String toString() {
    NonBlockingHashMapLong<String> dups = new NonBlockingHashMapLong<>();
    VBitSet bs = new VBitSet();
    find_dups(bs,dups,0);
    return str(new SB(),bs.clr(),dups,true).toString();
  }

  // These TV2 types get large, with complex sharing patterns.
  // Need to find the sharing to pretty-print the shared parts.
  final int find_dups(VBitSet bs, NonBlockingHashMapLong<String> dups, int scnt) {
    if( bs.tset(_uid) ) {
      if( is_base() || is_dead() ) return scnt;
      dups.put(_uid,new String(new char[]{(char)('A'+scnt)}));
      return scnt+1;
    }
    if( _args!=null )
      for( TV2 tv : _args.values() )
        if( !(isa("Mem") && _args.get(7) == tv) )
          scnt = tv.find_dups(bs,dups,scnt);
    return scnt;
  }

  // Pretty print
  public final SB str(SB sb, VBitSet bs, NonBlockingHashMapLong<String> dups, boolean debug) {
    if( is_dead() ) return sb.p("Dead"); // Do not print NS

    String stv = dups.get(_uid);
    if( stv!=null ) {
      sb.p('$').p(stv);
      if( bs.tset(_uid) ) return sb;
      sb.p(':');
    }
    // Explicit U-F chain
    if( is_unified() ) {
      if( debug ) sb.p("V").p(_uid).p(">>");
      return _args.get("Unified").str(sb,bs,dups,debug);
    }
    if( is_fresh() )
      return get_fresh().str(sb.p('#'),bs,dups,debug);

    (is_base() ? sb.p(_type) : sb.p(_name)).p(':');
    // Print all unioned nodes
    if( _ns!=null && _ns.size() != 0 ) { // Have any
      for( Node tn : _ns.values() )      // For all unioned
        if( !tn.is_dead() ) { // Dead lazily cleared out, do not bother to print
          sb.p('N').p(tn._uid).p(':');
          if( !debug ) break; // Debug, see them all; non-debug just the first
        }
    } else                      // No unioned nodes
      sb.p("V").p(_uid);        // So just the _uid
    // Structural contents
    if( _args != null ) {
      switch(_name) {
      case "Fun":
        sb.p(":{ ");
        TV2 args = _args.get("Args");
        if( args==null ) sb.p("Args"); else args.str(sb,bs,dups,debug);
        sb.p(" -> ");
        TV2 ret = _args.get("Ret");
        if( ret ==null ) sb.p("Ret" ); else ret .str(sb,bs,dups,debug);
        sb.p(" }");
        break;
      default:
        sb.p(":[ ");
        for( Object key : _args.keySet() )
          if( isa("Mem") && key instanceof Integer && ((Integer)key)==7 ) sb.p("7:PRIMS ");
          else _args.get(key).str(sb.p(key.toString()).p(':'),bs,dups,debug).p(' ');
        sb.p("]");
      }
    }
    return sb;
  }
}
