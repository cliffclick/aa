package com.cliffc.aa.tvar;

import com.cliffc.aa.node.CallEpiNode;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.*;

import java.util.HashMap;
import java.util.HashSet;

import org.jetbrains.annotations.NotNull;

// Type Variable.  TVars unify (ala Tarjan Union-Find), and can have structure
// (such as "{ A -> B }").  TVars are tied to a TNode to enforce Type structure
// on Types.  TVars with no structure either refer to a plain Node, or get
// unioned into another TVar.  TVars with structure have to match structure to
// be unified, but then can be recursively unified.

public class TV2 {
  // Unique ID
  static private int UID=1;
  public final int _uid;
  // - Structural tag for the H-M "type", Args, Ret, Fun, Mem, Obj, Base (some
  // constant Type).  These typically have to be equal during unification (Base
  // Types MEET).
  // - Can also be "Fresh", which is a one-off indirection to another TV2 which
  // needs to be fresh-unified instead of normal-unification of this TV2.  The
  // freshable TV2 is in _args under the key "Fresh".
  // - Can also be "Unified", which is a one-off indirection for Tarjan U-F.
  // The unified TV2 is in _args under the key "Unified".
  private String _name;
  // Set of structural H-M parts.  Indexed by dense integer for fixed-size (ala
  // Args,Ret,Fun), indexed by sparse integer alias for TMem, indexed by String
  // for Obj field names.  Can be null if empty.
  public HashMap<Object,TV2> _args;

  // Base primitive types, not really tied to any Node.  TypeInt, TypeFlt.
  public final Type _type;

  // Set of dependent CallEpiNodes, to be re-worklisted if the called function changes TV2.
  public HashSet<CallEpiNode> _deps;

  // Debug only.  Set of unioned Nodes.  null for empty.  Helpful to track where TV2s come from.
  public HashSet<Node> _ns;     //
  public String _alloc_site;    // Creation site; used to track excessive creation.

  // Common constructor
  private TV2(@NotNull String name, HashMap<Object,TV2> args, Type type, HashSet<Node> ns, @NotNull String alloc_site) {
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
  public boolean is_leaf   () { return Util.eq(_name,"Leaf"   ); }
  public boolean is_unified() { return Util.eq(_name,"Unified"); }
  public boolean is_fresh  () { return Util.eq(_name,"Fresh"  ); }
  public boolean is_base   () { return Util.eq(_name,"Base"   ); }
  public TV2    get_unified() { assert is_unified(); return _args.get("Unified"); } // Accessor does NOT fold up U-F
  public TV2    get_fresh  () { assert is_fresh  (); return _args.get("Fresh"  ); } 

  // Public factories
  // Make a new TV2 attached to a Node.
  TV2 make_new(@NotNull String name, Node n, @NotNull String alloc_site) {
    HashSet<Node> ns = new HashSet<>();  ns.add(n);
    TV2 tv2 = new TV2(name,null,null,ns,alloc_site);
    assert tv2.is_leaf() && _args==null && _type==null && !tv2.is_fresh() && !tv2.is_base();
    return tv2;
  }
  // Make a new Fresh TV2 attached to a prior TV2
  TV2 make_fresh(TV2 tv, @NotNull String alloc_site) {
    HashMap<Object,TV2> args = new HashMap<>();
    args.put("Fresh",tv);
    TV2 fresh = new TV2("Fresh",args,null,tv._ns,alloc_site);
    assert fresh.is_fresh() && _args.size()==1;
    return fresh;
  }
  // Make a new primitive base TV2
  TV2 make_base(Type type, @NotNull String alloc_site) {
    TV2 tv2 = new TV2("Base",null,type,null,alloc_site);
    assert is_base() && !is_leaf() && !is_fresh();
    return tv2;
  }
  // Structural constructor
  TV2 make_tv(@NotNull String name, Node n, @NotNull String alloc_site, HashMap<Object,TV2> args) {
    HashSet<Node> ns = new HashSet<>();  ns.add(n);
    TV2 tv2 = new TV2(name,args,null,ns,alloc_site);
    assert !is_base() && !is_leaf() && !is_fresh();
    return tv2;
  }

  // --------------------------------------------
  // Classic Tarjan U-F with rollup
  public TV2 find() {
    if( !is_unified() ) return this;
    TV2 u = get_unified();
    if( !u.is_unified() ) return u;
    while( u.is_unified() ) u = u.get_unified();
    TV2 v = this;
    while( v != u ) { v._args.put("Unified",u); v = v.get_unified(); }
    return u;
  }
  
  // U-F union; this becomes that.  If 'this' was used in an CallEpi/Apply,
  // re-check the CallEpi.
  TV2 union(TV2 that, Ary<Node> work) {
    assert is_leaf() && !is_unified(); // Only leafs union; more complex things unify
    if( this==that ) return that;
    _args.clear();
    _args.put("Unified",that);
    assert is_unified() && !is_leaf();
    // Worklist: put updates on the worklist for revisiting
    if( work!=null ) work.addAll(_deps); // Re-CallEpi
    // Merge update lists, for future unions
    if( _deps != null ) {
      if( that._deps==null ) that._deps = _deps;
      else that._deps.addAll(this._deps);
      _deps=null;
    }
    // Merge Node list, for easier debugging
    if( _ns != null ) {
      if( that._ns==null ) that._ns = _ns;
      else that._ns.addAll(this._ns);
      this._ns=null;
    }
    ALLOCS.get(_alloc_site)._free++;
    return that;
  }


  // --------------------------------------------
  // Used in the recursive unification process.  During fresh_unify tracks the
  // mapping from LHS TV2s to RHS TVs.
  static private HashMap<TV2,TV2> VARS = new HashMap<>();
  // Used in the recursive unification process.  During unify detects cycles,
  // to allow cyclic unification.
  static private NonBlockingHashMapLong<TV2> DUPS = new NonBlockingHashMapLong<>();
  
  // Structural unification.  Both 'this' and that' are the same afterwards and
  // returns the unified bit.  Returns True if progress.
  boolean unify(TV2 that, Ary<Node> work, boolean test) {
    assert !this.is_unified() && !that.is_unified();
    if( this==that ) return false;
    assert !that.is_fresh();    // Only can lazy-clone LHS
    // Fresh_unify does not modify the LHS 'this', but forces the RHS 'that' to
    // match structurally.
    boolean progress;
    if( this.is_fresh() ) {     // Peel off fresh lazy & do a fresh-unify
      assert VARS.isEmpty();
      progress = get_fresh()._fresh_unify(that,work,test);
      VARS.clear();
    } else {
      // Normal unification, with side-effects allows both LHS and RHS
      assert DUPS.isEmpty();
      progress = _unify(that,work,test);
      DUPS.clear();
    }
    return progress;
  }

  private boolean _unify(TV2 that, Ary<Node> work, boolean test) {
    throw com.cliffc.aa.AA.unimpl();
  }

  private boolean _fresh_unify(TV2 that, Ary<Node> work, boolean test) {
    throw com.cliffc.aa.AA.unimpl();
  }

  
  // --------------------------------------------
  // Track allocation statistics
  static private class ACnts { int _malloc, _free; }
  static private HashMap<String,ACnts> ALLOCS = new HashMap<>(); // Counts at alloc sites
  
  public String pcounts() {
    throw com.cliffc.aa.AA.unimpl();
  }
  
  @Override public final String toString() { return str(new SB(),new VBitSet(),true).toString();  }

  // Pretty print
  public final SB str(SB sb, VBitSet bs, boolean debug) {
    // Explicit U-F chain
    if( is_unified() ) {
      if( debug ) sb.p("V").p(_uid).p(">>");
      return get_unified().str(sb,bs,debug);
    }
    if( _uid != -1 && bs.tset(_uid) )
      return sb.p("V").p(_uid).p("$");
    // Print all unioned nodes
    if( _ns!=null && _ns.size() != 0 ) { // Have any
      for( Node tn : _ns )               // For all unioned
        if( !tn.is_dead() ) { // Dead lazily cleared out, do not both  to print
          sb.p('N').p(tn.uid()).p(':');
          if( !debug ) break; // Debug, see them all; non-debug just the first
        }
      sb.unchar();
    } else                      // No unioned nodes
      sb.p("V").p(_uid);        // So just the _uid
    // Structural contents
    if( _args != null ) {
      sb.p(":[ ");
      for( Object key : _args.keySet() )
        _args.get(key).str(sb.p(key.toString()).p(':'),bs,debug).p(' ');
      sb.p("]");
    }
    return sb;
  }
}
