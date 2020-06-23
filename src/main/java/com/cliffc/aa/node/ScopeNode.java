package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;

import java.util.HashMap;
import java.util.function.Predicate;

// Lexical-Scope Node.  Tracks control & phat memory, plus a stack frame (which
// is just a NewNode).  The stack frame maps local variable names to Nodes and
// is modeled as a true memory indirection - for true closures.  Unless there
// is an upwards funarg the stack frame will optimize away.
public class ScopeNode extends Node {

  // Mapping from type-variables to Types.  Types have a scope lifetime like values.
  private final HashMap<String,Type> _types; // user-typing type names
  private Ary<IfScope> _ifs;                 // Nested set of IF-exprs used to track balanced new-refs
  public final Parse _debug_open;
  public Parse _debug_close;

  public ScopeNode(Parse open, boolean closure) {
    super(OP_SCOPE,null,null,null,null);
    if( closure ) { add_def(null); add_def(null); add_def(null); } // Wire up an early-function-exit path
    _debug_open = open;
    _types = new HashMap<>();
    _ifs = null;
    keep();
  }

  // Add base types on startup
  public void init0() { Type.init0(_types); }

  public   Node  ctrl() { return in(0); }
  public   Node  mem () { return in(1); }
  public   Node  ptr () { return in(2); }
  public   Node  rez () { return in(3); }
  public NewObjNode stk () { return (NewObjNode)ptr().in(0); }
  public <N extends Node> N set_ctrl( N n, GVNGCM gvn) { set_def(0,n,gvn); return n; }
  public void set_ptr ( Node n, GVNGCM gvn) { set_def(2,n,gvn); }
  public void set_rez ( Node n, GVNGCM gvn) { set_def(3,n,gvn); }
  // Set a new deactive GVNd memory, ready for nested Node.ideal() calls.
  public Node set_mem( Node n, GVNGCM gvn) {
    assert n==null || (gvn.touched(n) && gvn.type(n) instanceof TypeMem);
    set_def(1,n,gvn);
    return this;
  }
  // Set a new active NOT-GVNd memory, ready for directly updating memory edges.
  public MemMergeNode set_active_mem( MemMergeNode mmem, GVNGCM gvn) {
    assert !gvn.touched(mmem);
    set_def(1,mmem,gvn);
    return mmem;
  }
  // Convert a possibly active memory to an inactive memory.
  public Node all_mem( GVNGCM gvn ) {
    Node mem = mem();
    if( gvn.touched(mem) ) return mem; // Already not active
    assert mem._uses._len==1;          // Only self usage
    mem.keep();                 // Remove this scope usage without deleting
    set_mem(null,gvn);          // Remove this scope usage
    mem = gvn.xform(mem.unhook());// Then xform like a new node
    set_mem(mem,gvn);           // Re-insert
    return mem;                 // Return inactive memory
  }

  public Node get(String name) { return stk().get(name); }
  public boolean is_mutable(String name) { return stk().is_mutable(name); }

  public RegionNode early_ctrl() { return (RegionNode)in(4); }
  public    PhiNode early_mem () { return (   PhiNode)in(5); }
  public    PhiNode early_val () { return (   PhiNode)in(6); }
  public void       early_kill() { pop(); pop(); pop(); }

  // Name to type lookup, or null
  public Type get_type(String name) { return _types.get(name);  }
  public HashMap<String,Type> types() { return _types; }

  // Extend the current Scope with a new type; cannot override existing name.
  public void add_type( String name, Type t ) {
    assert _types.get(name)==null;
    _types.put( name, t );
  }
  // Replacing a recursive type with final definition
  public void def_type( String name, Type t ) {
    assert _types.get(name)!=null;
    _types.put( name, t );
  }

  public boolean is_closure() { assert _defs._len==4 || _defs._len==7; return _defs._len==7; }

  @Override public Node ideal(GVNGCM gvn, int level) {
    Node mem = mem();
    Node rez = rez();
    Type trez = rez==null ? null : gvn.type(rez);
    if( gvn._opt_mode != 0 &&   // Past parsing
        rez != null &&          // Have a return result
        // If type(rez) can never lift to any TMP, then we will not return a
        // pointer, and do not need the memory state on exit.
        !TypeMemPtr.OOP0.dual().isa(trez) &&
        // And not already wiped it out
        !(mem instanceof ConNode && gvn.type(mem)==TypeMem.XMEM) )
      // Wipe out return memory
      return set_mem(gvn.add_work(gvn.con(TypeMem.XMEM)), gvn);


    // Load can move past a Join if all aliases align.
    if( mem instanceof MemJoinNode &&
        trez instanceof TypeMemPtr ) {
      Node jmem = ((MemJoinNode)mem).can_bypass(gvn,(TypeMemPtr)trez);
      // Aliases have to work out.  Also, must keep the isa
      // types, which can fail for cycles until GCP.
      if( jmem != null && gvn.type(jmem).isa(gvn.type(mem)) )
        return set_mem(jmem,gvn);
    }

    return null;
  }
  @Override public Type value(GVNGCM gvn) { return Type.ALL; }
  @Override public boolean basic_liveness() { return false; }

  // From a memory and a possible pointer-to-memory, find all the reachable
  // aliases and fold them into 'live'.  This is unlike other live_use
  // because this "turns around" the incoming live memory to also be the
  // demanded/used memory.
  static TypeMem compute_live_mem(GVNGCM gvn, Node mem, Node rez) {
    Type tmem = gvn.type(mem);
    Type trez = gvn.type(rez);
    if( !(tmem instanceof TypeMem ) ) return tmem.oob(TypeMem.ALLMEM); // Not a memory?
    if( TypeMemPtr.OOP.isa(trez) ) return (TypeMem)tmem; // All possible pointers, so all memory is alive
    if( !(trez instanceof TypeMemPtr) ) return TypeMem.ANYMEM; // Not a pointer, basic live only
    if( trez.above_center() ) return TypeMem.ANYMEM; // Have infinite choices still, report basic live only
    // Find everything reachable from the pointer and memory, and report it all
    return ((TypeMem)tmem).slice_all_aliases_plus_children(((TypeMemPtr)trez)._aliases);
  }
  @Override public TypeMem live( GVNGCM gvn) {
    // The top scope is always alive, and represents what all future unparsed
    // code MIGHT do.
    if( this==Env.SCP_0 )
      return gvn._opt_mode < 2 ? TypeMem.ALLMEM : TypeMem.DEAD;
    assert _uses._len==0;
    // All fields in all reachable pointers from rez() will be marked live
    return compute_live_mem(gvn,mem(),rez());
  }

  @Override public TypeMem live_use( GVNGCM gvn, Node def ) {
    // The top scope is always alive, and represents what all future unparsed
    // code MIGHT do.
    if( this==Env.SCP_0 )
      return gvn._opt_mode < 2 ? TypeMem.ALLMEM : TypeMem.DEAD;
    // Basic liveness ("You are Alive!") for control and returned value
    if( def == ctrl() ) return TypeMem.ALIVE;
    if( def == rez () ) return def.basic_liveness() ? TypeMem.ALIVE : TypeMem.ANYMEM;
    if( def == ptr () ) return TypeMem.DEAD; // Returned display is dead
    // Memory returns the compute_live_mem state in _live.  If rez() is a
    // pointer, this will include the memory slice.
    assert def == mem();
    return _live;
  }

  @Override public int hashCode() { return 123456789; }
  // ScopeNodes are never equal
  @Override public boolean equals(Object o) { return this==o; }
  // End of dominator tree; do not walk past
  @Override Node walk_dom_last(Predicate<Node> P) { return P.test(this) ? this : null; }

  // Create an if-scope and start tracking vars
  public void push_if() {
    if( _ifs == null ) _ifs = new Ary<>(new IfScope[1],0);
    _ifs.push(new IfScope());
  }
  // Flip true-arm for false-arm
  public void flip_if() { _ifs.last().flip(); }

  // Pop ifscope
  public void pop_if() { _ifs.pop(); }

  // Test for being inside a ?: expression
  public boolean test_if() { return _ifs!=null && !_ifs.isEmpty(); }

  public void def_if( String name, byte mutable, boolean create ) {
    if( _ifs == null || _ifs._len==0 ) return; // Not inside an If
    _ifs.last().def(name,mutable,create);      // Var defined in arm of if
  }

  public Node check_if( boolean arm, Parse bad, GVNGCM gvn, Node ctrl, Node ptr, Node mem ) { return _ifs.last().check(this,arm,bad,gvn,ctrl,ptr,mem); }

  private static class IfScope {
    HashMap<String,Byte> _tvars, _fvars;
    boolean _arm = true;
    void flip() { _arm = !_arm; }
    // Record creation on either arm of an if
    void def(String name, byte mutable, boolean create) {
      if( _tvars == null ) { _tvars = new HashMap<>(); _fvars = new HashMap<>(); }
      // If there was no prior create inside the same if, then this update
      // predates the if and is not involved in a partial-creation error
      if( !create && !_arm && _tvars.get(name) != null )
        _fvars.put(name,mutable);
      if( create ) {
        HashMap<String,Byte> vars = _arm ? _tvars : _fvars;
        Byte res = vars.put(name,mutable);
        assert res==null;         // No double-creation
      }
    }
    // Check for balanced creation, and insert errors on unbalanced
    Node check(ScopeNode scope, boolean arm, Parse bad, GVNGCM gvn, Node ctrl, Node ptr, Node mem) {
      if( _tvars == null ) return mem; // No new vars on either arm
      // Pull from both variable sets names that are common to both
      if( arm ) {               // Only do it first time
        Ary<String> names = new Ary<>(String.class).addAll(_tvars.keySet());
        while( !names.isEmpty() ) {
          String name = names.pop();
          if( _fvars.remove(name)!=null ) _tvars.remove(name);
        }
      }
      // Everything in this set is a partially-created variable error
      HashMap<String,Byte> vars = arm ? _fvars : _tvars;
      if( vars.isEmpty() ) return mem;
      MemMergeNode mmem = new MemMergeNode(mem.unhook());
      for( String name : vars.keySet() ) {
        String msg = bad.errMsg("'"+name+"' not defined on "+arm+" arm of trinary");
        Node err = gvn.xform(new ErrNode(ctrl,msg,null));
        // Exactly like a parser store of an error, on the missing side
        int alias = scope.stk()._alias; // Alias for scope
        Node omem = mmem.active_obj(alias);
        Node st = gvn.xform(new StoreNode(omem,scope.ptr(),err,TypeStruct.FFNL,name,bad));
        int idx = mmem.make_alias2idx(alias); // Precise alias update
        mmem.set_def(idx,st,gvn);
      }
      return gvn.xform(mmem.deactive(gvn)).keep();
    }
  }
}
