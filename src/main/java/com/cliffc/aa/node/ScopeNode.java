package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;

import java.util.HashMap;
import java.util.function.Predicate;

import static com.cliffc.aa.type.TypeFld.Access;
import static com.cliffc.aa.AA.MEM_IDX;

/**
 * Lexical-Scope Node.  Tracks control & phat memory, plus a stack frame (which
 * is just a NewNode).  The stack frame maps local variable names to Nodes and
 * is modeled as a true memory indirection - for true closures.  Unless there
 * is an upwards funarg the stack frame will optimize away.
 */
public class ScopeNode extends Node {

  /**
   * Mapping from type-variables to Types.  Types have a scope lifetime like values.
   */
  private final HashMap<String,ConTypeNode> _types; // user-typing type names
  private Ary<IfScope> _ifs;                 // Nested set of IF-exprs used to track balanced new-refs

  public ScopeNode(Parse open, boolean closure) {
    super(OP_SCOPE,null,null,null,null);
    if( closure ) { add_def(null); add_def(null); add_def(null); } // Wire up an early-function-exit path
    _types = new HashMap<>();
    _ifs = null;
    keep();
  }
  public ScopeNode(HashMap<String,ConTypeNode> types,  Node ctl, Node mem, Node ptr, Node rez) {
    super(OP_SCOPE,ctl,mem,ptr,rez);
    _types = types;
    keep();
  }

  // Add base types on startup
  public void init() {
    HashMap<String,Type> ts = new HashMap<>();
    Type.init0(ts);
    for( String tname : ts.keySet() )
      _types.put(tname,Env.GVN.init(new ConTypeNode(tname,ts.get(tname),Env.SCP_0)));
  }

  public   Node  ctrl() { return in(0); }
  public   Node  mem () { return in(MEM_IDX); }
  public   Node  ptr () { return in(2); }
  public   Node  rez () { return in(3); }
  public NewObjNode stk () { return (NewObjNode)ptr().in(0); }
  public <N extends Node> N set_ctrl( N n ) { set_def(0,n); return n; }
  public void set_ptr ( Node n) { set_def(2,n); }
  public void set_rez ( Node n) { set_def(3,n); }

  // Set a new deactive GVNd memory, ready for nested Node.ideal() calls.
  public Node set_mem( Node n) {
    assert n._val instanceof TypeMem || n._val ==Type.ANY || n._val ==Type.ALL;
    Node old = mem();
    set_def(MEM_IDX,n);
    if( old!=null ) {
      Env.GVN.add_work_all(old);
      if( old._uses._len <= 2 ) // DEFMEM and a MemSplit
        for( Node use : old._uses )
          if( use instanceof MemSplitNode )
            Env.GVN.add_mono(((MemSplitNode)use).join());
      old.add_flow_def_extra(n); // old loses a use, triggers extra
      Env.GVN.add_work_all(n);
    }
    return this;
  }
  public void replace_mem(Node st) {
    set_def(MEM_IDX,null);
    Node mem = Env.GVN.xform(st);
    set_def(MEM_IDX,mem);
  }
  @Override public boolean is_mem() { return true; }

  public Node get(String name) { return stk().get(name); }
  public boolean is_mutable(String name) { return stk().is_mutable(name); }

  public RegionNode early_ctrl() { return (RegionNode)in(4); }
  public    PhiNode early_mem () { return (   PhiNode)in(5); }
  public    PhiNode early_val () { return (   PhiNode)in(6); }
  public void       early_kill() { pop(); pop(); pop(); }

  // Name to type lookup, or null
  public ConTypeNode get_type(String name) { return _types.get(name);  }

  // Alias to TypeMemPtr lookup, or null
  public ConTypeNode get_type(int alias) {
    for( ConTypeNode ctn : _types.values() )
      if( ctn._t instanceof TypeMemPtr &&
          ((TypeMemPtr)ctn._t)._aliases.test(alias) )
        return ctn;
    return null;
  }
  
  // Extend the current Scope with a new type; cannot override existing name.
  public void add_type( String name, ConTypeNode t ) {
    assert _types.get(name)==null;
    _types.put( name, t );
  }

  public boolean is_closure() { assert _defs._len==4 || _defs._len==7; return _defs._len==7; }

  @Override public Node ideal_reduce() {
    Node ctrl = in(0).is_copy(0);
    if( ctrl != null ) { set_ctrl(ctrl); return this; }

    Node mem = mem();
    Node rez = rez();
    Type trez = rez==null ? null : rez._val;
    if( Env.GVN._opt_mode != GVNGCM.Mode.Parse &&   // Past parsing
        rez != null &&          // Have a return result
        // If type(rez) can never lift to any TMP, then we will not return a
        // pointer, and do not need the memory state on exit.
        (!TypeMemPtr.OOP0.dual().isa(trez) || trez==Type.XNIL) &&
        // And not already wiped it out
        !(mem instanceof ConNode && mem._val ==TypeMem.XMEM) )
      // Wipe out return memory
      return set_mem(Node.con(TypeMem.XMEM));

    return null;
  }
  @Override public Type value(GVNGCM.Mode opt_mode) { return Type.ALL; }
  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }

  // From a memory and a possible pointer-to-memory, find all the reachable
  // aliases and fold them into 'live'.  This is unlike other live_use
  // because this "turns around" the incoming live memory to also be the
  // demanded/used memory.
  static TypeMem compute_live_mem(Node mem, Node rez) {
    Type tmem = mem._val;
    Type trez = rez._val;
    if( !(tmem instanceof TypeMem ) ) return tmem.oob(TypeMem.ALLMEM); // Not a memory?
    if( TypeMemPtr.OOP.isa(trez) ) return ((TypeMem)tmem).flatten_fields(); // All possible pointers, so all memory is alive
    if( !(trez instanceof TypeMemPtr) ) return TypeMem.ANYMEM; // Not a pointer, basic live only
    if( trez.above_center() ) return TypeMem.ANYMEM; // Have infinite choices still, report basic live only
    // Find everything reachable from the pointer and memory, and report it all
    TypeMem tmem0 = (TypeMem)tmem;
    BitsAlias aliases = tmem0.all_reaching_aliases(((TypeMemPtr)trez)._aliases);
    return tmem0.slice_reaching_aliases(aliases).flatten_fields();
  }

  @Override public TypeMem live(GVNGCM.Mode opt_mode) {
    // Prim scope is not used past Call-Graph discovery
    if( this==Env.SCP_0 )  return opt_mode._CG ? TypeMem.DEAD : TypeMem.ALLMEM;
    if( opt_mode == GVNGCM.Mode.Parse ) return TypeMem.MEM;
    assert _uses._len==0;
    // All fields in all reachable pointers from rez() will be marked live
    return compute_live_mem(mem(),rez());
  }

  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    // The top scope is always alive, and represents what all future unparsed
    // code MIGHT do.
    if( this==Env.SCP_0 && opt_mode._CG )
      return TypeMem.DEAD;
    // Basic liveness ("You are Alive!") for control and returned value
    if( def == ctrl() ) return TypeMem.ALIVE;
    if( def == rez () ) return def.all_live().basic_live() ? TypeMem.LIVE_BOT : TypeMem.ANYMEM;
    // Returned display is dead in a whole program.
    // In a partial-program, whats in the display is exported to the next step.
    if( def == ptr () ) return opt_mode._CG ? TypeMem.DEAD : TypeMem.LIVE_BOT; // Returned display is dead after CG
    // Memory returns the compute_live_mem state in _live.  If rez() is a
    // pointer, this will include the memory slice.
    if( def == mem() )
      return opt_mode==GVNGCM.Mode.Parse ? TypeMem.ALLMEM : _live.flatten_fields();
    // Merging exit path
    return def._live;
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

  public void def_if( String name, Access mutable, boolean create ) {
    if( _ifs == null || _ifs._len==0 ) return; // Not inside an If
    _ifs.last().def(name,mutable,create);      // Var defined in arm of if
  }

  public Node check_if( boolean arm, Parse bad, GVNGCM gvn, Node ctrl, Node mem ) { return _ifs.last().check(this,arm,bad,gvn,ctrl,mem); }

  private static class IfScope {
    HashMap<String,Access> _tvars, _fvars;
    boolean _arm = true;
    void flip() { _arm = !_arm; }
    // Record creation on either arm of an if
    void def(String name, Access mutable, boolean create) {
      if( _tvars == null ) { _tvars = new HashMap<>(); _fvars = new HashMap<>(); }
      // If there was no prior create inside the same if, then this update
      // predates the if and is not involved in a partial-creation error
      if( !create && !_arm && _tvars.get(name) != null )
        _fvars.put(name,mutable);
      if( create ) {
        HashMap<String,Access> vars = _arm ? _tvars : _fvars;
        Access res = vars.put(name,mutable);
        assert res==null;         // No double-creation
      }
    }
    // Check for balanced creation, and insert errors on unbalanced
    Node check(ScopeNode scope, boolean arm, Parse bad, GVNGCM gvn, Node ctrl, Node mem) {
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
      HashMap<String,Access> vars = arm ? _fvars : _tvars;
      if( vars.isEmpty() ) return mem;
      mem.unkeep(2);             // Passed-in 'hooked' memory
      for( String name : vars.keySet() ) {
        String msg = "'"+name+"' not defined on "+arm+" arm of trinary";
        Node err = gvn.xform(new ErrNode(ctrl,bad,msg));
        // Exactly like a parser store of an error, on the missing side
        mem = gvn.xform(new StoreNode(mem,scope.ptr(),err,Access.Final,name,bad));
      }
      return mem.keep(2);        // Return 'hooked' memory
    }
  }
}
