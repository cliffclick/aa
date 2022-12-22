package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;

import java.util.HashMap;
import java.util.Set;
import java.util.function.Predicate;

import static com.cliffc.aa.AA.*;
import static com.cliffc.aa.type.TypeFld.Access;

// Lexical-Scope Node.  Tracks control & phat memory, plus a stack frame (which
// is just a NewNode).  The stack frame maps local variable names to Nodes and
// is modeled as a true memory indirection - for true closures.  Unless there
// is an upwards funarg the stack frame will optimize away.
public class ScopeNode extends Node {

  // Mapping from type-variables to Types.  Types have a scope lifetime like values.
  private final HashMap<String,StructNode> _types; // user-typing type names
  private Ary<IfScope> _ifs;                 // Nested set of IF-exprs used to track balanced new-refs
  private final boolean _closure;

  public ScopeNode(boolean closure) {
    super(OP_SCOPE,null,null,null,null);
    add_def(null); add_def(null); add_def(null); // Wire up an early-function-exit path
    _closure = closure;
    _types = new HashMap<>();
    _ifs = null;
  }
  public ScopeNode(HashMap<String,StructNode> types,  Node ctl, Node mem, Node ptr, Node rez) {
    super(OP_SCOPE,ctl,mem,ptr,rez);
    _types = types;
    _closure = false;
  }
  @Override boolean is_CFG() { return true; }

  public       Node ctrl() { return in(CTL_IDX); }
  public       Node mem () { return in(MEM_IDX); }
  public StructNode stk () { return (StructNode)dsp().rec(); }
  public    NewNode dsp () { return (NewNode)ptr().in(0); }
  public   ProjNode ptr () { return (ProjNode)in(DSP_IDX); }
  public       Node rez () { return in(ARG_IDX); }
  public <N extends Node> N set_ctrl( N    n) { set_def(CTL_IDX,n); return n; }
  public void               set_ptr ( Node n) { set_def(DSP_IDX,n);           }
  public void               set_rez ( Node n) { set_def(ARG_IDX,n);           }

  // Set a new deactive GVNd memory, ready for nested Node.ideal() calls.
  public Node set_mem( Node n) {
    assert n._val instanceof TypeMem || n._val ==Type.ANY || n._val ==Type.ALL;
    Node old = mem();
    set_def(MEM_IDX,n);
    if( old!=null ) {
      Env.GVN.add_work_new(old);
      if( old._uses._len == 1 && // Only a MemSplit
          old._uses.at(0) instanceof MemSplitNode )
        Env.GVN.add_mono(((MemSplitNode)old._uses.at(0)).join());
      //old.add_flow_def_extra(n); // old loses a use, triggers extra
      //Env.GVN.add_work_new(n);
    }
    return this;
  }
  public void replace_mem(Node st) {
    // Remove the scope use of old memory, so the store becomes the ONLY use of
    // old memory, allowing the store to fold immediately.
    set_def(MEM_IDX,null);
    set_def(MEM_IDX,Env.GVN.xform(st));
  }
  @Override public boolean is_mem() { return true; }

  public Node get(String name) { return stk().in(name); }
  public boolean is_mutable(String name) { return stk().access(name)==Access.RW; }

  public RegionNode early_ctrl() { return (RegionNode)in(4); }
  public    PhiNode early_mem () { return (   PhiNode)in(5); }
  public    PhiNode early_val () { return (   PhiNode)in(6); }
  public void       early_kill() { set_def(4,null); set_def(5,null); set_def(6,null); }
  public static final int RET_IDX = 7;

  // Name to type lookup, or null
  public StructNode get_type(String name) { return _types.get(name);  }

  // Extend the current Scope with a new type; cannot override existing name.
  public void add_type( String name, StructNode t ) {
    assert _types.get(name)==null;
    _types.put( name, t );
    add_def(t);                 // Hook so it does not die
  }

  public Set<String> typeNames() { return _types.keySet(); }

  public boolean is_closure() { return _closure; }

  @Override public Node ideal_reduce() {
    Node ctrl = in(0).is_copy(0);
    if( ctrl != null ) { set_ctrl(ctrl); return this; }
    return null;
  }

  // Produce a tuple of the return result and a summary of all escaping
  // functions, on behalf of the following CEProjs.
  @Override public Type value() { return Type.CTRL; }

  // From a memory and a possible pointer-to-memory, find all the reachable
  // aliases and fold them into 'live'.  This is unlike other live_use
  // because this "turns around" the incoming live memory to also be the
  // demanded/used memory.
  static TypeMem compute_live_mem(ScopeNode scope, Node mem, Node rez) {
    Type tmem = mem._val;
    Type trez = rez._val;
    if( !(tmem instanceof TypeMem tmem0) ) return tmem.oob(TypeMem.ALLMEM); // Not a memory?
    if( TypeMemPtr.ISUSED.isa(trez) ) return tmem0.flatten_live_fields(); // All possible pointers, so all memory is alive
    // For function pointers, all memory returnable from any function is live.
    if( trez instanceof TypeFunPtr tfp && scope != null ) {
      TypeMem tmem3 = TypeMem.ANYMEM;
      for( int i=ARG_IDX+1 ; i<scope._defs._len; i++ ) {
        if( !(scope.in(i) instanceof RetNode ret) ) continue;
        int fidx = ret.fidx();
        if( ret._val instanceof TypeTuple tret && tfp.test(fidx) ) {
          TypeMem post_call = (TypeMem)tret.at(MEM_IDX);
          TypeMem cepi_out;
          if( tmem0==post_call ) {
            cepi_out = tmem0;
          } else {
            Type trez2 = tret.at(REZ_IDX);
            BitsAlias esc_in = tfp.dsp() instanceof TypeMemPtr tmp ? tmp._aliases : BitsAlias.EMPTY;
            //cepi_out = CallEpiNode.live_out(tmem0, post_call, trez2, esc_in, null);
            throw unimpl();
          }
          tmem3 = (TypeMem)tmem3.meet(cepi_out);
        }
      }
      return tmem3.flatten_live_fields();
    }
    if( !(trez instanceof TypeMemPtr) ) return TypeMem.ANYMEM; // Not a pointer, basic live only
    if( trez.above_center() ) return TypeMem.ANYMEM; // Have infinite choices still, report basic live only
    // Find everything reachable from the pointer and memory, and report it all
    BitsAlias aliases = tmem0.all_reaching_aliases(((TypeMemPtr)trez)._aliases);
    return tmem0.slice_reaching_aliases(aliases).flatten_live_fields();
  }

  @Override public TypeMem live() {
    if( is_keep() ) return TypeMem.ALLMEM;
    // All fields in all reachable pointers from rez() will be marked live
    return compute_live_mem(this,mem(),rez());
  }

  @Override public Type live_use(Node def ) {
    // Basic liveness ("You are Alive!") for control and returned value
    if( def == ctrl() ) return Type.ALL;
    if( def == rez () ) return Type.ALL; // Returning a Scalar, including e.g. a mem ptr
    if( def == ptr () ) return Type.ALL; // Display must be kept-alive during e.g. parsing.
    // Memory returns the compute_live_mem state in _live.  If rez() is a
    // pointer, this will include the memory slice.
    if( def == mem() ) return _uses._len>0 && _uses.at(0)==Env.KEEP_ALIVE ? Type.ALL : _live;
    // Any function which may yet have unwired CallEpis, and so needs full
    // memory alive until all Calls are wired.
    if( def instanceof RetNode ) return _live;
    // Merging exit path, or ConType
    return def._live;
  }

  @Override public int hashCode() { return 123456789; }
  // ScopeNodes are never equal
  @Override public boolean equals(Object o) { return this==o; }
  // End of dominator tree; do not walk past
  @Override Node walk_dom_last(Predicate<Node> P) { return P.test(this) ? this : null; }

  @Override public boolean has_tvar() { return false; }
  
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

  public Node check_if( boolean arm, Node ptr, Parse bad, Node ctrl, Node mem ) { return _ifs.last().check(this,arm,ptr,bad,ctrl,mem); }

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
    Node check(ScopeNode scope, boolean arm, Node ptr, Parse bad, Node ctrl, Node mem) {
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
      for( String name : vars.keySet() ) {
        String msg = "'"+name+"' not defined on "+arm+" arm of trinary";
        // Exactly like a parser store of an error, on the missing side
        Node ld  = Env.GVN.xform(new LoadNode(mem,ptr,bad));
        Node err = Env.GVN.xform(new ErrNode(ctrl,bad,msg));
        Node setf= Env.GVN.xform(new SetFieldNode(name,Access.Final,ld,err,bad));
        mem = Env.GVN.xform(new StoreNode(mem,ptr,setf,bad));
      }
      return mem;
    }
  }
}
