package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeStruct;
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

  public ScopeNode(boolean closure) {
    super(OP_SCOPE,null,null,null,null);
    if( closure ) { add_def(null); add_def(null); add_def(null); } // Wire up an early-function-exit path
    _types = new HashMap<>();
    _ifs = null;
    keep();
  }

  // Add base types on startup
  public void init0() { Type.init0(_types); }

  public   Node ctrl() { return in(0); }
  public   Node mem () { return in(1); }
  public   Node ptr () { return in(2); }
  public NewNode stk() { return (NewNode)ptr().in(0); }
  public <N extends Node> N set_ctrl( N n, GVNGCM gvn) { set_def(0,n,gvn); return n; }
  public void set_mem ( Node n, GVNGCM gvn) { set_def(1,n,gvn); }
  public void set_ptr ( Node n, GVNGCM gvn) { set_def(2,n,gvn); }

  public Node get(String name) { return stk().get(name); }
  public boolean exists(String name) { return get(name)!=null; }
  public boolean is_mutable(String name) { return stk().is_mutable(name); }

  public RegionNode early_ctrl() { return (RegionNode)in(3); }
  public    PhiNode early_mem () { return (   PhiNode)in(4); }
  public    PhiNode early_val () { return (   PhiNode)in(5); }
  public void       early_kill() { pop(); pop(); pop(); }

  // Name to type lookup, or null
  public Type get_type(String name) { return _types.get(name);  }
  public HashMap<String,Type> types() { return _types; }

  // Extend the current Scope with a new type; cannot override existing name.
  public void add_type( String name, Type t ) {
    assert _types.get(name)==null;
    _types.put( name, t );
  }

  public boolean early() { return _defs._len==6; }

  @Override public Node ideal(GVNGCM gvn) { return null; }
  @Override public Type value(GVNGCM gvn) { return all_type(); }
  @Override public Type all_type() { return Type.ALL; }
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

  public void def( String name, byte mutable, boolean create ) {
    if( _ifs == null || _ifs._len==0 ) return; // Not inside an If
    _ifs.last().def(name,mutable,create);      // Var defined in arm of if
  }

  public Node check_if( boolean arm, Parse bad, GVNGCM gvn, Node ctrl, Node ptr, Node mem ) { return _ifs.last().check(arm,bad,gvn,ctrl,ptr,mem); }

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
    Node check(boolean arm, Parse bad, GVNGCM gvn, Node ctrl, Node ptr, Node mem) {
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
      mem.unhook();
      HashMap<String,Byte> vars = arm ? _fvars : _tvars;
      for( String name : vars.keySet() ) {
        String msg = bad.errMsg("'"+name+"' not defined on "+arm+" arm of trinary");
        Node err = gvn.xform(new ErrNode(ptr,msg,Type.SCALAR));
        mem = gvn.xform(new StoreNode(ctrl,mem,ptr,err,TypeStruct.ffinal(),name,bad));
      }
      return mem.keep();
    }
  }
}
