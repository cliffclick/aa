package com.cliffc.aa.node;

import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

import java.util.HashMap;
import java.util.Set;

import static com.cliffc.aa.AA.*;
import static com.cliffc.aa.type.TypeFld.Access;

// Lexical-Scope Node.  Tracks control & phat memory, plus a stack frame (which
// is just a NewNode).  The stack frame maps local variable names to Nodes and
// is modeled as a true memory indirection - for true closures.  Unless there
// is an upwards funarg the stack frame will optimize away.
public class ScopeNode extends Node {

  // Mapping from type-variables to Types.  Types have a scope lifetime like values.
  public final HashMap<String,TypeNil> _types; // user-typing type names

  public ScopeNode( HashMap<String,TypeNil> types,  Node ctl, Node mem, Node rez, Node ptr, StructNode dsp) {
    super(ctl,mem,rez,ptr,dsp);
    _types = types;
    _live = RootNode.defMem(this);
  }
  @Override public String label() {
    if( Parse.PARSE != null && Parse.PARSE.scope()==this )
      return "CURSCOP";
    return "Scope";
  }
  @Override public boolean isCFG() { return true; }
  @Override public boolean isMem() { return true; }

  public       Node ctrl() { return in(CTL_IDX); }
  public       Node mem () { return in(MEM_IDX); }
  public       Node rez () { return in(REZ_IDX); }
  public    NewNode ptr () { return (   NewNode)in(ARG_IDX  ); }
  public StructNode stk () { return (StructNode)in(ARG_IDX+1); }
  public <N extends Node> N ctrl( N n) { setDef(CTL_IDX,n); return n; }
  public void set_rez ( Node n) { setDef(REZ_IDX,n); }
  public void set_ptr ( Node n) { setDef(ARG_IDX,n); }

  public void mem(Node st) {
    // Remove the scope use of old memory, so the store becomes the ONLY use of
    // old memory, allowing the store to fold immediately.
    //setDef(MEM_IDX,null);
    setDef(MEM_IDX,st);
  }

  public Node get(String name) { return stk().in(name); }
  public boolean is_mutable(String name) { return stk().access(name)==Access.RW; }

  public static final int RET_IDX = ARG_IDX+5;
  public boolean has_early_exit() { return len()==RET_IDX; }
  public RegionNode early_ctrl() { return (RegionNode)in(ARG_IDX+2); }
  public    PhiNode early_mem () { return (   PhiNode)in(ARG_IDX+3); }
  public    PhiNode early_val () { return (   PhiNode)in(ARG_IDX+4); }
  public void       early_kill() { setDef(ARG_IDX+2,null); setDef(ARG_IDX+3,null); setDef(ARG_IDX+4,null); }
  public void make_early_exit_merge() {
    setDef(ARG_IDX+2, new RegionNode((Node)null))._val = Type.CTRL;
    setDef(ARG_IDX+3, new PhiNode(TypeMem.ALLMEM, null,(Node)null));
    setDef(ARG_IDX+4, new PhiNode(TypeNil.SCALAR, null,(Node)null));
  }

  // Name to type lookup, or null
  public TypeNil get_type(String name) { return _types.get(name);  }

  // Extend the current Scope with a new type; cannot override existing name.
  public void add_type( String name, TypeNil t ) {
    assert _types.get(name)==null;
    _types.put( name, t );
  }

  public Set<String> typeNames() { return _types.keySet(); }

  // Produce a tuple of the return result and a summary of all escaping
  // functions, on behalf of the following CEProjs.
  @Override public Type value() { return Type.CTRL; }

  @Override public TypeMem live() {
    //assert is_keep() || Combo.pre() || is_prim();
    return RootNode.removeKills(this);
  }

  @Override public Type live_use( int i ) {
    // Basic liveness ("You are Alive!") for control and returned value
    if( i == CTL_IDX ) return Type.ALL;
    if( i == MEM_IDX ) return _live;
    if( i == REZ_IDX ) return Type.ALL; // Returning a Scalar, including e.g. a mem ptr
    if( i == ARG_IDX ) return Type.ALL; // Display must be kept-alive during e.g. parsing.
    if( i == ARG_IDX+1 ) return TypeStruct.ISUSED;
    //// Any function which may yet have unwired CallEpis, and so needs full
    //// memory alive until all Calls are wired.
    //if( in(i) instanceof RetNode ) return _live;
    //// Merging exit path, or ConType
    //return def._live;
    throw TODO();             // TODO Test me
  }

  @Override int hash() { return 123456789; }
  // ScopeNodes are never equal
  @Override public boolean equals(Object o) { return this==o; }
  // End of dominator tree; do not walk past
  //@Override Node walk_dom_last(Predicate<Node> P) { return P.test(this) ? this : null; }

  @Override public boolean has_tvar() { return false; }

  // Test for being inside a ?: expression
  public boolean test_if() { return stk()._nargs==-1; }
}
