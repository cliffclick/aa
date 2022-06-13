package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;

import static com.cliffc.aa.AA.unimpl;
import static com.cliffc.aa.type.TypeFld.Access;

// Makes a TypeStruct without allocation

// A simple gather/builder node, with support for incremental field discovery
// for the Parser.  Does not have control or memory edges.  This is an identity:
//
//       Scalar <- Struct[name] <- Field[name] <- Scalar
//
// Value is a TypeStruct.  Liveness a per-field TypeStruct in TypeMem.at[1].
//
// Does NOT support field updates directly.

// Can be marked as a closure, which is mostly used for asserts.
// The Parser uses this flag to help with early-returns: "^".

// Can be marked as a forward-ref, which again is mostly used for asserts.
// The Parser also uses this for determining where HM FreshNodes go.

// Holds argument-starts for argument tuples, for eventual error reporting.

// Inputs are sorted in the same order as a canonicalizing TypeStruct (alpha
// within lexical scope; shadowing requires another scope; deBruin numbers).
public class StructNode extends Node {

  private TypeStruct _ts; // Field names and default types, alpha-sorted.

  // Used to distinguish closures from normal structs in the Parser (the "^"
  // syntax escapes all nested struct scopes to the enclosing closure).
  public final boolean _is_closure;

  // Still adding fields or not.  Helps with asserting in the Parser
  private boolean _closed;

  // True if forward-ref.  Again, helps with the Parser
  private boolean _forward_ref;

  // Parser helper for error reports on arg tuples, start of tuple/struct is in
  // slot 0, and the args are +1 from there.
  // Example: "  ( x,y)\n"
  // Example:  012345678
  // _fld_starts[0]==2, offset to the openning paren
  // _fld_starts[1]==4, offset to start of zeroth arg
  // _fld_starts[2]==7, offset to start of oneth arg
  private Ary<Parse> _fld_starts;

  public StructNode(boolean is_closure, boolean forward_ref, Parse bad_start) {
    super(OP_STRUCT);
    _is_closure = is_closure;
    _forward_ref = forward_ref;
    _ts = TypeStruct.ISUSED;
    _fld_starts = new Ary<>(new Parse[]{bad_start});
  }

  @Override String str() { return _ts.toString(); }

  // Structs with the same inputs and same field names are the same.
  @Override public int hashCode() {
    return super.hashCode()+ (int)_ts._hash;
  }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof StructNode rec) ) return false;
    return _ts==rec._ts;
  }
  private StructNode set_ts(TypeStruct ts) {
    if( _elock ) unelock();    // Unlock before changing hash
    _ts=ts;
    return this;
  }
  StructNode name(String name) {
    assert _ts._clz.length()==0;
    return set_ts(_ts.set_name(name));
  }
  public TypeStruct ts() { return _ts; }

  // String-to-node-index
  public int find(String name) { return _ts.find(name); }
  // String-to-Node
  public Node in(String name) { return in(find(name)); } // Error if not found
  // String to TypeFld
  public TypeFld get(String name) { return _ts.get(name); }

  // String to a BOUND node: if field name maps to a FunPtrNode or an
  // UnresolvedNode, return the bound version instead.  Otherwise
  // return the Node as-is, or null if the name misses.
  public Node in_bind( String fld, Node clz ) {
    int idx = find(fld);
    if( idx == -1 ) return null; // No name
    Node n = in(idx);
    if( n instanceof FunPtrNode fptr )
      return new FunPtrNode(fptr._name,fptr.ret(),clz).init();
    else if( n instanceof UnresolvedNode unr )
      return ((UnresolvedNode)unr.copy(true)).set_bad(null).set_def(0,clz);
    // No binding to address, e.g. loading a global constant
    return n;
  }


  // One-time transition when closing a Struct to new fields.
  public StructNode close() { assert !_closed; _closed=true; return this; }
  public boolean is_closed() { return _closed; }

  // One-time transition when defining a forward ref
  public void define() { assert _forward_ref && _closed; _forward_ref=false; }
  @Override public boolean is_forward_type() { return _forward_ref; }

  // Simple parser helpers
  public Parse[] fld_starts() { return _fld_starts.asAry(); }

  // Add a field
  public Node add_fld( TypeFld fld, Node val, Parse badt ) {
    assert !_closed;
    int len = len();
    // Change TypeStruct for fields
    set_ts(_ts.add_fldx(fld));
    int idx = _ts.find(fld._fld);   // Where inserted
    insert(idx,val);                // Same place in defs
    _fld_starts.insert(idx+1,badt); // Same place in field starts + 1
    return this;
  }

  // Add a named FunPtr to a Struct.  Auto-inflates to an Unresolved as needed.
  public void add_fun( String name, Access fin, FunPtrNode fptr, Parse bad ) {
    assert !_closed;
    int idx = find(name);       // Node index
    if( idx == -1 ) {
      TypeFld fld2 = TypeFld.make(name,fptr._val,fin);
      add_fld(fld2, fptr, bad);
      return;
    }
    Node n = in(idx);
    if( n._val==TypeNil.XNIL ) // Stomp over a nil field create
      //return set_fld(fld.make_from(fptr._val,fin),fptr);
      throw unimpl();
    // Inflate to unresolved as needed
    UnresolvedNode unr = n instanceof UnresolvedNode unr2
      ? unr2
      : new UnresolvedNode(name,bad).scoped().add_fun((FunPtrNode)n);
    unr.add_fun(fptr);          // Checks all formals are unambiguous
    set_ts(_ts.replace_fld(_ts.get(name).make_from(unr._val)));
    set_def(idx,unr);           // No change to def orders
    xval();
  }

  // For reseting primitives for multi-testing
  public void pop_fld() {
    pop();
    _fld_starts.pop();
    set_ts(_ts.pop_fld(len()));
  }

  // The current local scope ends, no more names will appear.  Forward refs
  // first found in this scope are assumed to be defined in some outer scope
  // and get promoted.  Other locals are no longer kept alive, but live or die
  // according to use.
  public void promote_forward( StructNode parent ) {
    assert parent != null;
    for( int i=0; i<_defs._len; i++ ) {
      Node n = in(i);
      if( n.is_forward_ref() ) {
        // Is this Unresolved defined in this scope, or some outer scope?
        if( ((UnresolvedNode)n).is_scoped() ) {
          // Definitely defined here, and all stores are complete; all fcns added
        //    ((UnresolvedNode)n).define();
        //    Env.GVN.add_unuse(n);
          throw com.cliffc.aa.AA.unimpl();        // TODO: Access input by field name
        } else {
          // Make field in the parent
          TypeFld fld = _ts.get(i);
          parent.add_fld(fld, n, _fld_starts.at(i+1));
          // Stomp field locally to ANY
          set_def(i,Env.ANY);
          set_ts(_ts.replace_fld(TypeFld.make(fld._fld, Type.ANY, TypeFld.Access.Final)));
          Env.GVN.add_flow_uses(this);
        }
      }
    }
  }

  // Gather inputs into a TypeStruct.
  @Override public Type value() {
    assert _defs._len==_ts.len();
    TypeFld[] flds = TypeFlds.get(_ts.len());
    for( int i=0; i<flds.length; i++ )
      flds[i] =_ts.get(i).make_from(in(i)._val);
    return _ts.make_from(flds);
  }

  // Return liveness for a field
  @Override public Type live_use( Node def ) {
    if( !(_live instanceof TypeStruct ts) ) return _live.oob();
    int idx = _defs.find(def);        // Get Node index
    TypeFld lfld = ts.get(idx);       // Liveness for this index
    return lfld==null ? ts.oob() : lfld._t.oob();
  }

  @Override public boolean has_tvar() { return true; }

  @Override public boolean unify( boolean test ) {
    // Force result to be a struct with at least these fields.
    // Do not allocate a TV2 unless we need to pick up fields.
    boolean progress = false;
    TV2 rec = tvar();
    if( rec.is_leaf() ) {
      if( test ) return true;
      progress = _tvar.unify(rec=TV2.make_struct(this,"init_struct"),test);
    }
    assert check_fields(rec);
    rec.push_dep(this);

    // Unify existing fields.  Ignore extras on either side.
    for( int i=0; i<_ts.len(); i++ ) {
      TV2 fld = rec.arg(_ts.get(i)._fld);
      if( fld!=null ) progress |= fld.unify(tvar(i),test);
      if( test && progress ) return true;
    }

    return progress;
  }
  // Extra fields are unified with ERR since they are not created here:
  // error to load from a non-existing field
  private boolean check_fields(TV2 rec) {
    if( rec._args != null )
      for( String id : rec._args.keySet() )
        if( _ts.find(id)==-1 && !rec.arg(id).is_err() )
          return false;
    return true;
  }
}
