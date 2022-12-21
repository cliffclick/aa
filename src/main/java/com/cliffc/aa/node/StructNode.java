package com.cliffc.aa.node;

import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVStruct;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFld;
import com.cliffc.aa.type.TypeFlds;
import com.cliffc.aa.type.TypeStruct;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.Util;

import static com.cliffc.aa.AA.unimpl;

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

  // Used to distinguish closures from normal structs in the Parser (the "^"
  // syntax escapes all nested struct scopes to the enclosing closure).
  public final boolean _is_closure;

  // Still adding fields or not.  Helps with asserting in the Parser
  private boolean _closed;
  
  // True if forward-ref.  Again, helps with the Parser.
  // Only modify if !_closed
  private boolean _forward_ref;

  // A collection of fields which *almost* make up a TypeStruct.  Almost,
  // because missing the field Types, which come from the Node inputs are not
  // otherwise part of a StructNode.
  
  // String clazz.  Never null.  Empty string "" is the empty clazz.
  public final String _clz;

  // Default type for unnamed fields.  Frequently 'ALL' except for primitive
  // classes which support direct lattice isa() tests vs XNIL.
  public final Type _def;
  
  // Field names mapped one-to-one with inputs.  Not sorted.
  // Order is IGNORED for H-M purposes.
  // Only modify if !_closed
  private final  Ary<String> _flds;

  // R/W vs Read-only status of fields
  // Only modify if !_closed
  final Ary<TypeFld.Access> _accesses;
  
  // Parser helper for error reports on arg tuples, start of tuple/struct is in
  // _paren_start, and the args are in _fld_starts.
  // Example: "  ( x,y)\n"
  // Example:  012345678
  // _paren_start  ==2, offset to the openning paren
  // _fld_starts[0]==4, offset to start of zeroth arg
  // _fld_starts[1]==6, offset to start of oneth arg
  private final Parse _paren_start;
  private final Ary<Parse> _fld_starts;

  public StructNode(boolean is_closure, boolean forward_ref, Parse paren_start, String clz, Type def) {
    super(OP_STRUCT);
    _is_closure = is_closure;
    _forward_ref = forward_ref;
    _clz = clz;
    _def = def;
    _flds = new Ary<>(new String[1],0);
    _accesses = new Ary<>(new TypeFld.Access[1],0);
    _paren_start = paren_start;
    _fld_starts = new Ary<>(new Parse[1],0);
  }

  @Override String str() {
    SB sb = new SB().p(_clz).p("@{");
    if( _flds.isEmpty() ) return sb.p("}").toString();
    for( String fld : _flds ) sb.p(fld).p(";");
    return sb.unchar().p("}").toString();
  }

  // Structs with the same inputs and same field names are the same.
  @Override public int hashCode() {
    return super.hashCode() ^ _flds.hashCode() ^ _accesses.hashCode() ^ (int)_def._hash ^ _clz.hashCode();
  }
  @Override public boolean equals(Object o) {
    assert _closed;             // V-N only for closed structs
    if( this==o ) return true;
    return super.equals(o) && o instanceof StructNode rec &&
      _flds.equals(rec._flds) && _accesses.equals(rec._accesses) &&
      _def==rec._def && Util.eq(_clz,rec._clz);
  }
  //private StructNode set_ts(TypeStruct ts) {
  //  if( _elock ) unelock();    // Unlock before changing hash
  //  _ts=ts;
  //  return this;
  //}
  //StructNode name(String name) {
  //  assert _ts._clz.length()==0;
  //  return set_ts(_ts.set_name(name));
  //}
  //public TypeStruct ts() { return _ts; }

  // String-to-node-index
  public int find(String name) { return _flds.find(name); }
  // String-to-Node
  public Node in(String name) { return in(find(name)); } // Error if not found
  //
  public TypeFld.Access access(String name) { return _accesses.at(find(name)); }

  public String fld(int idx) { return _flds.at(idx); }

  // One-time transition when closing a Struct to new fields.
  public StructNode close() { assert !_closed; _closed=true; return this; }
  public boolean is_closed() { return _closed; }

  // One-time transition when defining a forward ref
  public void define() { assert _forward_ref && _closed; _forward_ref=false; }
  @Override public boolean is_forward_type() { return _forward_ref; }

  // Simple parser helpers
  public Parse[] fld_starts() { return _fld_starts.asAry(); }

  // Add a field
  public Node add_fld( String fld, TypeFld.Access access, Node val, Parse badt ) {
    assert !_closed;
    add_def(val);               // Node in node array
    _flds.push(fld);            // Field name
    _accesses.push(access);     // Access rights to field
    _fld_starts.push(badt);     // Parser offset for errors
    return this;
  }

  // Remove a field, preserving order.  For reseting primitives for multi-testing
  public void remove_fld(int idx) {
    //set_ts(_ts.remove_fld(idx));
    //remove(idx);
    //_fld_starts.remove(idx+1);
    throw unimpl();
  }

  //// Set a replacement field in a Struct.  Fails if trying to replace a final
  //// field.
  //public boolean set_fld(String id, Access access, Node val, boolean force ) {
  //  int idx = find(id);
  //  TypeFld fld = _ts.get(idx);
  //  if( !force && fld._access == Access.Final ) return false;
  //  TypeStruct ts = _ts.replace_fld(fld.make_from(fld._t,access));
  //  set_ts(ts);
  //  set_def(idx,val);
  //  return true;
  //}

  // The current local scope ends, no more names will appear.  Forward refs
  // first found in this scope are assumed to be defined in some outer scope
  // and get promoted.  Other locals are no longer kept alive, but live or die
  // according to use.
  public void promote_forward( StructNode parent ) {
    //assert parent != null;
    //for( int i=0; i<_defs._len; i++ ) {
    //  Node n = in(i);
    //  if( n.is_forward_ref() ) {
    //    // Is this Unresolved defined in this scope, or some outer scope?
    //    if( ((UnresolvedNode)n).is_scoped() ) {
    //      // Definitely defined here, and all stores are complete; all fcns added
    //    //    ((UnresolvedNode)n).define();
    //    //    Env.GVN.add_unuse(n);
    //      throw com.cliffc.aa.AA.unimpl();        // TODO: Access input by field name
    //    } else {
    //      // Make field in the parent
    //      TypeFld fld = _ts.get(i);
    //      parent.add_fld(fld, n, _fld_starts.at(i+1));
    //      // Stomp field locally to ANY
    //      set_def(i,Env.ANY);
    //      set_ts(_ts.replace_fld(TypeFld.make(fld._fld, Type.ANY, TypeFld.Access.Final)));
    //      Env.GVN.add_flow_uses(this);
    //    }
    //  }
    //}
  }

  // Gather inputs into a TypeStruct.
  @Override public Type value() {
    assert _defs._len==_flds.len();
    TypeFld[] flds = TypeFlds.get(_flds.len());
    for( int i=0; i<flds.length; i++ )
      flds[i] = TypeFld.make(_flds.at(i),in(i)._val,_accesses.at(i));
    return TypeStruct.make_flds(_clz,_def,flds);
  }

  // Return liveness for a field
  @Override public Type live_use( Node def ) {
    if( !(_live instanceof TypeStruct ts) )
      { assert _live==Type.ANY || _live==Type.ALL; return _live; }
    int idx = _defs.find(def);        // Get Node index
    String fld = _flds.at(idx);       // Get field name
    // Use name lookup to get liveness for that field
    TypeFld lfld = ts.get(fld);       // Liveness for this field name
    return lfld==null ? ts.oob() : lfld._t.oob();
  }

  @Override public boolean has_tvar() { return true; }

  @Override TV3 _set_tvar() {
    TVStruct ts = new TVStruct(_flds);
    for( int i=0; i<len(); i++ )
      ts.set_fld(i,in(i).set_tvar()); 
    return ts;
  }
  

  @Override public boolean unify( boolean test ) {
    TVStruct rec = (TVStruct)tvar();

    // Unify existing fields.  Ignore extras on either side.
    boolean progress = false;
    for( int i=0; i<len(); i++ ) {
      TV3 fld = rec.arg(_flds.at(i)); // Field lookup by string
      if( fld!=null ) progress |= fld.unify(tvar(i),test);
      if( test && progress ) return true;
    }
    
    return progress;
  }
  //// Extra fields are unified with ERR since they are not created here:
  //// error to load from a non-existing field
  //private boolean check_fields(TV3 rec) {
  //  //if( rec._args != null )
  //  //  for( String id : rec._args.keySet() )
  //  //    if( !Util.eq(id," def") && _ts.find(id)==-1 && !rec.arg(id).is_err() )
  //  //      return false;
  //  //return true;
  //  throw unimpl();
  //}
}
