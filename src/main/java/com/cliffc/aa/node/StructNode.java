package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVErr;
import com.cliffc.aa.tvar.TVStruct;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.Util;

import java.util.Arrays;

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

  // Number of args in the enclosing function scope.  Inputs up to this count
  // are in the NONGEN set; inputs after this are out of the NONGEN set.  This
  // is zero for non-function scopes, and -1 for if-half-scopes
  public final int _nargs;

  // Still adding fields or not.  Helps with asserting in the Parser
  private boolean _closed;
  
  // True if forward-ref.  Again, helps with the Parser.
  // Only modify if !_closed
  private boolean _forward_ref;

  // A collection of fields which *almost* make up a TypeStruct.  Almost,
  // because missing the field Types, which come from the Node inputs are not
  // otherwise part of a StructNode.

  // Default type for unnamed fields.  Frequently 'ALL' except for primitive
  // classes which support direct lattice isa() tests vs XNIL.
  public final Type _def;
  
  // Field names mapped one-to-one with inputs.  Not sorted.
  // Order is IGNORED for H-M purposes.
  // Only modify if !_closed
  private final Ary<String> _flds;

  // R/W vs Read-only status of fields
  // Only modify if !_closed
  final Ary<TypeFld.Access> _accesses;
  
  // Parser helper for error reports on arg tuples, start of tuple/struct is in
  // _paren_start, and the args are in _fld_starts.
  // Example: "  ( x,y)\n"
  // Example:  012345678
  // _paren_start  ==2, offset to the opening paren
  // _fld_starts[0]==4, offset to start of zeroth arg
  // _fld_starts[1]==6, offset to start of oneth arg
  private final Parse _paren_start;
  private final Ary<Parse> _fld_starts;

  public StructNode(int nargs, boolean forward_ref, Parse paren_start, Type def) {
    super(OP_STRUCT);
    _nargs = nargs;
    _forward_ref = forward_ref;
    _def = def;
    _flds = new Ary<>(new String[1],0);
    _accesses = new Ary<>(new TypeFld.Access[1],0);
    _paren_start = paren_start;
    _fld_starts = new Ary<>(new Parse[1],0);
    _live = TypeStruct.ISUSED;
  }

  @Override String str() {
    SB sb = new SB().p("@{");
    for( int i=0; i<_flds._len; i++ ) {
      if( i==_nargs ) sb.p("| ");
      sb.p(_flds.at(i)).p("; ");
    }
    if( _flds._len>0 ) sb.unchar(2);
    return sb.p("}").toString();
  }

  // Structs with the same inputs and same field names are the same.
  @Override public int hashCode() {
    return super.hashCode() ^ _flds.hashCode() ^ _accesses.hashCode() ^ (int)_def._hash;
  }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    return super.equals(o) && o instanceof StructNode rec &&
      _closed==rec._closed &&
      _flds.equals(rec._flds) &&
      _accesses.equals(rec._accesses) &&
      _def==rec._def;
  }

  // String-to-node-index
  public int find(String name) { return _flds.find(name); }
  // String-to-Node
  public Node in(String name) { return in(find(name)); } // Error if not found
  // String-to-field access enum
  public TypeFld.Access access(String name) { return _accesses.at(find(name)); }

  public String fld(int idx) { return _flds.at(idx); }
  public TypeFld.Access access(int idx) { return _accesses.at(idx); }

  // One-time transition when closing a Struct to new fields.
  public boolean is_closed() { return _closed; }
  public StructNode close() {
    assert !_closed;
    assert _nargs <= _flds._len;
    unelock();                  // Changes hash
    _closed=true;
    Env.GVN.add_reduce(this);   // Rehash
    add_flow();
    return this;
  }

  public boolean is_nongen(String fld) { return _nargs!=0 && find(fld)<_nargs; }
  public boolean is_closure() { return _nargs>0; }
  
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
    add_flow();
    return this;
  }

  // Set a replacement field in a Struct.  Fails if trying to replace a final
  // field.
  public boolean set_fld(String id, TypeFld.Access access, Node val, boolean force ) {
    int idx = find(id);
    if( !force && _accesses.at(idx) == TypeFld.Access.Final ) return false;
    set_def(idx,val);
    _accesses.set(idx,access);
    return true;
  }

  // The current local scope ends, no more names will appear.  Forward refs
  // first found in this scope are assumed to be defined in some outer scope
  // and get promoted.  Other locals are no longer kept alive, but live or die
  // according to use.
  public void promote_forward( StructNode parent ) {
    assert parent != null;
    for( int i=0; i<_defs._len; i++ ) {
      if( in(i) instanceof ForwardRefNode fref && Util.eq(fref._name,fld(i))) {
        // Is this ForwardRef defined in this scope, or some outer scope?
        if( fref.is_scoped() ) {
          // Definitely defined here
          //    fref.define();
          throw unimpl();        // TODO: Access input by field name
        } else {
          // Make field in the parent
          if( !parent.is_prim() ) {
            parent.add_fld(fref._name,TypeFld.Access.RW,fref,_fld_starts.at(i)).xval();
            // Stomp field locally to load from parent
            FieldNode fld = new FieldNode(parent,fref._name,_fld_starts.at(i));
            fld._val = val(i);
            set_def(i,fld);
            Env.GVN.add_work_new(fld);
          }
        }
      }
    }
  }

  // Remove a non-prim field, preserving order.  For resetting primitives for
  // multi-testing
  @Override void walk_reset0( ) {
    Node c;
    if( _defs._len>0 )
      while( !(c=_defs.last()).is_prim() ) {
        _flds.pop();
        _accesses.pop();
        _fld_starts.pop();
        _defs.pop();
        c._uses.del(this);
      }
  }
  
  // Gather inputs into a TypeStruct.
  @Override public Type value() {
    assert _defs._len==_flds.len();
    TypeFld[] flds = TypeFlds.get(_flds.len());
    for( int i=0; i<_flds.len(); i++ )
      flds[i] = TypeFld.make(_flds.at(i),val(i),_accesses.at(i));
    // Fields are sorted in TypeStruct so I can merge-sort
    Arrays.sort(flds,( tf0, tf1) -> TypeFld.scmp(tf0._fld,tf1._fld));
    return TypeStruct.make_flds(_def,flds);
  }

  // Return liveness for a field
  @Override public Type live_use( int idx ) {
    if( !(_live instanceof TypeStruct ts) ) return _live;
    String fld = _flds.at(idx);       // Get field name
    // Use name lookup to get liveness for that field
    Type live = ts.at_def(fld).oob();
    // Stacked overloads in struct
    if( in(idx) instanceof StructNode ) return live.oob(TypeStruct.ISUSED);
    return live;
  }
  @Override boolean assert_live(Type live) { return live instanceof TypeStruct; }

  @Override public Node ideal_reduce() {
    if( is_prim() ) return null;
    // Kill dead fields
    if( _live instanceof TypeStruct live ) {
      deps_add(this);           // If self-live lifts, self reduce makes progress
      Node progress=null;
      for( int i=0; i<_flds._len; i++ ) 
        if( in(i)!=Env.ANY && live.at_def(_flds.at(i)).above_center() &&
            !Util.eq(_flds.at(i),TypeFld.CLZ) )  // Leave a dead CLZ for error messages
          progress = set_def(i,Env.ANY);
      if( progress!=null ) return this;
    }
    return null;
  }

  
  @Override public boolean has_tvar() { return true; }

  // Used to close the cycle between the ints and flts
  public void init_tvar() {
    _tvar = new TVStruct(_flds);
  }

  // Self is always @{flds...}
  @Override public TV3 _set_tvar() {
    if( _tvar==null ) init_tvar();
    TVStruct ts = (TVStruct)_tvar;
    // Unify all fields
    for( int i=0; i<len(); i++ )
      ts.arg(i).unify(in(i).set_tvar(),false); // Unify (possible cycle)
    return _tvar;
  }
  
  // Structs are pre-unified in set_tvar
  @Override public boolean unify( boolean test ) { return false; }

  @Override public ErrMsg err( boolean fast ) {
    if( _tvar==null ) return null;
    if( !(tvar() instanceof TVErr terr) ) return null;
    if( fast ) return ErrMsg.FAST;
    return ErrMsg.unresolved(terr._bad,tvar().p());
  }
}
