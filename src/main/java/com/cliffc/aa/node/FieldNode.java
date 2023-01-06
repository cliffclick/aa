package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;

import static com.cliffc.aa.AA.unimpl;

// Takes a static field name, a TypeStruct and returns the field value.
// Basically a ProjNode except it does lookups by field name in TypeStruct
// instead of by index in TypeTuple.
//
// Fields with a fixed name either lookup in the incoming self record or in the
// prototype.  The Field is unresolved until the lookup is successful in one or
// the other; error if found in both.  Once resolved, the Field is marked.
//
// Fields with the "_" name resolve locally only via H-M matching to one choice
// field.  Once resolved the Field name changes to match.

public class FieldNode extends Node implements Resolvable {
  
  // Field being loaded from a TypeStruct.  If "_", the field name is inferred
  // from amongst the field choices.  If not-"_" and not present, then the
  // lookup tries again in the prototype, and if that fields, then error.
  public       String _fld;
  public final Parse _bad;
  
  public static final byte UNKNOWN=0; // Unknown if the field loads from self or prototype
  public static final byte LOCAL  =1; // Loads from self, not prototype
  public static final byte PROTO  =2; // Loads from prototype, but the prototype is not known yet
  // Fields from known prototype are rewritten in Iter to local-on-prototype fields.
  // Fields can find their prototype in Combo and not rewritten until after Combo.
  private byte _mode;

  public FieldNode(Node struct, byte mode, String fld, Parse bad) {
    super(OP_FIELD,struct);
    _mode = mode;               // Local or prototype
    // A plain "_" field is a resolving field
    _fld = Util.eq(fld,"_") ? ("&"+_uid).intern() : fld;
    _bad = bad;
  }

  @Override public String xstr() { return "."+(is_resolving() ? "_" : _fld); }   // Self short name
  String  str() { return xstr(); } // Inline short name
  @Override public boolean is_resolving() { return Resolvable.is_resolving(_fld); }
  @Override public String fld() { assert !is_resolving(); return _fld; }
  @Override public String resolve(String label) {
    unelock();                  // Hash changes since label changes
    String old = _fld;
    _fld = label;
    add_flow();
    return old;
  }
  @Override public TV3 match_tvar() { return tvar(0); }
  
  @Override public Type value() {
    Type t = val(0);
    if( is_resolving() ) {
      // Pre-HMT, dunno which one, use meet.
      // Still resolving, use the join of all fields.
      boolean lo = _tvar==null || Combo.HM_AMBI;
      if( t instanceof TypeStruct ts )
        return lo ? meet(ts) : join(ts);
      return TypeNil.SCALAR.oob(!lo);
    }

    TypeFld fld;
    Node n = resolve_local_clz(); // self or clz or null
    if( n==null ) return t.oob(); // No resolve yet
    if( !((n==this ? t : n._val) instanceof TypeStruct ts) ||
        (fld = ts.get(_fld))==null ) {
      if( _mode==UNKNOWN ) throw unimpl(); // True missing
      else return t.oob();
    }
    return fld._t;
  }

  private static Type meet(TypeStruct ts) { Type t = TypeNil.XSCALAR; for( TypeFld t2 : ts )  t = t.meet(t2._t); return t; }
  private static Type join(TypeStruct ts) {
    Type t = TypeNil.SCALAR;
    for( TypeFld t2 : ts )
      t = t.join( t2._t instanceof TypeFunPtr tfp2  ? tfp2.make_from(tfp2.fidxs().dual()) : t2._t );
    return t.meet(TypeNil.XSCALAR);
  }

  // Checks is_err from HMT from StructNode.
  // Gets the T2 from the base StructNode.
  // Gets the StructNode from the aliases - needs the actual struct layout
  private Type missing_field() {
    throw unimpl();
  }

  @Override public Node ideal_reduce() {
    if( is_resolving() ) return null;

    if( _mode==UNKNOWN || _mode==PROTO ) {
      Node n = resolve_local_clz();
      if( n!=null ) {
        if( n==this ) { _mode=LOCAL; return this; }
        set_def(0,n);
        _mode=LOCAL;
      }
    }
    
    // Back-to-back SetField/Field
    if( in(0) instanceof SetFieldNode sfn && sfn.err(true)==null )
      return Util.eq(_fld, sfn._fld)
        ? sfn.in(1)             // Same field, use same
        : set_def(0, sfn.in(0)); // Unrelated field, bypass

    // Back-to-back Struct/Field
    if( in(0) instanceof StructNode str && str.err(true)==null ) {
      int idx = str.find(_fld);
      if( idx >= 0 ) return str.in(idx);
    }
    
    // Skip past a BindFP (or delay the bind)
    if( in(0) instanceof BindFPNode bind ) {
      FieldNode fld2 = new FieldNode(bind.fp(),_mode,_fld,_bad).init();
      return new BindFPNode(fld2,bind.dsp()).init();
    }

    return null;
  }

  // If LOCAL, return self.
  // If PROTO, return clz.
  // If UNKNOWN, return either self, clz or null.
  Node resolve_local_clz() {
    if( _mode==LOCAL ) return this;
    if( _mode==PROTO && len()>1 ) return in(1);
    String clz;
    Type t = val(0);
    // TODO: proper semantics?  For now, mimic int
    if( t==TypeNil.XNIL ) clz = "int:"; // Nil class
    else if( t instanceof TypeInt ) clz="int:";
    else if( t instanceof TypeFlt ) clz="flt:";
    else if( t instanceof TypeStruct ts ) {
      // Normal field lookup
      TypeFld fld = ts.get(_fld);
      // Hit with field name
      if( fld!=null ) return this; 
      // Prototype lookup
      clz = ts._clz;
    } else return null;         // No resolve yet
    
    // Try the prototype lookup
    StructNode proto = Env.PROTOS.get(clz);
    if( proto==null || !(proto._val instanceof TypeStruct ts) )
      return null;              // No resolve yet

    // Proto field lookup
    TypeFld fld = ts.get(_fld);
    // Hit with field name in prototype
    return fld==null ? null : proto;
  }

    
  @Override public Node ideal_grow() {
    // Load from a memory Phi; split through in an effort to sharpen the memory.
    // TODO: Only split thru function args if no unknown_callers, and must make a Parm not a Phi
    // TODO: Hoist out of loops.
    if( in(0) instanceof PhiNode phi ) {
      int fcnt=0;
      for( int i=1; i<phi.len(); i++ )
        if( phi.in(i)._op == OP_SETFLD ) fcnt++;
      if( fcnt>0 ) {
        Node lphi = new PhiNode(TypeNil.SCALAR,phi._badgc,phi.in(0));
        for( int i=1; i<phi.len(); i++ )
          lphi.add_def(Env.GVN.add_work_new(new FieldNode(phi.in(i),FieldNode.LOCAL,_fld,_bad)));
        subsume(lphi);
        return lphi;
      }
    }

    return null;
  }

  @Override public boolean has_tvar() { return true; }

  @Override public boolean unify( boolean test ) {
    boolean progress = false;
    TVStruct str = null;
    TV3 proto = null;
    switch( tvar(0) ) {
    // Stall if leaf, since might become either a struct, or something with
    // prototype struct
    case TVLeaf leaf -> {
      if( !test ) leaf.deps_add_deep(this); // If this changes, we might not be direct user
      return false;
    }
    case TVNil nil -> { proto = Env.PROTOS.get("int:").tvar(); }
    case TVBase base -> {
      if( base._t == TypeNil.XNIL )         proto = Env.PROTOS.get("int:").tvar();
      else if( base._t instanceof TypeInt ) proto = Env.PROTOS.get("int:").tvar();
      else if( base._t instanceof TypeFlt ) proto = Env.PROTOS.get("flt:").tvar();
      else throw unimpl();
    }
    case TVStruct str0 -> {
      str = str0;

      // If resolving, cannot do a field lookup.  Attempt resolve first.
      if( is_resolving() ) {
        progress = try_resolve(str,test);
        if( !progress || test ) return progress;
      }
      
      // Look up field normally (not in prototype)
      TV3 fld = str.arg(_fld);
      if( fld!=null )           // Unify against a pre-existing field
        return fld.unify(tvar(), test) | progress;
      
      // Try again in a prototype
      proto = str.arg("!");
      if( proto==null )
        throw unimpl();         // Might pick up proto field on open structs
    }
    default -> throw unimpl();
    }
    assert !is_resolving();

    // Proto might become a struct; stall
    if( proto instanceof TVLeaf ) throw unimpl();
    TV3 fld = ((TVStruct)proto).arg(_fld);
    if( fld!=null )           // Unify against a pre-existing field
      return fld.unify(tvar(), test) | progress;

    // If the field is resolved, and not in struct and not in proto and the
    // struct is closed, then the field is missing.
    if( str==null || !str.is_open() ) {
      throw unimpl();           // Missing field
    }

    // Add the field, make progress
    if( !test ) str.add_fld(_fld,tvar());
    return true;
  }

  private boolean try_resolve( TVStruct str, boolean test ) {
    // If struct is open, more fields might appear and cannot do a resolve.
    TV3 self = tvar();
    if( !str.is_open() ) {
      if( trial_resolve(self, str, str, test) ) return true;
      // No progress, try again if self changes
      if( !test ) self.deps_add_deep(this);
    }
    // Progress if field is missing
    if( test ) return str.arg(_fld)==null;
    str.deps_add_deep(this);    // Try again if str closes
    // Add unresolved field if not already there (even if closed)
    return str.arg(_fld)==null && str.add_fld(_fld,self); 
  }

  @Override public int hashCode() { return super.hashCode()+_fld.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof FieldNode fld) ) return false;
    return Util.eq(_fld,fld._fld);
  }

}
