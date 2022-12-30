package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;

import static com.cliffc.aa.AA.unimpl;

// Takes a static field name, a TypeStruct and returns the field value.
// Basically a ProjNode except it does lookups by field name in TypeStruct
// instead of by index in TypeTuple.

// Lookups that miss the field name will try again in a prototype.  A 2nd
// lookup for field "!" (the prototype field) will be tried.  If this works and
// produces a pointer with a single PROTOS alias, the field will be looked up
// in the prototype and if found, the result will be bound to the original.
//
// Example: a lookup of "_+_" in the wrapped struct for 1, "@{!=int:clazz,.=1}".
// The field "_+_" is not found in the wrapped 1; so the lookup goes again on
// the int clazz.  This hits, and returns an overload of integer-add functions:
// "( { int   int -> int}; { int   flt -> flt})".  This value is then bound:
// "( { int:1 int -> int}; { int:1 flt -> flt})".

public class FieldNode extends Node implements Resolvable {
  
  // Field being loaded from a TypeStruct.  If null, the field name is inferred
  // from amongst the field choices.  If not-null and not present, then an error.
  public       String _fld;
  public final Parse _bad;

  public FieldNode(Node struct, String fld, Parse bad) {
    super(OP_FIELD,struct);
    _fld = fld==null ? ("&"+_uid).intern() : fld;
    _bad = bad;
  }

  @Override public String xstr() { return "."+(is_resolving() ? "_" : _fld); }   // Self short name
  String  str() { return xstr(); } // Inline short name
  @Override public boolean is_resolving() { return Resolvable.is_resolving(_fld); }
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
    
    int alias;
    if( t==TypeNil.XNIL ) {
      // TODO: proper semantics?  For now, mimic int
      alias = PrimNode.NINT._alias;
    } else {
      // Input is not a struct, so error return
      if( !(t instanceof TypeStruct ts) )
        return t.oob();
      // Normal field lookup
      TypeFld fld = ts.get(_fld);
      // Hit with field name
      if( fld!=null ) return fld._t;

      // Prototype lookup
      TypeFld proto = ts.get("!");
      if( !(proto._t instanceof TypeMemPtr tptr) ||
          (alias = tptr.aliases().abit()) < 0 ) {
        // No prototype field found.
        // If ts is low  and lifting, one might yet appear.
        // If ts is high and falling, one might yet appear.
        return proto._t.oob();
      }

    }

    // Try the prototype lookup
    NewNode nnn = Env.PROTOS.get(alias);
    StructNode proto = (StructNode)nnn.rec();
    if( !(proto._val instanceof TypeStruct ts) )
      return proto._val.oob();

    // Proto field lookup
    TypeFld fld = ts.get(_fld);
    // Hit with field name in prototype
    if( fld!=null ) {
      // Add an edge, so prototype updates trigger updates here
      if( len()==1 ) add_def(proto);
      else assert in(1)==proto;
      // Bind the result.
      return BindFPNode.bind(fld._t,t);
    }
    
    // True missing field
    throw unimpl();
  }

  private static Type meet(TypeStruct ts) { Type t = TypeNil.XSCALAR; for( TypeFld t2 : ts )  t = t.meet(t2._t); return t; }
  private static Type join(TypeStruct ts) {
    Type t = TypeNil.SCALAR;
    for( TypeFld t2 : ts )
      t = t.join( t2._t instanceof TypeFunPtr tfp2  ? tfp2.make_from(tfp2.fidxs().dual()) : t2._t );
    return t;
  }

  // Checks is_err from HMT from StructNode.
  // Gets the T2 from the base StructNode.
  // Gets the StructNode from the aliases - needs the actual struct layout
  private Type missing_field() {
    throw unimpl();
  }

  @Override public Node ideal_reduce() {
    if( is_resolving() ) return null;
    
    // Back-to-back SetField/Field
    if( in(0) instanceof SetFieldNode sfn && sfn.err(true)==null )
      return Util.eq(_fld, sfn._fld)
        ? sfn.in(1)             // Same field, use same
        : set_def(0, sfn.in(0)); // Unrelated field, bypass

    // Hitting in the prototype requires rewiring.  Wire directly to the
    // prototype, remove the prototype edge, and insert a BindFP.
    if( len()>1 ) {
      // Wire directly to the prototype (not doing a prototype-style lookup on
      // the prototype, just a normal lookup).  Remove the prootype edge.
      Node fld = new FieldNode(in(1),_fld,_bad).init();
      return new BindFPNode(fld,in(0)).init();
    }
    
    // Skip past a BindFP
    if( in(0) instanceof BindFPNode bind ) {
      FieldNode fld2 = new FieldNode(bind.fp(),_fld,_bad).init();
      return new BindFPNode(fld2,bind.dsp()).init();
    }

    return null;
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
          lphi.add_def(Env.GVN.add_work_new(new FieldNode(phi.in(i),_fld,_bad)));
        subsume(lphi);
        return lphi;
      }
    }

    return null;
  }

  @Override public boolean has_tvar() { return true; }

  @Override public boolean unify( boolean test ) {
    boolean progress = false;
    TV3 rec = tvar(0);
    assert !(rec instanceof TVPtr); // No ptrs here, just structs

    // Add struct-ness if needed
    TVStruct str;
    if( !(rec instanceof TVStruct str0) ) {
      if( test ) return true;
      progress = rec.unify(str=new TVStruct(new String[0],new TV3[0],true),test);
    } else {
      str = str0;
    }

    // Attempt resolve
    if( is_resolving() ) {
      if( str.is_open() ) str.deps_add_deep(this);
      else {
        progress = trial_resolve(tvar(), str, str, test);
        if( test ) { if( progress ) return true; }
        // Revisit if parts change to allow unification
        else tvar().deps_add_deep(str.deps_add_deep(this));
      }
    }

    // Look up field
    TV3 fld = str.arg(_fld);
    TV3 self = tvar();
    if( fld!=null )           // Unify against a pre-existing field
      return fld.unify(self, test) | progress;

    // Try again in a prototype
    TV3 proto = str.arg("!");
    if( proto instanceof TVPtr pptr ) {
      fld = pptr.load().arg(_fld);
      if( fld!=null )           // Unify against a pre-existing field
        return fld.unify(self, test) | progress;
    }

    // If field is doing overload resolution, inject even if rec is closed
    if( is_resolving() ) {
      if( test ) return true;
      str.add_fld(_fld,self);
      return true;
    }

    // If the field is not there and the struct is closed, then the field is
    // missing.
    if( !str.is_open() ) {
      // Might yet get a prototype and find field
      if( proto instanceof TVLeaf ) {
        proto.deps_add_deep(this);
        return false;
      }
      throw unimpl();
    }

    // Add the field
    if( test ) return true;
    str.add_fld(_fld,self);
    return true;
  }

  @Override public int hashCode() { return super.hashCode()+_fld.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof FieldNode fld) ) return false;
    return Util.eq(_fld,fld._fld);
  }

}
