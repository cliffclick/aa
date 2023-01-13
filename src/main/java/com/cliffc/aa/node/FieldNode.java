package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
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

  public FieldNode(Node struct, String fld, Parse bad) {
    super(OP_FIELD,struct);
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
      if( t==Type.ALL ) return Type.ALL;
      return Type.ALL.oob(!lo);
    }

    // Hit on a field
    if( t instanceof TypeStruct ts && ts.find(_fld)!= -1 )
      return ts.at(_fld);    

    Node proto = clzz(t);
    if( proto!=null && proto._val instanceof TypeStruct clz ) {
      TypeFld fld = clz.get(_fld);
      if( fld !=null ) return fld._t; // Find in CLZ
    }
    return (proto==null ? t : proto._val).oob();
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

    // Back-to-back clz:Struct/Field.  Only for primitives; other clazz
    // references lazily discovered after Combo.
    StructNode proto = clzz(val(0));
    if( proto!=null )
      return proto.in(_fld);
    
    // Sink BindFP, lift Field
    if( in(0) instanceof BindFPNode bind ) {
      Node fld = new FieldNode(bind.fp(),_fld,_bad).init();
      return new BindFPNode(fld,bind.dsp()).init();
    }
    
    return null;
  }

  private static StructNode clzz(Type t) {
    return switch( t ) {
    case TypeInt ti -> PrimNode.ZINT;
    case TypeFlt tf -> PrimNode.ZFLT;
    case TypeStruct ts -> Env.PROTOS.get(ts._clz);  // CLZ from instance
    // TODO: XNIL uses the INT clazz.
    // Other, like SCALAR, does not have a known CLZ
    case TypeNil xnil -> xnil.isa(TypeNil.XNIL) ? PrimNode.ZINT : null;
    default -> null;
    };
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
    TVStruct str;
    switch( tvar(0) ) {
    case TVLeaf leaf -> {
      // Leaf is forced to be a struct with this field.  If the field is an
      // oper, the field is further forced to be an overload.  However, I have
      // no way to force a Lambda with the 'this' and unknown args.
      if (test) return true;
      leaf.unify(new TVStruct(true, new String[]{_fld}, new TV3[]{tvar()}, true), test);
      //if( Oper.is_oper(_fld) )
      //  throw unimpl();
      return true;
    }
    case TVNil nil -> {
      throw unimpl();
    }
    case TVBase base -> 
      str = tv_clz(base._t);
    
    case TVStruct str0 -> {
      // If resolving, cannot do a field lookup.  Attempt resolve first.
      if( is_resolving() ) {
        progress = try_resolve(str0,test);
        if( is_resolving() || test ) return progress;
      }
      str = str0;
    }
    default -> throw unimpl();
    };
    assert !is_resolving();

    // Look up field normally
    TV3 fld = str.arg(_fld);
    if( fld!=null )           // Unify against a pre-existing field
      return fld.unify(tvar(), test) | progress;

    // If the field is resolved, and not in struct and not in proto and the
    // struct is closed, then the field is missing.
    if( !str.is_open() ) {
      throw unimpl();           // Missing field
    }

    // Add the field, make progress
    if( !test ) str.add_fld(_fld,tvar());
    //return true;
    throw unimpl();
  }

  public static TVStruct tv_clz(Type t) {
    String clz = switch( t ) {
    case TypeInt ti -> "int:";
    case TypeFlt tf -> "flt:";
    case TypeNil tn -> tn==TypeNil.XNIL ? "int:" : null;
    default -> null;
    };
    return (TVStruct)Env.PROTOS.get(clz).tvar();
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

  @Override public ErrMsg err( boolean fast ) {
    Ary<String> errs = tvar()._errs;
    if( errs==null ) return null;
    if( fast ) return ErrMsg.FAST;
    if( errs.len()>1 ) throw unimpl();
    if( tvar(0) instanceof TVLeaf )
      return ErrMsg.unresolved(_bad,"Not a struct loading field "+_fld);
    return tvar(0).as_struct().err_resolve(_bad, errs.at(0));
  }

  @Override public int hashCode() { return super.hashCode()+_fld.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof FieldNode fld) ) return false;
    return Util.eq(_fld,fld._fld);
  }

}
