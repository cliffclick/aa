package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;

// Takes a static field name, a TypeStruct and returns the field value.
// Basically a ProjNode except it does lookups by field name in TypeStruct
// instead of by index in TypeTuple.
public class FieldNode extends Node {
  public final String _fld;

  public FieldNode(Node struct, String fld) {
    super(OP_FIELD,struct);
    _fld=fld;
  }

  @Override public String xstr() { return "."+_fld; }   // Self short name
  String  str() { return xstr(); } // Inline short name

  @Override public Node ideal_reduce() {
    if( (in(0) instanceof StructNode clz) )
      return clz.in_bind(_fld,in(0));
    // For named prototypes, if the field load fails, try again in the
    // prototype.  Only valid for final fields.
    Type t = val(0);
    if( t==Type.NIL || t==Type.XNIL ) t = TypeStruct.ZERO;
    if( !(t instanceof TypeStruct ts) ) return null;
    String tname = ts.clz().substring(0,ts.clz().length()-1);
    StructNode clz = Env.PROTOS.get(tname);
    if( clz==null ) return null;
    return clz.in_bind(_fld,in(0));
  }


  @Override public Type value() {
    Type t = val(0);
    if( t==Type.NIL || t==Type.XNIL ) t = TypeStruct.ZERO;
    if( !(t instanceof TypeStruct ts) )
      return t.oob(Type.SCALAR);
    TypeFld fld = ts.get(_fld);
    if( fld!=null ) return fld._t;
    // For named prototypes, if the field load fails, try again in the
    // prototype.  Only valid for final fields.
    String tname = ts.clz().substring(0,ts.clz().length()-1);
    StructNode clz = Env.PROTOS.get(tname);
    if( clz==null ) return t.oob(Type.SCALAR);
    TypeFld pfld = ((TypeStruct) clz._val).get(_fld);
    if( pfld == null ) return t.oob(Type.SCALAR);
    assert pfld._access == TypeFld.Access.Final;
    // If this is a function, act as-if it was pre-bound to 'this' argument
    if( !(pfld._t instanceof TypeFunPtr tfp) || tfp.has_dsp() )
      return pfld._t;           // Clazz field type
    return tfp.make_from(t);
  }

  @Override public boolean unify( boolean test ) {
    TV2 self = tvar();
    TV2 rec = tvar(0);
    if( test ) rec.push_dep(this);

    // Look up field
    TV2 fld = rec.arg(_fld);
    if( fld!=null )           // Unify against a pre-existing field
      return fld.unify(self, test);

    // Add struct-ness if possible
    if( !rec.is_obj() && !rec.is_nil() ) {
      if( test ) return true;
      rec.make_struct_from();
    }
    // Add the field
    if( rec.is_obj() && rec.is_open() ) {
      if( !test ) rec.add_fld(_fld,self);
      return true;
    }
    // Closed/non-record, field is missing
    return self.set_err(("Missing field "+_fld).intern(),test);
  }

}
