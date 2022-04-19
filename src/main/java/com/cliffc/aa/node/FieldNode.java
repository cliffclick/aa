package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.type.*;

// Takes a static field name, a TypeStruct and returns the field value.
public class FieldNode extends Node {
  public final String _fld;

  public FieldNode(Node struct, String fld) {
    super(OP_FIELD,struct);
    _fld=fld;
  }

  @Override public String xstr() { return "."+_fld; }   // Self short name
  String  str() { return xstr(); } // Inline short name

  @Override public Type value() {
    Type t = val(0);
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

}
