package com.cliffc.aa.node;

import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.unimpl;

// Takes a static field name, a TypeStruct and returns the field value.
public class FieldNode extends Node {
  public final String _fld;

  FieldNode(Node struct, String fld) {
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
    if( fld==null ) return t.oob(Type.SCALAR);
    return fld._t;
  }

}
