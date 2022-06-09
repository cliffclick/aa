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
    if( !(t instanceof TypeStruct ts) ) return null;
    StructNode clz = proto(ts.clz());
    if( clz==null ) return null;
    return clz.in_bind(_fld,in(0));
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
          lphi.add_def(Env.GVN.add_work_new(new FieldNode(phi.in(i),_fld)));
        subsume(lphi);
        return lphi;
      }
    }

    return null;
  }


  @Override public Type value() {
    Type t = val(0);
    if( !(t instanceof TypeStruct ts) )
      return t.oob();           // Input is not a Struct
    TypeFld fld = ts.get(_fld);
    if( fld!=null ) return fld._t;
    // For named prototypes, if the field load fails, try again in the
    // prototype.  Only valid for final fields.
    StructNode clz = proto(ts.clz());
    if( clz==null ) return t.oob();
    TypeFld pfld = ((TypeStruct) clz._val).get(_fld);
    if( pfld == null ) return t.oob(TypeNil.SCALAR);
    assert pfld._access == TypeFld.Access.Final;
    // If this is a function, act as-if it was pre-bound to 'this' argument
    if( !(pfld._t instanceof TypeFunPtr tfp) || tfp.has_dsp() )
      return pfld._t;           // Clazz field type
    return tfp.make_from(t);
  }

  private static StructNode proto(String clz) {
    if( clz.isEmpty() ) return null;
    String tname = clz.substring(0,clz.length()-1);
    return Env.PROTOS.get(tname);
  }

  @Override public boolean has_tvar() { return true; }

  @Override public boolean unify( boolean test ) {
    TV2 self = tvar();
    TV2 rec = tvar(0);
    if( !test ) rec.push_dep(this);

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
