package com.cliffc.aa.node;

import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;

import java.util.Collection;

import static com.cliffc.aa.AA.ARG_IDX;
import static com.cliffc.aa.AA.unimpl;


// Values.  Values mimic a NewObj for a "class" wrapper around some primitives.
// All fields are final, so no Stores and no need to track memory.  Values have
// no identity (e.g. a "3" is a "3" is a "3").  Named types can be passed to
// Loads directly; Loads against fields are honored "as if" the named type is
// both a pointer and a memory.  Loads against fields not in the core ValNode
// use the Type name to get the class via a global flat lookup table; then the
// Load repeats against those fields.
public class ValNode extends ValFunNode {
  final String[] _flds;         // Map from node inputs to local field names
  final int _fidx;
  final TypeFunPtr _tfp;

  private ValNode(String[] flds, TypeStruct ret) {
    super(OP_VAL);
    _flds=flds;
    _fidx = BitsFun.new_fidx(BitsFun.ALL);
    _tfp = TypeFunPtr.make(BitsFun.make0(_fidx),nargs(),TypeMemPtr.NO_DISP,ret);
  }
  @Override public String xstr() { return proto()._ts._name; }
  @Override public Type value() {
    // Wrap a name over a TypeStruct
    TypeStruct ts = proto()._ts;
    for( int i=1; i<len(); i++ ) {
      TypeFld fld = ts.get(_flds[i]);
      TypeFld fld2 = fld.make_from(val(i), TypeFld.Access.Final);
      ts = ts.replace_fld(fld2);
    }
    return ts;
  }
  @Override public TypeMem all_live() { return TypeMem.ALIVE; }
  NewObjNode proto() { return (NewObjNode)in(0).in(0); }
  @Override int nargs() { return _flds.length-1+ARG_IDX; }
  // Declared argument type
  @Override Type argtype(int idx) {
    throw unimpl();
  }
  // Actual type, as a constructor function
  @Override TypeFunPtr funtype() { return _tfp; }

  // Build a ValNode default constructor from the NewObj.  Walk all fields.
  // If the field is ANY (dead f-ref), ignore it.
  // If the field is MUTABLE, it was a default set; make it immutable and a
  // required constructor arg.
  // If the final field  is_con, leave it in the prototype object.
  // If the final field !is_con, need a normal function constructor NOT a ValNode.
  public static ValNode make(Node proj) {
    NewObjNode proto = (NewObjNode)proj.in(0);
    Ary<String> flds = new Ary<>(new String[1],0);
    flds.push(null);            // Prototype in slot 0

    Collection<TypeFld> oflds = proto._ts.osorted_flds();
    for( TypeFld fld : oflds ) {
      Type pt = proto.val(fld._order);
      if( fld._access==TypeFld.Access.RW ) {
        if( pt != Type.XNIL  ) throw unimpl();   // Default constructed; "fld := init" mutable not allowed in Val
        flds.push(fld._fld);
      }
      if( (pt==Type.ANY ||            // Dead
           pt.is_con() ||             // Find class constants in the prototype
           pt instanceof TypeFunPtr ) )// Includes e.g. instance methods
        continue;                    // Leave in prototype
      throw unimpl();      // Non-constant field, needs a full function
    }


    ValNode val = new ValNode(flds.asAry(),proto._ts);
    val.add_def(proj);          // Prototype in slot 0
    for( TypeFld fld : oflds )  // Gather remaining RW fields for constructor
      if( fld._access==TypeFld.Access.RW )
        val.add_def(con(fld._t));
    return val;
  }

}
