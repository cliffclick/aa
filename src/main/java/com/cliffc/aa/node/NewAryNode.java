package com.cliffc.aa.node;

import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.NonBlockingHashMap;

import static com.cliffc.aa.AA.ARG_IDX;

// Allocates a TypeAry in memory.  Takes in the size and initial element value
// produces the pointer.  Hence, liveness is odd.
public abstract class NewAryNode extends NewNode.NewPrimNode<TypeAry> {
  public NewAryNode( TypeAry tary, String name, int op_prec, TypeInt sz ) {
    super(OP_NEWARY,BitsAlias.AARY,tary,name,false,TypeAry.ARY,op_prec,TypeFld.make("len",sz,ARG_IDX));
  }
  @Override TypeAry dead_type() { return TypeAry.ARY.dual(); }

  // --------------------------------------------------------------------------
  // "[" defines a new array, and expects an integer size.  Produces
  // partial-alloc type which is consumed by "]" to produce the array.
  public static class NewAry extends NewAryNode {
    public NewAry( ) { super(TypeAry.ARY,"$[",0,TypeInt.INT64); }
    @Override public String bal_close() { return "]"; } // Balanced op
    @Override public byte op_prec() { return 0; } // Balanced op
    @Override TypeObj valueobj() {
      Type sz = val(ARG_IDX);
      if( !(sz instanceof TypeInt) ) return sz.oob(TypeObj.ISUSED);
      // Storage class can be found by looking at _live, needs the reverse-flow of use sizes.
      return TypeAry.make((TypeInt)sz,Type.XNIL,TypeObj.OBJ);
    }
  }

  @Override public TV2 new_tvar(String alloc_site) {
    NonBlockingHashMap<String,TV2> args = new NonBlockingHashMap<>() {{
      put("len" , TV2.make_base(null,TypeInt.INT64,alloc_site));
      put("elem", TV2.make_leaf(null, alloc_site));}};
    return TV2.make("Ary",this,_tptr,alloc_site,args);
  }

  @Override public boolean unify( Work work ) {
    assert _tvar.isa("Ary");     // Self should always should be a Ary
    if( is_unused() ) return false;
    // Length is an int
    TV2 len = tvar(ARG_IDX);
    if( len.is_base() && len._type.isa(TypeInt.INT64) )
      return false;
    return work==null ||        // Fast cutout
      len.unify(TV2.make_base(in(ARG_IDX),TypeInt.INT64,"NewAry"),work);
  }

}

