package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;

// Allocates a TypeAry in memory.  Takes in the size and initial element value
// produces the pointer.  Hence liveness is odd.
abstract class NewAryNode extends NewNode.NewPrimNode<TypeAry> {
  public NewAryNode( TypeAry tary, String name, TypeInt sz ) {
    super(OP_NEWARY,BitsAlias.ARY,tary,name,false,null,sz);
  }
  @Override TypeAry dead_type() { return TypeAry.ARY.dual(); }
  // The one string field is memory-alive
  @Override public TypeMem live_use( byte opt_mode, Node def ) { return TypeMem.ANYMEM; }

  protected static void add_libs( Ary<NewPrimNode> INTRINSICS ) {
    INTRINSICS.push(new NewAry(TypeAry.ARY,TypeInt.INT64));
  }

  // --------------------------------------------------------------------------
  // "[" defines a new array, and expects an integer size.  Produces
  // partial-alloc type which is consumed by "]" to produce the array.
  public static class NewAry extends NewAryNode {
    public NewAry( TypeAry tary, TypeInt sz ) { super(tary,"[",sz); }
    @Override public byte op_prec() { return 2; }
    @Override public Node ideal(GVNGCM gvn, int level) { return null; }
    @Override TypeObj valueobj() {
      Type sz = val(3);
      if( !(sz instanceof TypeInt) ) return sz.oob(TypeObj.ISUSED);
      // Storage class can be found by looking at _live, needs the reverse-flow of use sizes.
      return TypeAry.make((TypeInt)sz,Type.XNIL,TypeObj.OBJ);
    }
    public String postop() { return "]"; } // Balancing function name
  }

}

