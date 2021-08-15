package com.cliffc.aa.node;

import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.NonBlockingHashMap;

/**
 * Allocates a TypeAry in memory.  Takes in the size and initial element value
 * produces the pointer.  Hence liveness is odd.
 */
abstract class NewAryNode extends NewNode.NewPrimNode<TypeAry> {
  public NewAryNode( TypeAry tary, String name, int op_prec,TypeInt sz ) {
    super(OP_NEWARY,BitsAlias.AARY,tary,name,false,op_prec,Type.CTRL,TypeMem.ALLMEM,null,sz);
  }
  @Override TypeAry dead_type() { return TypeAry.ARY.dual(); }

  protected static void add_libs( Ary<NewPrimNode> INTRINSICS ) {
    INTRINSICS.push(new NewAry(TypeAry.ARY0,TypeInt.INT64));
  }

  // --------------------------------------------------------------------------
  // "[" defines a new array, and expects an integer size.  Produces
  // partial-alloc type which is consumed by "]" to produce the array.
  public static class NewAry extends NewAryNode {
    public NewAry( TypeAry tary, TypeInt sz ) { super(tary,"[",0,sz); }
    @Override public String bal_close() { return "]"; } // Balanced op
    @Override public byte op_prec() { return 0; } // Balanced op
    @Override TypeObj valueobj() {
      Type sz = val(3);
      if( !(sz instanceof TypeInt) ) return sz.oob(TypeObj.ISUSED);
      // Storage class can be found by looking at _live, needs the reverse-flow of use sizes.
      return TypeAry.make((TypeInt)sz,Type.XNIL,TypeObj.OBJ);
    }
  }

  //@Override public TV2 new_tvar(String alloc_site) {
  //  final Node n = this;
  //  NonBlockingHashMap<Comparable,TV2> args = new NonBlockingHashMap<Comparable,TV2>(){{
  //      put(" len" ,TV2.make_base(null,TypeInt.INT64,alloc_site));
  //      put(" elem",TV2.make_leaf(null,alloc_site));
  //    }};
  //  return TV2.make("Obj",this,alloc_site,args);
  //}

  //@Override public boolean unify( boolean test ) {
  //  // Self should always should be a TObj
  //  TV2 tvar = tvar();
  //  if( tvar.is_dead() ) return false;
  //  if( _defs._len <=3 ) return false; // Mid-kill
  //  if( tvar.isa("Obj") &&
  //      tvar.get(" len") == tvar(3) && // Size equals
  //      tvar.get(" elem") != null )    // Has an element type
  //    return false;
  //  // Structural unification on all fields
  //  return tvar.unify_at(" len",tvar(3),test);
  //}

}

