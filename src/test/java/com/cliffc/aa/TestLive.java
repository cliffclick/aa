package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class TestLive {
  @Test public void testBasic() {
    Node fullmem = new ConNode<>(TypeMem.ALLMEM);
    fullmem._val = TypeMem.ALLMEM;
    fullmem._live = TypeMem.ANYMEM;
    Env.KEEP_ALIVE._live = TypeMem.ANYMEM; // Post-combo
    Env.MEM_0._live = TypeMem.ANYMEM;

    // Return the number '5' - should be alive with no special memory.
    Node rez = new ConNode<>(TypeInt.con(5));
    rez._val = TypeInt.con(5);

    // Liveness is a backwards flow.  Root always demands all return results.
    RootNode root = Env.ROOT;
    root.set_def(1,fullmem);
    root.set_def(2,rez    );
    Combo.HM_FREEZE = true;     // Parsing done, Root gives precise results
    root.xval();
    root.xliv();

    // Check liveness base case
    assertEquals(TypeMem.EXTMEM,root._live);

    // Check liveness recursive back one step
    rez._live = rez.live();
    assertEquals(Type.ALL,rez._live);
    Combo.HM_FREEZE = false;    // Reset
  }

  @Test public void testNewNode() {
    GVNGCM gvn = Env.GVN;
    Node._INIT0_CNT = 1; // No prims
    // Always memory for the NewNode
    Node mmm = new ConNode<>(TypeMem.ANYMEM).init();
    Env.KEEP_ALIVE._live = TypeMem.ANYMEM; // Post-combo
    Env.MEM_0._live = TypeMem.ANYMEM;

    // Fields
    ConNode fdx = new ConNode(TypeInt.con(5)).init();
    ConNode fdy = new ConNode(TypeInt.con(9)).init();

    // New object, fields x,y holding ints
    StructNode obj = new StructNode(0,false,null );
    obj.add_fld("x",TypeFld.Access.Final,fdx,null);
    obj.add_fld("y",TypeFld.Access.Final,fdy,null);
    obj.close().init();

    NewNode ptr = new NewNode().init();
    Node mem = new StoreXNode(mmm,ptr,obj,null).init();

    // Use the object for scope exit
    RootNode root = Env.ROOT;
    root.set_def(1,mem);
    root.set_def(2,ptr);
    Combo.HM_FREEZE = true;     // Parsing done, Root gives precise results
    root.xval();

    // Check 'live' is stable on creation, except for mem & root
    // which are 'turning around' liveness.
    // Value was computed in a forwards flow.
    for( Node n : new Node[]{mmm,fdx,fdy,obj,ptr,mem,root} ) {
      if( n != mem && n != root )
        assertTrue(n.live().isa(n._live));
      assertEquals(n._val,n.value());
    }
    for( Node n : new Node[]{mmm,mem,root} ) {
      n._live = TypeMem.ANYMEM;
    }

    // Check liveness base case
    root.xliv();
    // Since simple forwards-flow, the default memory is known UNUSED.
    // However, we got provided at least one object.
    TypeMem expected_live = ((TypeMem) mem._val.meet(TypeMem.EXTMEM)).flatten_live_fields();
    assertEquals(root._live,expected_live);

    // Check liveness recursive back one step
    mem.xliv();
    assertEquals(mem._live,expected_live); // Object demands of OProj, but OProj passes along request to NewObj
    ptr.xliv();
    assertEquals(TypeMem.ALL,ptr._live);
    mmm.xliv();
    assertEquals(TypeMem.EXTMEM,mmm._live); // Since ptr is scalar, all memory is alive
    fdx.xliv();
    assertEquals(Type.ALL,fdx._live); // Since ptr is scalar, all memory is alive
    Combo.HM_FREEZE = false;          // Reset

  }
}
