package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;
import org.junit.Test;

import static com.cliffc.aa.AA.REZ_IDX;
import static com.cliffc.aa.type.TypeFld.Access;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class TestLive {
  @Test public void testBasic() {
    GVNGCM gvn = new GVNGCM();

    // Liveness is a backwards flow.  Scope always demands all return results.
    ScopeNode scope = new ScopeNode(false);

    Node fullmem = new ConNode<>(TypeMem.FULL);
    fullmem._val = TypeMem.FULL;
    scope.set_mem(fullmem);

    // Return the number '5' - should be alive with no special memory.
    Node rez = new ConNode<>(TypeInt.con(5));
    rez._val = TypeInt.con(5);
    scope.set_rez(rez);

    // Check liveness base case
    scope.xliv();
    assertEquals(TypeMem.ANYMEM,scope._live);

    // Check liveness recursive back one step
    rez.xliv();
    assertEquals(TypeMem.ALIVE,rez._live);
  }

  @SuppressWarnings("unchecked")
  @Test public void testNewObj() {
    GVNGCM gvn = Env.GVN;
    Node._INIT0_CNT = 1; // No prims
    // Always memory for the NewObj
    Node mmm = new ConNode<>(TypeMem.ANYMEM).keep();
    mmm._val = TypeMem.ANYMEM;

    // Fields
    Type ti5 = TypeInt.con(5);
    ConNode fdx = new ConNode(ti5);
    fdx._val = ti5;
    Type ti9 = TypeInt.con(9);
    ConNode<Type> fdy = new ConNode<>(ti9);
    fdy._val = ti9;

    // New object, fields x,y holding ints
    int alias = BitsAlias.new_alias(BitsAlias.REC);
    NewObjNode nnn = new NewObjNode(false,alias,TypeMemPtr.DISPLAY,Node.con(Type.NIL));
    nnn.create_active("x",fdx,Access.Final);
    nnn.create_active("y",fdy,Access.Final);
    nnn._val = Type.ANY;
    nnn.no_more_fields();
    nnn.xval();
    nnn._live = TypeMem.ALIVE;

    // Proj, OProj
    Node mem = new MrgProjNode(nnn,mmm);
    mem.xval();
    Node ptr = new  ProjNode(REZ_IDX, nnn);
    ptr.xval();

    // Use the object for scope exit
    ScopeNode scope = new ScopeNode(false);
    scope.set_mem(mem);
    scope.set_rez(ptr);
    scope._val = TypeTuple.EXIT_STATE;

    // Check 'live' is stable on creation, except for mem & scope
    // which are 'turning around' liveness.
    // Value was computed in a forwards flow.
    for( Node n : new Node[]{mmm,fdx,fdy,nnn,mem,ptr,scope} ) {
      if( n != mem && n != scope )
        assertTrue(n.live().isa(n._live));
      assertEquals(n._val,n.value());
    }

    // Check liveness base case
    scope.xliv();
    // Since simple forwards-flow, the default memory is known UNUSED.
    // However, we got provided at least one object.
    TypeMem expected_live = ((TypeMem) mem._val).flatten_fields();
    assertEquals(scope._live,expected_live);

    // Check liveness recursive back one step
    ptr.xliv();
    assertEquals(TypeMem.ALIVE,ptr._live); // Ptr is all_type, conservative so all memory alive
    mem.xliv();
    assertEquals(mem._live,expected_live); // Object demands of OProj, but OProj passes along request to NewObj
    nnn.xliv();
    assertEquals(expected_live,nnn._live); // NewObj supplies object, needs what its input needs
    mmm.xliv();
    assertEquals(TypeMem.ALIVE,mmm._live); // Since ptr is scalar, all memory is alive
    fdx.xliv();
    assertEquals(TypeMem.ALIVE,fdx._live); // Since ptr is scalar, all memory is alive

  }
}
