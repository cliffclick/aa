package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class TestLive {
  @Test public void testBasic() {
    GVNGCM gvn = new GVNGCM();

    // Liveness is a backwards flow.  Scope always demands all return results.
    ScopeNode scope = new ScopeNode(null,false);

    Node fullmem = new ConNode<>(TypeMem.FULL);
    gvn.setype(fullmem,fullmem.all_type());
    scope.set_mem(fullmem,gvn);

    // Return the number '5' - should be alive with no special memory.
    Node rez = new ConNode<>(TypeInt.con(5));
    scope.set_rez(rez,gvn);

    // Check liveness base case
    scope._live = scope.live(gvn);
    assertEquals(scope._live,TypeMem.EMPTY);

    // Check liveness recursive back one step
    rez._live = rez.live(gvn);
    assertEquals(rez._live,TypeMem.EMPTY);
  }

  @Test public void testNewObj() {
    GVNGCM gvn = new GVNGCM();
    GVNGCM._INIT0_CNT = 1; // No prims
    // Always control for the NewObj
    Node ctl = new ConNode<>(Type.CTRL);
    gvn.setype(ctl,ctl.all_type());

    // Fields
    ConNode<Type<TypeInt>> fdx = new ConNode<>(TypeInt.con(5));
    gvn.setype(fdx,fdx.all_type());
    ConNode<Type> fdy = new ConNode<>(TypeInt.con(9));
    gvn.setype(fdy,fdy.all_type());

    // New object, fields x,y holding ints
    NewObjNode nnn = new NewObjNode(false,TypeStruct.DISPLAY,ctl,gvn.con(Type.NIL));
    nnn.create_active("x",fdx,TypeStruct.FFNL,gvn);
    nnn.create_active("y",fdy,TypeStruct.FFNL,gvn);
    gvn.setype(nnn,nnn.value(gvn));

    // Proj, OProj
    Node mem = new OProjNode(nnn,0);
    gvn.setype(mem,mem.value(gvn));
    Node ptr = new  ProjNode(nnn,1);
    gvn.setype(ptr,ptr.value(gvn));

    // Starting full memory
    Node fullmem = new ConNode<>(TypeMem.FULL);
    gvn.setype(fullmem,fullmem.all_type());

    // MemMerge object with all memory
    MemMergeNode mmm = new MemMergeNode(fullmem,mem,nnn._alias);
    gvn.setype(mmm,mmm.value(gvn));

    // Use the object for scope exit
    ScopeNode scope = new ScopeNode(null,false);
    scope.set_mem(mmm,gvn);
    scope.set_rez(ptr,gvn);
    gvn.setype(scope,scope.all_type());

    // Check 'live' is stable on creation, except for mmm & scope
    // which are 'turning around' liveness.
    // Value was computed in a forwards flow.
    for( Node n : new Node[]{ctl,fdx,fdy,nnn,mem,ptr,fullmem,mmm,scope} ) {
      if( n != mmm && n != scope )
        assertEquals(n._live,n.live(gvn));
      assertEquals(gvn.type(n),n.value(gvn));
    }

    // Check liveness base case
    scope._live = scope.live(gvn);
    // Since simple forwards-flow, the default memory is known dead/XOBJ.
    // However, we got provided at least one object.
    TypeMem expected_live = TypeMem.make(nnn._alias,(TypeObj)gvn.type(mem));
    assertEquals(scope._live,expected_live);

    // Check liveness recursive back one step
    ptr._live = ptr.live(gvn);
    assertEquals(ptr._live,TypeMem.EMPTY); // Ptr is all_type, conservative so all memory alive
    mmm._live = mmm.live(gvn);
    assertEquals(mmm._live,expected_live);
    mem._live = mem.live(gvn);
    assertEquals(mem._live,TypeMem.EMPTY);
    nnn._live = nnn.live(gvn);
    assertEquals(nnn._live,TypeMem.EMPTY); // Since ptr is scalar, all memory is alive
    ctl._live = ctl.live(gvn);
    assertEquals(ctl._live,TypeMem.EMPTY); // Since ptr is scalar, all memory is alive
    fdx._live = fdx.live(gvn);
    assertEquals(fdx._live,TypeMem.EMPTY); // Since ptr is scalar, all memory is alive

  }
}
