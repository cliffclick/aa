package com.cliffc.aa;

import com.cliffc.aa.GVNGCM;
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
    scope._live = scope.compute_live(gvn);
    assertEquals(scope._live,TypeMem.EMPTY);

    // Check liveness recursive back one step
    rez._live = rez.compute_live(gvn);
    assertEquals(rez._live,TypeMem.EMPTY);
  }

  @Test public void testNewObj() {
    GVNGCM gvn = new GVNGCM();
    GVNGCM._INIT0_CNT = 1; // No prims
    // Always control for the NewObj
    Node ctl = new ConNode<>(Type.CTRL);
    gvn.setype(ctl,ctl.all_type());

    // Fields
    ConNode<TypeInt> fdx = new ConNode<>(TypeInt.con(5));
    gvn.setype(fdx,fdx.all_type());
    ConNode<TypeInt> fdy = new ConNode<>(TypeInt.con(9));
    gvn.setype(fdy,fdy.all_type());

    // New object, fields x,y holding ints
    NewObjNode nnn = new NewObjNode(false,TypeStruct.DISPLAY,ctl,gvn.con(Type.NIL));
    nnn.create_active("x",fdx,TypeStruct.FFNL,gvn);
    nnn.create_active("y",fdy,TypeStruct.FFNL,gvn);

    // Proj, OProj
    Node mem = new OProjNode(nnn,0);
    gvn.setype(mem,mem.all_type());
    Node ptr = new  ProjNode(nnn,1);
    gvn.setype(ptr,ptr.all_type());

    // Starting full memory
    Node fullmem = new ConNode<>(TypeMem.FULL);
    gvn.setype(fullmem,fullmem.all_type());

    // MemMerge object with all memory
    MemMergeNode mmm = new MemMergeNode(fullmem,mem,nnn._alias);
    gvn.setype(mmm,mmm.all_type());

    // Use the object for scope exit
    ScopeNode scope = new ScopeNode(null,false);
    scope.set_mem(mmm,gvn);
    scope.set_rez(ptr,gvn);

    // Check liveness base case
    scope._live = scope.compute_live(gvn);
    assertEquals(scope._live,TypeMem.EMPTY);

    // Check liveness recursive back one step
    ptr._live = ptr.compute_live(gvn);
    assertEquals(ptr._live,TypeMem.FULL); // Ptr is all_type, conservative so all memory alive
    mmm._live = mmm.compute_live(gvn);
    assertEquals(mmm._live,TypeMem.FULL);
    mem._live = mem.compute_live(gvn);
    assertEquals(mem._live,TypeMem.make(nnn._alias,TypeObj.OBJ));
    nnn._live = nnn.compute_live(gvn);
    assertEquals(nnn._live,TypeMem.FULL); // Since ptr is scalar, all memory is alive
    ctl._live = ctl.compute_live(gvn);
    assertEquals(ctl._live,TypeMem.FULL); // Since ptr is scalar, all memory is alive
    fdx._live = fdx.compute_live(gvn);
    assertEquals(fdx._live,TypeMem.FULL); // Since ptr is scalar, all memory is alive

    // Now flow types forward.
    gvn.setype(nnn,nnn.value(gvn));
    gvn.setype(mem,mem.value(gvn));
    gvn.setype(ptr,ptr.value(gvn));
    gvn.setype(mmm,mmm.value(gvn));

    // Check liveness again, but with refined types
    ptr._live = ptr.compute_live(gvn);
    assertEquals(ptr._live,TypeMem.EMPTY);
    mem._live = mem.compute_live(gvn);
    assertEquals(mem._live,TypeMem.make(nnn._alias,TypeObj.OBJ));
    nnn._live = nnn.compute_live(gvn);
    assertEquals(nnn._live,TypeMem.EMPTY); // Since ptr is scalar, all memory is alive
    ctl._live = ctl.compute_live(gvn);
    assertEquals(ctl._live,TypeMem.EMPTY); // Since ptr is scalar, all memory is alive
    fdx._live = fdx.compute_live(gvn);
    assertEquals(fdx._live,TypeMem.EMPTY); // Since ptr is scalar, all memory is alive


  }
}
