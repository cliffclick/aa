package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class TestLive {
  @Test public void testBasic() {
    GVNGCM gvn = new GVNGCM();

    // Liveness is a backwards flow.  Scope always demands all return results.
    ScopeNode scope = new ScopeNode(null,false);

    Node fullmem = new ConNode<>(TypeMem.FULL);
    fullmem._val = TypeMem.FULL;
    scope.set_mem(fullmem,gvn);

    // Return the number '5' - should be alive with no special memory.
    Node rez = new ConNode<>(TypeInt.con(5));
    rez._val = TypeInt.con(5);
    scope.set_rez(rez,gvn);

    // Check liveness base case
    scope.xliv(gvn._opt_mode);
    assertEquals(scope._live,TypeMem.ALLMEM);

    // Check liveness recursive back one step
    rez.xliv(GVNGCM.Mode.PesiCG);
    assertEquals(rez._live,TypeMem.ALIVE);
  }

  @SuppressWarnings("unchecked")
  @Test public void testNewObj() {
    Env env = Env.top_scope();
    GVNGCM gvn = Env.GVN;
    GVNGCM._INIT0_CNT = 1; // No prims
    // Always memory for the NewObj
    Node mmm = new ConNode<>(TypeMem.ANYMEM);
    mmm._val = TypeMem.ANYMEM;

    // Fields
    Type ti5 = TypeInt.con(5);
    ConNode fdx = new ConNode(ti5);
    fdx._val = ti5;
    Type ti9 = TypeInt.con(9);
    ConNode<Type> fdy = new ConNode<>(ti9);
    fdy._val = ti9;

    // New object, fields x,y holding ints
    NewObjNode nnn = new NewObjNode(false,TypeStruct.DISPLAY,gvn.con(Type.NIL));
    nnn.create_active("x",fdx,TypeStruct.FFNL);
    nnn.create_active("y",fdy,TypeStruct.FFNL);
    nnn._val = Type.ANY;
    nnn.no_more_fields();
    nnn.xval(gvn._opt_mode);
    nnn._live = TypeMem.LIVE_BOT;

    // Proj, OProj
    Node mem = new MrgProjNode(nnn,mmm);
    mem.xval(gvn._opt_mode);
    Node ptr = new  ProjNode(1, nnn);
    ptr.xval(gvn._opt_mode);

    // Use the object for scope exit
    ScopeNode scope = new ScopeNode(null,false);
    scope.set_mem(mem,gvn);
    scope.set_rez(ptr,gvn);
    scope._val = Type.ALL;

    // Check 'live' is stable on creation, except for mem & scope
    // which are 'turning around' liveness.
    // Value was computed in a forwards flow.
    for( Node n : new Node[]{mmm,fdx,fdy,nnn,mem,ptr,scope} ) {
      if( n != mem && n != scope )
        assertTrue(n.live(gvn._opt_mode).isa(n._live));
      assertEquals(n._val,n.value(gvn._opt_mode));
    }

    // Check liveness base case
    scope.xliv(GVNGCM.Mode.PesiNoCG);
    // Since simple forwards-flow, the default memory is known UNUSED.
    // However, we got provided at least one object.
    TypeMem expected_live = ((TypeMem)mem._val).flatten_fields();
    assertEquals(scope._live,expected_live);

    // Check liveness recursive back one step
    ptr.xliv(GVNGCM.Mode.PesiNoCG);
    assertEquals(TypeMem.ALIVE,ptr._live); // Ptr is all_type, conservative so all memory alive
    mem.xliv(GVNGCM.Mode.PesiNoCG);
    assertEquals(mem._live,expected_live); // Object demands of OProj, but OProj passes along request to NewObj
    nnn.xliv(GVNGCM.Mode.PesiNoCG);
    assertEquals(TypeMem.ALIVE,nnn._live); // NewObj supplies object, needs what its input needs
    mmm.xliv(GVNGCM.Mode.PesiNoCG);
    assertEquals(TypeMem.ALIVE,mmm._live); // Since ptr is scalar, all memory is alive
    fdx.xliv(GVNGCM.Mode.PesiNoCG);
    assertEquals(TypeMem.ESCAPE,fdx._live); // Since ptr is scalar, all memory is alive

  }
}
