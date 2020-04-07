package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class TestNodeSmall {

  private Type[] _testMonotonicChain(Node[] ins, Node n, TypeTuple[] argss) {
    GVNGCM gvn = Env.GVN;

    // First validate the test itself
    int len = argss.length;
    int num = argss[0]._ts.length;
    for( int i=0; i<len; i++ ) {
      TypeTuple tti = argss[i];
      midloop:
      for( int j=i+1; j<len; j++ ) { // Triangulate
        TypeTuple ttj = argss[j];
        for( int k=0; k<num-1; k++ )
          if( !tti.at(k).isa(ttj.at(k)) )
            continue midloop;
        Type ttiN = tti.at(num-1);
        Type ttjN = ttj.at(num-1);
        assertTrue("Test is broken: "+tti+" isa "+ttj+", but "+ttiN+" !isa "+ttjN,ttiN.isa(ttjN));
      }
    }


    // Now call Node.value() call, and compare to expected
    TypeTuple[] tns= new TypeTuple[argss.length];
    for( int i=0; i<argss.length; i++ ) {
      for( int j=0; j<ins.length; j++ )
        gvn.setype(ins[j], argss[i].at(j));
      tns[i] = (TypeTuple)n.value(gvn);
    }
    // Equals check after computing them all
    for( int i=0; i<argss.length; i++ )
      assertEquals(argss[i].at(ins.length),tns[i].at(2));
    return tns;
  }

  /** Valdiate monotonicity of CallNode.resolve().  There are only a couple of
   *  interesting variants; this test also tests e.g. XCTRL for correctness but
   *  its implementation is a simple cutout, same for the display arg "^" being
   *  NO_DISP.
   *
   *  === High mul fptr (e.g. GCP) ===
   *  arg1  arg2    fptr*      resolve
   *   ~S    ~S   [~int+flt]  [~int+flt]   Choices all around
   *    2    ~S   [~int+flt]  [~int+flt]   Choices all around; arg2 can fall to e.g. 3 or 3.14
   *    2     3   [~int+flt]  [~int+XXX]   Valid to cutout flt or allow (least_cost will resolve)
   *    2     S   [~int+flt]  [ int,flt]   Error state, but arg2 may lift
   *    S     S   [~int+flt]  [ int,flt]   Error state, but args may lift
   *   ~S     S   [~int+flt]  [ int,flt]   Error state in GCP, args may lift in ITER
   *   ~S    str  [~int+flt]  [ int,flt]   Error state - sideways
   *    2    str  [~int+flt]  [ int,flt]   Error state - sideways
   *
   *  === High add fptr (e.g. GCP) ===
   *  arg1  arg2     fptr+           resolve
   *   ~S    ~S   [~int+flt+str]  [~int+flt+str]   Choices all around
   *   2     ~S   [~int+flt+str]  [~int+XXX    ]   Cutout str, but int,flt OK
   *   2     3    [~int+flt+str]  [~int+XXX    ]   Valid to cutout flt or allow (least_cost will resolve by lowering)
   *   2     S    [~int+flt+str]  [ int,flt    ]   Error state, but arg2 may lift
   *   S     S    [~int+flt+str]  [ int,flt,str]   Error state, but args may lift
   *   2     str  [~int+flt+str]  [ int,flt,str]   Error state, none of {int,flt,str} work
   *   ~S    str  [~int+flt+str]  [        ~str]   Choice, since may yet be error
   *   str   str  [~int+flt+str]  [        ~str]   Choice, since may yet be error
   *
   *  === Low fptr (GCP, but also ITER depending on implementation choices )  ===
   *  arg1  arg2    fptr        resolve
   *   X     X    [ int,flt]  [  SAME  ]   Same as high fptr
   *   2     ~S   [~int+flt]  [~int+flt]   Error args
   *   2     3    [ int,flt]  [ int,XXX]   Low, not high, for all good args
   */
  @SuppressWarnings("unchecked")
  @Test public void testCallNodeIntInt() {
    GVNGCM gvn = Env.GVN;

    // Make a Unknown/CallNode/CallEpi combo.
    // Unwired.  Validate the resolve process and monotonicity.
    gvn._opt_mode=0;
    ConNode ctrl = (ConNode) gvn.xform(new ConNode<>(Type.CTRL));
    UnresolvedNode fp_mul = (UnresolvedNode)Env.top().lookup("*"); // {int int -> int} and {flt flt -> flt}
    UnresolvedNode fp_add = (UnresolvedNode)Env.top().lookup("+"); // {int int -> int} and {flt flt -> flt} and {str str -> str}
    ConNode mem  = gvn.init(new ConNode<>(TypeMem.FULL));
    ConNode arg1 = gvn.init(new ConNode<>(Type.SCALAR));
    ConNode arg2 = gvn.init(new ConNode<>(Type.SCALAR));
    CallNode call = (CallNode)gvn.xform(new CallNode(true, null, ctrl, mem, fp_mul, arg1, arg2));
    CallEpiNode cepi = (CallEpiNode)gvn.xform(new CallEpiNode(call)); // Unwired

    gvn.unreg(call);            // Will be hacking edges
    Node[] ins = new Node[]{ctrl,mem,fp_mul,arg1,arg2};

    Type tctl = Type.CTRL, txctl = Type.XCTRL;
    Type tscl = Type.SCALAR, txscl = Type.XSCALAR;
    Type tnil = Type.NIL;
    TypeMem tfull = TypeMem.FULL;
    Type t2 = TypeInt.con(2);
    Type t3 = TypeInt.con(3);
    Type tabc=TypeMemPtr.ABCPTR;

    // iter(), not gcp().  Types always rise.  Very low types might lift to be
    // valid, but e.g. a 2:int will never lift to a str.
    gvn._opt_mode=1;

    // The various kinds of results we expect
    TypeFunPtr tmul = (TypeFunPtr)fp_mul.value(gvn);
    TypeFunPtr tadd = (TypeFunPtr)fp_add.value(gvn);
    TypeFunPtr tmulX= tmul.dual();  assert tmulX.fidxs().above_center();
    TypeFunPtr taddX= tadd.dual();

    TypeFunPtr tfltX = ((TypeFunPtr)gvn.type(fp_add.in(0))).dual(); assert tfltX.fidxs().above_center();
    TypeFunPtr tintX = ((TypeFunPtr)gvn.type(fp_add.in(1))).dual(); assert tintX.fidxs().above_center();
    TypeFunPtr tstrX = ((TypeFunPtr)gvn.type(fp_add.in(2))).dual(); assert tstrX.fidxs().above_center();
    TypeFunPtr tstr  = tstrX.dual();
    TypeFunPtr tflt_intX = (TypeFunPtr)tfltX.join(tintX);       assert tflt_intX.fidxs().above_center();
    TypeFunPtr tflt_int  = tflt_intX.dual();
    TypeFunPtr tmulE = TypeFunPtr.make(BitsFun.EMPTY,TypeStruct.make_args(TypeStruct.ts(Type.SCALAR,TypeStruct.NO_DISP,Type.NIL,Type.NIL))); // All bad choices
    assert taddX.isa(tflt_intX) && tflt_intX.isa(tfltX) && tfltX.isa(tflt_int) && tflt_int.isa(tadd);


    // Check the fptr {int,flt} meet
    call.set_fun(ins[2]=fp_mul,gvn);
    TypeTuple[] argss_mul1 = new TypeTuple[] {                 // arg1  arg2   resolve
      TypeTuple.make( tctl, tfull, tmul, txscl, txscl, tmulX), //  ~S    ~S   [+int+flt] ;          high
      TypeTuple.make( tctl, tfull, tmul, t2   , txscl, tmulX), //   2    ~S   [+int+flt] ;     good+high
      TypeTuple.make( tctl, tfull, tmul, t2   , t3   , tmul ), //   2     3   [ int,flt] ;     good
      TypeTuple.make( tctl, tfull, tmul, t2   , tscl , tmul ), //   2     S   [ int,flt] ; low+good
      TypeTuple.make( tctl, tfull, tmul, tscl , tscl , tmul ), //   S     S   [ int,flt] ; low
      TypeTuple.make( tctl, tfull, tmul, txscl, tscl , tmul ), //  ~S     S   [ int,flt] ; low     +high
      TypeTuple.make( tctl, tfull, tmul, txscl, tabc , tmulX), //  ~S    str  [ int,flt] ; bad      high
      TypeTuple.make( tctl, tfull, tmul, tabc , tabc , tmulE), //  str   str  [        ] ; bad
      TypeTuple.make( tctl, tfull, tmul, t2   , tabc , tmulE), //   2    str  [ int,flt] ; bad+good
    };
    _testMonotonicChain(ins,call,argss_mul1);

    // Simple XCTRL check
    TypeTuple[] argss_mul1x = new TypeTuple[] {
      TypeTuple.make( txctl, tfull, tmul, txscl, txscl, tmulX), //  ~S    ~S   [+int+flt]
      TypeTuple.make( txctl, tfull, tmul, t2   , txscl, tmulX), //   2    ~S   [+int+flt]
      TypeTuple.make( txctl, tfull, tmul, t2   , t3   , tmul ), //   2     3   [ int,flt]
      TypeTuple.make( txctl, tfull, tmul, t2   , tscl , tmul ), //   2     S   [ int,flt]
      TypeTuple.make( txctl, tfull, tmul, tscl , tscl , tmul ), //   S     S   [ int,flt]
      TypeTuple.make( txctl, tfull, tmul, txscl, tabc , tmulX), //  ~S    str  [ int,flt]
      TypeTuple.make( txctl, tfull, tmul, t2   , tabc , tmulE), //   2    str  [ int,flt]
    };
    _testMonotonicChain(ins,call,argss_mul1x);

    // Check the {int,flt,str} meet.
    // Rules:
    // - Some args High & no Low, keep all & join (ignore Good,Bad)
    // - Some args Low & no High, keep all & meet (ignore Good,Bad)
    // - Mix High/Low & no Good , keep all & fidx?join:meet
    // - Some Good, no Low, no High, drop Bad & fidx?join:meet
    // - All Bad, like Low: keep all & meet
    call.set_fun(ins[2]=fp_add,gvn);
    TypeTuple[] argss_add1 = new TypeTuple[] {
      TypeTuple.make( tctl, tfull, tadd, txscl, txscl, taddX), //  ~S    ~S   [+int+flt+str] (__H,__H,__H) ; All  high, keep all, join
      TypeTuple.make( tctl, tfull, tadd, txscl, tabc , taddX), //  ~S    str  [+int+flt+str] (B_H,B_H,_GH) ; Some high, keep all, join
      TypeTuple.make( tctl, tfull, tadd, txscl, tscl , tadd ), //  ~S     S   [ int,flt,str] (L_H,L_H,L_H) ; Mix H/L no Good, fidx/meet
      TypeTuple.make( tctl, tfull, tadd, tnil , txscl, taddX), //   0    ~S   [+int+flt+str] (_GH,_GH,_GH) ; Some high, keep all, join
      TypeTuple.make( tctl, tfull, tadd, tnil , t3, tflt_int), //   0     3   [ int,flt    ] (_G_,_G_,BG_) ; Some good, drop bad, fidx/meet
      TypeTuple.make( tctl, tfull, tadd, tnil , tabc , tstr ), //   0    str  [         str] (BG_,BG_,_G_) ; Some good, drop bad, fidx/meet
      TypeTuple.make( tctl, tfull, tadd, tnil , tscl , tadd ), //   0     S   [ int,flt,str] (LG_,LG_,LG_) ; Some low , keep all, meet
      TypeTuple.make( tctl, tfull, tadd, t2   , txscl, taddX), //   2    ~S   [+int+flt+str] (_GH,_GH,B_H) ; Some high, keep all, join
      TypeTuple.make( tctl, tfull, tadd, t2   , t3, tflt_int), //   2     3   [ int,flt    ] (_G_,_G_,B__) ; Some good, drop bad, fidx/meet
      TypeTuple.make( tctl, tfull, tadd, t2   , tabc , tmulE), //   2    str  [ int,flt,str] (BG_,BG_,BG_) ; All  bad , keep all, meet
      TypeTuple.make( tctl, tfull, tadd, t2   , tscl , tadd ), //   2     S   [ int,flt,str] (LG_,LG_,B__) ; Some low , keep all, meet
      TypeTuple.make( tctl, tfull, tadd, tabc , tabc , tstr ), //  str   str  [         str] (B__,B__,_G_) ; Some good, drop bad, fidx/meet
      TypeTuple.make( tctl, tfull, tadd, tscl , tscl , tadd ), //   S     S   [ int,flt,str] (L__,L__,L__) ; All  low , keep all, meet
    };
    _testMonotonicChain(ins,call,argss_add1);


    // gcp(), not iter().  Types always lower.  Very high types might lower to be
    // valid, but e.g. a 2:int will never lower to a str.
    gvn._opt_mode=2;

    tmulX= (TypeFunPtr)fp_mul.value(gvn); assert tmulX.fidxs().above_center();
    taddX= (TypeFunPtr)fp_add.value(gvn);
    tmul = tmulX.dual();
    tadd = taddX.dual();
    // Same math as Unresolved

    // bugz... this assert fails.
    // tmulX is join of low args with high fidxs: [~11+22] but args int32,int32->int32.
    // Means EMPTY is not "in between" tmulX and tmulX.dual().  Probably required
    // for monotonicity here.
    // Perhaps GCP Unresolved should meet, then dual.
    assert taddX.isa(tflt_intX) && tflt_intX.isa(tfltX) && tfltX.isa(tflt_int) && tflt_int.isa(tadd);

    // Check the fptr {+int+flt} choices
    call.set_fun(ins[2]=fp_mul,gvn);
    TypeTuple[] argss_mul2 = new TypeTuple[] {                  // arg2  arg2   resolve
      TypeTuple.make( tctl, tfull, tmulX, txscl, txscl, tmulX), //  ~S    ~S   [+int+flt]
      TypeTuple.make( tctl, tfull, tmulX, t2   , txscl, tmulX), //   2    ~S   [+int+flt]
      TypeTuple.make( tctl, tfull, tmulX, t2   , t3   , tmulX), //   2     3   [ int,flt]
      TypeTuple.make( tctl, tfull, tmulX, t2   , tscl , tmul ), //   2     S   [ int,flt]
      TypeTuple.make( tctl, tfull, tmulX, tscl , tscl , tmul ), //   S     S   [ int,flt]
      TypeTuple.make( tctl, tfull, tmulX, txscl, tscl , tmulX), //  ~S     S   [ int,flt]
      TypeTuple.make( tctl, tfull, tmulX, txscl, tabc , tmulX), //  ~S    str  [ int,flt]
      TypeTuple.make( tctl, tfull, tmulX, t2   , tabc , tmulE), //   2    str  [ int,flt]
    };
    _testMonotonicChain(ins,call,argss_mul2);

    // Simple XCTRL check
    TypeTuple[] argss_mul2x = new TypeTuple[] {
      TypeTuple.make( txctl, tfull, tmulX, txscl, txscl, tmulX), //  ~S    ~S   [+int+flt]
      TypeTuple.make( txctl, tfull, tmulX, t2   , txscl, tmulX), //   2    ~S   [+int+flt]
      TypeTuple.make( txctl, tfull, tmulX, t2   , t3   , tmulX), //   2     3   [ int,flt]
      TypeTuple.make( txctl, tfull, tmulX, t2   , tscl , tmul ), //   2     S   [ int,flt]
      TypeTuple.make( txctl, tfull, tmulX, tscl , tscl , tmul ), //   S     S   [ int,flt]
      TypeTuple.make( txctl, tfull, tmulX, txscl, tabc , tmulX), //  ~S    str  [ int,flt]
      TypeTuple.make( txctl, tfull, tmulX, t2   , tabc , tmulE), //   2    str  [ int,flt]
    };
    _testMonotonicChain(ins,call,argss_mul2x);

    // Check the {+int+flt+str} choices
    call.set_fun(ins[2]=fp_add,gvn);
    TypeTuple[] argss_add2 = new TypeTuple[] {
      TypeTuple.make( tctl, tfull, taddX, txscl, txscl, taddX), //  ~S    ~S   [+int+flt+str] (__H,__H,__H) ; All  high, keep all, join
      TypeTuple.make( tctl, tfull, taddX, txscl, tabc , taddX), //  ~S    str  [+int+flt+str] (B_H,B_H,_GH) ; Some high, keep all, join
      TypeTuple.make( tctl, tfull, taddX, txscl, tscl , taddX), //  ~S     S   [+int+flt+str] (L_H,L_H,L_H) ; Mix H/L, no good, keep all, fidx/join
      TypeTuple.make( tctl, tfull, taddX, tnil , txscl, taddX), //   0    ~S   [+int+flt+str] (_GH,_GH,_GH) ; Some high, keep all, join
      TypeTuple.make( tctl, tfull, taddX, tnil , t3,tflt_intX), //   0     3   [+int+flt    ] (_G_,_G_,BG_) ; Some good, drop bad, fidx/join
      TypeTuple.make( tctl, tfull, taddX, tnil , tabc , tstrX), //   0    str  [        ~str] (BG_,BG_,_G_) ; Some good, drop bad, fidx/join
      TypeTuple.make( tctl, tfull, taddX, tnil , tscl , tadd ), //   0     S   [ int,flt,str] (LG_,LG_,LG_) ; Some low , keep all, meet
      TypeTuple.make( tctl, tfull, taddX, t2   , txscl, taddX), //   2    ~S   [+int+flt+str] (_GH,_GH,B_H) ; Some high, keep all, join
      TypeTuple.make( tctl, tfull, taddX, t2   , t3,tflt_intX), //   2     3   [+int+flt    ] (_G_,_G_,B__) ; Some good, drop bad, fidx/join
      TypeTuple.make( tctl, tfull, taddX, t2   , tabc , tadd ), //   2    str  [ int,flt,str] (BG_,BG_,BG_) ; All  bad , keep all, meet
      TypeTuple.make( tctl, tfull, taddX, t2   , tscl , tadd ), //   2     S   [ int,flt,str] (LG_,LG_,B__) ; Some low , keep all, meet
      TypeTuple.make( tctl, tfull, taddX, tabc , tabc , tstrX), //  str   str  [        ~str] (B__,B__,_G_) ; Some good, drop bad, fidx/join
      TypeTuple.make( tctl, tfull, taddX, tscl , tscl , tadd ), //   S     S   [ int,flt,str] (L__,L__,L__) ; All  low , keep all, meet
    };
    _testMonotonicChain(ins,call,argss_add2);
  }



  // When making a recursive function, we get a pointer cycle with the display
  // and function arguments.  Validate that we can re-discover this closed
  // cycle during GCP from whole cloth.

  // Code: "fact={ x -> x>1 ? fact(x-1)*x : 1 }"
  // tfp = [36]{^:[*10] x:int -> Scalar}   // Function def, with standard display.  Note the display is dead here.
  // *[10] -> {^:[*6] fact:tfp}            // File-level scope
  // *[6] -> { ^:nil PRIMS...}             // Prim-level scope
  //
  // Here's an example where the display is not dead-by-default:
  // Code: "gen_ctr={cnt;{cnt++}}; ctrA=gen_ctr(); ctrB=gen_ctr(); ctrA(); ctrB(); ctrB()"
  //
  @Test public void testRecursiveDisplay() {
    GVNGCM gvn = Env.GVN;

    // Build the graph for the "fact" example:
    // NewObj (display); inputs are prior display and FunPtr
    //   OProj
    //   DProj
    //   MemMerge; default mem and OProj
    // Fun (and Fun._tf) - Just default control and some other control
    //   Parm:^ - Default display and DProj
    //   Parm:mem - Default mem and the MemMerge of OProj
    //   Ret - {Fun,Mem,Parm:^} - Not really fact() nor gen_ctr() code but upwards exposed closure
    //   FunPtr - Ret
    gvn._opt_mode=0;
    ConNode ctl = (ConNode) gvn.xform(new ConNode<>(Type.CTRL));
    ConNode mem = gvn.init(new ConNode<>(TypeMem.FULL));
    ConNode rpc = gvn.init(new ConNode<>(TypeRPC.ALL_CALL));
    ConNode dsp_prims = (ConNode) gvn.xform(new ConNode<>(TypeMemPtr.DISPLAY_PTR));
    // The file-scope display closing the graph-cycle.  Needs the FunPtr, not
    // yet built.
    NewObjNode dsp_file = gvn.init(new NewObjNode(true,TypeStruct.DISPLAY,ctl,dsp_prims));
    OProjNode dsp_file_obj = gvn.init(new OProjNode(dsp_file,0));
    ProjNode  dsp_file_ptr = gvn.init(new  ProjNode(dsp_file,1));
    MemMergeNode dsp_merge = gvn.init(new MemMergeNode(mem,dsp_file_obj,dsp_file._alias));
    // The Fun and Fun._tf:
    Type[] args = TypeAry.get(3);
    args[0] = Type.SCALAR;            // Return
    args[1] = gvn.type(dsp_file_ptr); // File-scope display as arg0
    args[2] = Type.SCALAR;            // Some scalar arg1
    TypeFunPtr tf = TypeFunPtr.make_new(TypeStruct.make_args(new String[]{"->","^","x"},args));
    FunNode fun = new FunNode("fact",tf,BitsAlias.make0(dsp_file._alias));
    gvn.init(fun.add_def(ctl).add_def(ctl));
    // Parms for the Fun.  Note that the default type is "weak" because the
    // file-level display can not yet know about "fact".
    ParmNode parm_mem = new ParmNode(-2,"mem",fun,mem,null);
    ParmNode parm_dsp = new ParmNode( 0,"^"  ,fun,TypeMemPtr.DISPLAY_PTR,dsp_file_ptr,null);
    gvn.init(parm_mem.add_def(dsp_merge));
    gvn.init(parm_dsp.add_def(dsp_file_ptr));
    // Close the function up
    RetNode ret = gvn.init(new RetNode(fun,parm_mem,parm_dsp,rpc,fun));
    FunPtrNode fptr = gvn.init(new FunPtrNode(ret,dsp_file_ptr));
    // Close the cycle
    dsp_file.create("fact",fptr,TypeStruct.FFNL,gvn);
    // Return the fptr to keep all alive
    ScopeNode env = new ScopeNode(null,true);
    env.set_ctrl(ctl,gvn);
    env.set_ptr (dsp_file_ptr,gvn);
    env.set_mem (dsp_merge,gvn);
    env.set_rez (fptr,gvn);
    gvn.init(env);

    Node[] nodes = new Node[]{ctl,mem,rpc,dsp_prims,dsp_file,dsp_file_obj,dsp_file_ptr,dsp_merge,fun,parm_mem,parm_dsp,ret,fptr,env};

    // Validate graph initial conditions.  No optimizations, as this
    // pile-o-bits is all dead and will vaporize if the optimizer is turned
    // loose on it.  Just check the types flow correctly.
    gvn._opt_mode=1;
    for( Node n : nodes ) {
      Type old = gvn.type(n);
      Type nnn = n.value(gvn);
      assert nnn.isa(old);
    }

    // Now run GCP to closure.  This is the key call being tested.
    gvn.gcp(env);

    // Validate cyclic display/function type
    TypeFunPtr tfptr0 = (TypeFunPtr)gvn.type(fptr);
    Type tdptr0 = tfptr0.display();
    assertEquals(tfptr0.ret(),tdptr0); // Returning the display
    // Display contains 'fact' pointing to self
    TypeStruct tdisp0 = (TypeStruct)((TypeMemPtr)tdptr0)._obj;
    assertEquals(tfptr0,tdisp0.at(tdisp0.find("fact")));


  }
}
