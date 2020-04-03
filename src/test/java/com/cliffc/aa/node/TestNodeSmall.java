package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import org.junit.Test;

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
    //for( int i=0; i<argss.length; i++ )
    //  assertEquals(tns[i].at(2),argss[i].at(ins.length));
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
      TypeTuple.make( tctl, tfull, tmul, txscl, tabc , tmul ), //  ~S    str  [ int,flt] ; bad      high
      TypeTuple.make( tctl, tfull, tmul, t2   , tabc , tmul ), //   2    str  [ int,flt] ; bad+good
    };
    _testMonotonicChain(ins,call,argss_mul1);

    // Simple XCTRL check
    TypeTuple[] argss_mul1x = new TypeTuple[] {
      TypeTuple.make( txctl, tfull, tmul, txscl, txscl, tmulX), //  ~S    ~S   [+int+flt]
      TypeTuple.make( txctl, tfull, tmul, t2   , txscl, tmulX), //   2    ~S   [+int+flt]
      TypeTuple.make( txctl, tfull, tmul, t2   , t3   , tmul ), //   2     3   [ int,flt]
      TypeTuple.make( txctl, tfull, tmul, t2   , tscl , tmul ), //   2     S   [ int,flt]
      TypeTuple.make( txctl, tfull, tmul, tscl , tscl , tmul ), //   S     S   [ int,flt]
      TypeTuple.make( txctl, tfull, tmul, txscl, tabc , tmul ), //  ~S    str  [ int,flt]
      TypeTuple.make( txctl, tfull, tmul, t2   , tabc , tmul ), //   2    str  [ int,flt]
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
      TypeTuple.make( tctl, tfull, tadd, t2   , tabc , tadd ), //   2    str  [ int,flt,str] (BG_,BG_,BG_) ; All  bad , keep all, meet
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
    //tmul = tmulX.dual();
    //tadd = taddX.dual();
    // Same math as Unresolved
    tintX = tintX.dual().make_high_fidx();
    tfltX = tfltX.dual().make_high_fidx();
    tstrX = tstrX.dual().make_high_fidx();
    tflt_intX = (TypeFunPtr)tfltX.join(tintX);

    assert taddX.isa(tflt_intX) && tflt_intX.isa(tfltX) && tfltX.isa(tflt_int) && tflt_int.isa(tadd);

    // Check the fptr {+int+flt} choices
    call.set_fun(ins[2]=fp_mul,gvn);
    TypeTuple[] argss_mul2 = new TypeTuple[] {                  // arg2  arg2   resolve
      TypeTuple.make( tctl, tfull, tmulX, txscl, txscl, tmulX), //  ~S    ~S   [+int+flt]
      TypeTuple.make( tctl, tfull, tmulX, t2   , txscl, tmulX), //   2    ~S   [+int+flt]
      TypeTuple.make( tctl, tfull, tmulX, t2   , t3   , tmulX), //   2     3   [ int,flt]
      TypeTuple.make( tctl, tfull, tmulX, t2   , tscl , tmul ), //   2     S   [ int,flt]
      TypeTuple.make( tctl, tfull, tmulX, tscl , tscl , tmul ), //   S     S   [ int,flt]
      TypeTuple.make( tctl, tfull, tmulX, txscl, tscl , tmul ), //  ~S     S   [ int,flt]
      TypeTuple.make( tctl, tfull, tmulX, txscl, tabc , tmul ), //  ~S    str  [ int,flt]
      TypeTuple.make( tctl, tfull, tmulX, t2   , tabc , tmul ), //   2    str  [ int,flt]
    };
    _testMonotonicChain(ins,call,argss_mul2);

    // Simple XCTRL check
    TypeTuple[] argss_mul2x = new TypeTuple[] {
      TypeTuple.make( txctl, tfull, tmulX, txscl, txscl, tmulX), //  ~S    ~S   [+int+flt]
      TypeTuple.make( txctl, tfull, tmulX, t2   , txscl, tmulX), //   2    ~S   [+int+flt]
      TypeTuple.make( txctl, tfull, tmulX, t2   , t3   , tmulX), //   2     3   [ int,flt]
      TypeTuple.make( txctl, tfull, tmulX, t2   , tscl , tmul ), //   2     S   [ int,flt]
      TypeTuple.make( txctl, tfull, tmulX, tscl , tscl , tmul ), //   S     S   [ int,flt]
      TypeTuple.make( txctl, tfull, tmulX, txscl, tabc , tmul ), //  ~S    str  [ int,flt]
      TypeTuple.make( txctl, tfull, tmulX, t2   , tabc , tmul ), //   2    str  [ int,flt]
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

}
