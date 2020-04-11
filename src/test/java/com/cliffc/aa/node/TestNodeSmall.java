package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class TestNodeSmall {


  @Test public void testUnresolvedAdd() {
    GVNGCM gvn = Env.GVN;

    // Current theory on Unresolved:  Call.resolve moves closer to the centerline:
    //   LOW  fidxs are all must-calls, and removing one LIFTS .  If args are MEET, removing LIFTS.
    //   HIGH fidxs are all may -calls, and removing one LOWERS.  If args are JOIN, removing LOWERS.

    // Phi: always MEET, so highs meet to empty; and lows MEET.
    // During GCP fidxs are high, then move to low.
    // Call.resolve: choices get removed which lifts or lowers

    // WANT: During GCP, high choices fed to Call.resolve.  Choices get removed, which LOWERS resolved.
    //       Means Unresolved during GCP produces only HIGH choices.
    // WANT: During Iter, low choices fed to Call.resolve.  Choices get removed, which LIFTS  resolved.
    //       Means Unresolved during ITER produces only LOW choices.
    // WANT: Same behavior during GCP and ITER, but doesn't appear I can have that.

    // Unresolved: ITER: all is MEET and no FIDX goes HIGH (except for dead/dying).

    // Unresolved: GCP : if FunPtr above center optional to ignore or JOIN.
    //                   if FunPtr below center, flip to high and JOIN.  Also high/ignore args kept high, and low args moved high for JOIN.
    // Kinda sorta looks like: use startype on incoming, and JOIN.

    gvn._opt_mode=0;
    UnresolvedNode uadd = (UnresolvedNode)Env.top().lookup("+"); // {int int -> int} and {flt flt -> flt} and {str str -> str}
    FunPtrNode aflt = (FunPtrNode)uadd.in(0);
    FunPtrNode aint = (FunPtrNode)uadd.in(1);
    FunPtrNode astr = (FunPtrNode)uadd.in(2);
    // Make a flt/int combo, drops off string.
    UnresolvedNode anum = new UnresolvedNode(null,aflt,aint);

    // All nodes have this property: START >= {ALL.dual(),value(START)} >= value(ALL.dual()) >= value(ALL) >= ALL
    // Holds for both ITER and GCP.


    // Compute Node.all_type() and all_type.startype()
    TypeFunPtr uaddALL = uadd.all_type(), uaddSTART = uaddALL.dual();
    TypeFunPtr anumALL = anum.all_type(), anumSTART = anumALL.dual();
    TypeFunPtr afltALL = aflt.all_type(), afltSTART = afltALL.dual();
    TypeFunPtr aintALL = aint.all_type(), aintSTART = aintALL.dual();
    TypeFunPtr astrALL = astr.all_type(), astrSTART = astrALL.dual();

    // Compute Node.value() where initial GVN is startype()
    gvn.setype(uadd,uaddSTART);
    gvn.setype(anum,anumSTART);
    gvn.setype(aflt,afltSTART);
    gvn.setype(aint,aintSTART);
    gvn.setype(astr,astrSTART);
    gvn._opt_mode=1;
    TypeFunPtr uaddVAL1START = (TypeFunPtr)uadd.value(gvn);
    TypeFunPtr anumVAL1START = (TypeFunPtr)anum.value(gvn);
    TypeFunPtr afltVAL1START = (TypeFunPtr)aflt.value(gvn);
    TypeFunPtr aintVAL1START = (TypeFunPtr)aint.value(gvn);
    TypeFunPtr astrVAL1START = (TypeFunPtr)astr.value(gvn);
    gvn._opt_mode=2;
    TypeFunPtr uaddVAL2START = (TypeFunPtr)uadd.value(gvn);
    TypeFunPtr anumVAL2START = (TypeFunPtr)anum.value(gvn);
    TypeFunPtr afltVAL2START = (TypeFunPtr)aflt.value(gvn);
    TypeFunPtr aintVAL2START = (TypeFunPtr)aint.value(gvn);
    TypeFunPtr astrVAL2START = (TypeFunPtr)astr.value(gvn);

    // Compute Node.value() where initial GVN is all_type.dual()
    gvn.setype(uadd,uaddALL.dual());
    gvn.setype(anum,anumALL.dual());
    gvn.setype(aflt,afltALL.dual());
    gvn.setype(aint,aintALL.dual());
    gvn.setype(astr,astrALL.dual());
    gvn._opt_mode=1;
    TypeFunPtr uaddVAL1XALL = (TypeFunPtr)uadd.value(gvn);
    TypeFunPtr anumVAL1XALL = (TypeFunPtr)anum.value(gvn);
    TypeFunPtr afltVAL1XALL = (TypeFunPtr)aflt.value(gvn);
    TypeFunPtr aintVAL1XALL = (TypeFunPtr)aint.value(gvn);
    TypeFunPtr astrVAL1XALL = (TypeFunPtr)astr.value(gvn);
    gvn._opt_mode=2;
    TypeFunPtr uaddVAL2XALL = (TypeFunPtr)uadd.value(gvn);
    TypeFunPtr anumVAL2XALL = (TypeFunPtr)anum.value(gvn);
    TypeFunPtr afltVAL2XALL = (TypeFunPtr)aflt.value(gvn);
    TypeFunPtr aintVAL2XALL = (TypeFunPtr)aint.value(gvn);
    TypeFunPtr astrVAL2XALL = (TypeFunPtr)astr.value(gvn);

    // Compute Node.value() where initial GVN is all_type()
    gvn.setype(uadd,uaddALL);
    gvn.setype(anum,uaddALL);
    gvn.setype(aflt,afltALL);
    gvn.setype(aint,aintALL);
    gvn.setype(astr,astrALL);
    gvn._opt_mode=1;
    TypeFunPtr uaddVAL1ALL = (TypeFunPtr)uadd.value(gvn);
    TypeFunPtr anumVAL1ALL = (TypeFunPtr)anum.value(gvn);
    TypeFunPtr afltVAL1ALL = (TypeFunPtr)aflt.value(gvn);
    TypeFunPtr aintVAL1ALL = (TypeFunPtr)aint.value(gvn);
    TypeFunPtr astrVAL1ALL = (TypeFunPtr)astr.value(gvn);
    gvn._opt_mode=2;
    TypeFunPtr uaddVAL2ALL = (TypeFunPtr)uadd.value(gvn);
    TypeFunPtr anumVAL2ALL = (TypeFunPtr)anum.value(gvn);
    TypeFunPtr afltVAL2ALL = (TypeFunPtr)aflt.value(gvn);
    TypeFunPtr aintVAL2ALL = (TypeFunPtr)aint.value(gvn);
    TypeFunPtr astrVAL2ALL = (TypeFunPtr)astr.value(gvn);

    TypeFunPtr[] uadds = new TypeFunPtr[]{uaddSTART,uaddALL.dual(),uaddVAL1START,uaddVAL2START,uaddVAL1XALL,uaddVAL2XALL,uaddVAL1ALL,uaddVAL2ALL,uaddALL};
    TypeFunPtr[] anums = new TypeFunPtr[]{anumSTART,anumALL.dual(),anumVAL1START,anumVAL2START,anumVAL1XALL,anumVAL2XALL,anumVAL1ALL,anumVAL2ALL,anumALL};
    TypeFunPtr[] aflts = new TypeFunPtr[]{afltSTART,afltALL.dual(),afltVAL1START,afltVAL2START,afltVAL1XALL,afltVAL2XALL,afltVAL1ALL,afltVAL2ALL,afltALL};
    TypeFunPtr[] aints = new TypeFunPtr[]{aintSTART,aintALL.dual(),aintVAL1START,aintVAL2START,aintVAL1XALL,aintVAL2XALL,aintVAL1ALL,aintVAL2ALL,aintALL};
    TypeFunPtr[] astrs = new TypeFunPtr[]{astrSTART,astrALL.dual(),astrVAL1START,astrVAL2START,astrVAL1XALL,astrVAL2XALL,astrVAL1ALL,astrVAL2ALL,astrALL};
    TypeFunPtr[][] tfpss = new TypeFunPtr[][]{aflts,aints,astrs,anums,uadds};

    // All nodes have these properties:
    //    START >= {ALL.dual(),value1(START)} >= value1(ALL.dual()) >= value1(ALL) >= ALL
    //    START >= {ALL.dual(),value2(START)} >= value2(ALL.dual()) >= value2(ALL) >= ALL
    for( TypeFunPtr[] tfps : tfpss ) {
      TypeFunPtr start = tfps[0], xall  = tfps[1], val1s = tfps[2], val2s = tfps[3];
      TypeFunPtr val1x = tfps[4], val2x = tfps[5], val1a = tfps[6], val2a = tfps[7];
      TypeFunPtr all   = tfps[8];

      assertTrue(start.isa(xall ));
      assertTrue(start.isa(val1s));   assertTrue(start.isa(val2s));
      assertTrue(xall .isa(val1x));   assertTrue(xall .isa(val2x));
      assertTrue(val1s.isa(val1x));   assertTrue(val2s.isa(val2x));
      assertTrue(val1x.isa(val1a));   assertTrue(val2x.isa(val2a));
      assertTrue(val1a.isa(all  ));   assertTrue(val2a.isa(all  ));
    }

    // Also, for CallNode.resolve we want the properties:
    //    UnresolvedAdd.XAll >= AnumAdd.Xall} >= {Flt,Int,Str}XAdd.All-- Removing a choice during GCP  lowers
    //    {Flt,Int,Str}Add.ALL >= AnumAdd.ALL >= UnresolvedAdd.All  -- Removing a choice during ITER lifts
    assertTrue(uaddALL.dual().isa(anumALL.dual()));
    assertTrue(anumALL.dual().isa(afltALL.dual()));
    assertTrue(anumALL.dual().isa(aintALL.dual()));
    assertTrue(uaddALL.dual().isa(astrALL.dual()));

    assertTrue(astrALL.isa(uaddALL));
    assertTrue(aintALL.isa(anumALL));
    assertTrue(afltALL.isa(anumALL));
    assertTrue(anumALL.isa(uaddALL));

  }

  private Type[] _testMonotonicChain(Node[] ins, Node n, TypeTuple[] argss) {
    GVNGCM gvn = Env.GVN;

    // First validate the test itself.  If two tuples are 'isa' then the result
    // is also 'isa'.
    int len = argss.length;
    int num = argss[0]._ts.length;
    for( int i=0; i<len; i++ ) {
      TypeTuple tti = argss[i];
      midloop:
      for( int j=i+1; j<len; j++ ) { // Triangulate
        TypeTuple ttj = argss[j];
        for( int k=0; k<num-1; k++ )
          if( !tti.at(k).isa(ttj.at(k)) ) // All elements except last are 'isa'
            continue midloop;
        Type ttiN = tti.at(num-1); // Then check last element is 'isa'
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


  private static TypeFunPtr v(Node n, GVNGCM gvn) { return (TypeFunPtr)n.value(gvn); }

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
  @Test public void testCallNodeResolve() {
    GVNGCM gvn = Env.GVN;

    // Make a Unknown/CallNode/CallEpi combo.
    // Unwired.  Validate the resolve process and monotonicity.
    gvn._opt_mode=0;
    ConNode ctrl = (ConNode) gvn.xform(new ConNode<>(Type.CTRL));
    UnresolvedNode fp_mul = (UnresolvedNode)Env.top().lookup("*"); // {int int -> int} and {flt flt -> flt}
    UnresolvedNode fp_add = (UnresolvedNode)Env.top().lookup("+"); // {int int -> int} and {flt flt -> flt} and {str str -> str}
    FunPtrNode aflt = (FunPtrNode)fp_add.in(0);
    FunPtrNode aint = (FunPtrNode)fp_add.in(1);
    FunPtrNode astr = (FunPtrNode)fp_add.in(2);
    // Make a flt/int combo, drops off string.
    UnresolvedNode anum = new UnresolvedNode(null,aflt,aint);
    ConNode mem  = gvn.init(new ConNode<>(TypeMem.FULL));
    ConNode arg1 = gvn.init(new ConNode<>(Type.SCALAR));
    ConNode arg2 = gvn.init(new ConNode<>(Type.SCALAR));
    CallNode call = (CallNode)gvn.xform(new CallNode(true, null, ctrl, mem, fp_mul, arg1, arg2));
    CallEpiNode cepi = (CallEpiNode)gvn.xform(new CallEpiNode(call)); // Unwired

    gvn.unreg(call);            // Will be hacking edges
    Node[] ins = new Node[]{ctrl,mem,fp_mul,arg1,arg2};

    // Args to calls
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
    TypeFunPtr tmul1 = v(fp_mul,gvn), tmul1X = tmul1.dual();
    TypeFunPtr tadd1 = v(fp_add,gvn), tadd1X = tadd1.dual();

    TypeFunPtr tnum1 = v(anum,gvn), tnum1X = tnum1.dual();
    TypeFunPtr tflt1 = v(aflt,gvn), tflt1X = tflt1.dual();
    TypeFunPtr tint1 = v(aint,gvn), tint1X = tint1.dual();
    TypeFunPtr tstr1 = v(astr,gvn), tstr1X = tstr1.dual();

    TypeFunPtr tmul1E = TypeFunPtr.make(BitsFun.EMPTY,TypeStruct.make_args(TypeStruct.ts(Type.SCALAR,TypeStruct.NO_DISP,Type.NIL,Type.NIL))); // All bad choices

    assert tadd1X.isa(tnum1X) && tnum1X.isa(tflt1X) && tflt1X.isa(tnum1) && tnum1.isa(tadd1);


    // Check the fptr {int,flt} meet
    call.set_fun(ins[2]=fp_mul,gvn);
    TypeTuple[] argss_mul1 = new TypeTuple[] {                 // arg1  arg2   resolve
      TypeTuple.make( tctl, tfull, tmul1, txscl, txscl, tmul1X), //  ~S    ~S   [+int+flt] ;          high
      TypeTuple.make( tctl, tfull, tmul1, t2   , txscl, tmul1X), //   2    ~S   [+int+flt] ;     good+high
      TypeTuple.make( tctl, tfull, tmul1, t2   , t3   , tmul1 ), //   2     3   [ int,flt] ;     good
      TypeTuple.make( tctl, tfull, tmul1, t2   , tscl , tmul1 ), //   2     S   [ int,flt] ; low+good
      TypeTuple.make( tctl, tfull, tmul1, tscl , tscl , tmul1 ), //   S     S   [ int,flt] ; low
      TypeTuple.make( tctl, tfull, tmul1, txscl, tscl , tmul1 ), //  ~S     S   [ int,flt] ; low     +high
      TypeTuple.make( tctl, tfull, tmul1, txscl, tabc , tmul1X), //  ~S    str  [ int,flt] ; bad      high
      TypeTuple.make( tctl, tfull, tmul1, tabc , tabc , tmul1E), //  str   str  [        ] ; bad
      TypeTuple.make( tctl, tfull, tmul1, t2   , tabc , tmul1E), //   2    str  [ int,flt] ; bad+good
    };
    _testMonotonicChain(ins,call,argss_mul1);

    // Simple XCTRL check
    TypeTuple[] argss_mul1x = new TypeTuple[] {
      TypeTuple.make( txctl, tfull, tmul1, txscl, txscl, tmul1X), //  ~S    ~S   [+int+flt]
      TypeTuple.make( txctl, tfull, tmul1, t2   , txscl, tmul1X), //   2    ~S   [+int+flt]
      TypeTuple.make( txctl, tfull, tmul1, t2   , t3   , tmul1 ), //   2     3   [ int,flt]
      TypeTuple.make( txctl, tfull, tmul1, t2   , tscl , tmul1 ), //   2     S   [ int,flt]
      TypeTuple.make( txctl, tfull, tmul1, tscl , tscl , tmul1 ), //   S     S   [ int,flt]
      TypeTuple.make( txctl, tfull, tmul1, txscl, tabc , tmul1X), //  ~S    str  [ int,flt]
      TypeTuple.make( txctl, tfull, tmul1, t2   , tabc , tmul1E), //   2    str  [ int,flt]
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
      TypeTuple.make( tctl, tfull, tadd1, txscl, txscl, tadd1X), //  ~S    ~S   [+int+flt+str] (__H,__H,__H) ; All  high, keep all, join
      TypeTuple.make( tctl, tfull, tadd1, txscl, tabc , tadd1X), //  ~S    str  [+int+flt+str] (B_H,B_H,_GH) ; Some high, keep all, join
      TypeTuple.make( tctl, tfull, tadd1, txscl, tscl , tadd1 ), //  ~S     S   [ int,flt,str] (L_H,L_H,L_H) ; Mix H/L no Good, fidx/meet
      TypeTuple.make( tctl, tfull, tadd1, tnil , txscl, tadd1X), //   0    ~S   [+int+flt+str] (_GH,_GH,_GH) ; Some high, keep all, join
      TypeTuple.make( tctl, tfull, tadd1, tnil , t3   , tnum1 ), //   0     3   [ int,flt    ] (_G_,_G_,BG_) ; Some good, drop bad, fidx/meet
      TypeTuple.make( tctl, tfull, tadd1, tnil , tabc , tstr1 ), //   0    str  [         str] (BG_,BG_,_G_) ; Some good, drop bad, fidx/meet
      TypeTuple.make( tctl, tfull, tadd1, tnil , tscl , tadd1 ), //   0     S   [ int,flt,str] (LG_,LG_,LG_) ; Some low , keep all, meet
      TypeTuple.make( tctl, tfull, tadd1, t2   , txscl, tadd1X), //   2    ~S   [+int+flt+str] (_GH,_GH,B_H) ; Some high, keep all, join
      TypeTuple.make( tctl, tfull, tadd1, t2   , t3   , tnum1 ), //   2     3   [ int,flt    ] (_G_,_G_,B__) ; Some good, drop bad, fidx/meet
      TypeTuple.make( tctl, tfull, tadd1, t2   , tabc , tmul1E), //   2    str  [ int,flt,str] (BG_,BG_,BG_) ; All  bad , keep all, meet
      TypeTuple.make( tctl, tfull, tadd1, t2   , tscl , tadd1 ), //   2     S   [ int,flt,str] (LG_,LG_,B__) ; Some low , keep all, meet
      TypeTuple.make( tctl, tfull, tadd1, tabc , tabc , tstr1 ), //  str   str  [         str] (B__,B__,_G_) ; Some good, drop bad, fidx/meet
      TypeTuple.make( tctl, tfull, tadd1, tscl , tscl , tadd1 ), //   S     S   [ int,flt,str] (L__,L__,L__) ; All  low , keep all, meet
    };
    _testMonotonicChain(ins,call,argss_add1);


    // gcp(), not iter().  Types always lower.  Very high types might lower to be
    // valid, but e.g. a 2:int will never lower to a str.
    gvn._opt_mode=2;

    // The various kinds of results we expect
    TypeFunPtr tmul2X = v(fp_mul,gvn), tmul2 = tmul2X.dual();
    TypeFunPtr tadd2X = v(fp_add,gvn), tadd2 = tadd2X.dual();

    TypeFunPtr tnum2X = v(anum,gvn), tnum2 = tnum2X.dual();
    TypeFunPtr tflt2  = v(aflt,gvn), tflt2X= tflt2 .dual();
    TypeFunPtr tint2  = v(aint,gvn), tint2X= tint2 .dual();
    TypeFunPtr tstr2  = v(astr,gvn), tstr2X= tstr2 .dual();

    TypeFunPtr tmul2E = TypeFunPtr.make(BitsFun.EMPTY,TypeStruct.make_args(TypeStruct.ts(Type.SCALAR,TypeStruct.NO_DISP,Type.NIL,Type.NIL))); // All bad choices

    assert tadd2X.isa(tnum2X) && tnum2X.isa(tflt2X) && tflt2X.isa(tnum2) && tnum2.isa(tadd2);


    // Check the fptr {+int+flt} choices
    call.set_fun(ins[2]=fp_mul,gvn);
    TypeTuple[] argss_mul2 = new TypeTuple[] {                  // arg2  arg2   resolve
      TypeTuple.make( tctl, tfull, tmul2X, txscl, txscl, tmul2X), //  ~S    ~S   [+int+flt]
      TypeTuple.make( tctl, tfull, tmul2X, t2   , txscl, tmul2X), //   2    ~S   [+int+flt]
      TypeTuple.make( tctl, tfull, tmul2X, t2   , t3   , tmul2X), //   2     3   [ int,flt]
      TypeTuple.make( tctl, tfull, tmul2X, t2   , tscl , tmul2 ), //   2     S   [ int,flt]
      TypeTuple.make( tctl, tfull, tmul2X, tscl , tscl , tmul2 ), //   S     S   [ int,flt]
      TypeTuple.make( tctl, tfull, tmul2X, txscl, tscl , tmul2X), //  ~S     S   [ int,flt]
      TypeTuple.make( tctl, tfull, tmul2X, txscl, tabc , tmul2X), //  ~S    str  [ int,flt]
      TypeTuple.make( tctl, tfull, tmul2X, t2   , tabc , tmul2E), //   2    str  [ int,flt]
    };
    _testMonotonicChain(ins,call,argss_mul2);

    // Simple XCTRL check
    TypeTuple[] argss_mul2x = new TypeTuple[] {
      TypeTuple.make( txctl, tfull, tmul2X, txscl, txscl, tmul2X), //  ~S    ~S   [+int+flt]
      TypeTuple.make( txctl, tfull, tmul2X, t2   , txscl, tmul2X), //   2    ~S   [+int+flt]
      TypeTuple.make( txctl, tfull, tmul2X, t2   , t3   , tmul2X), //   2     3   [ int,flt]
      TypeTuple.make( txctl, tfull, tmul2X, t2   , tscl , tmul2 ), //   2     S   [ int,flt]
      TypeTuple.make( txctl, tfull, tmul2X, tscl , tscl , tmul2 ), //   S     S   [ int,flt]
      TypeTuple.make( txctl, tfull, tmul2X, txscl, tabc , tmul2X), //  ~S    str  [ int,flt]
      TypeTuple.make( txctl, tfull, tmul2X, t2   , tabc , tmul2E), //   2    str  [ int,flt]
    };
    _testMonotonicChain(ins,call,argss_mul2x);

    // Check the {+int+flt+str} choices
    call.set_fun(ins[2]=fp_add,gvn);
    TypeTuple[] argss_add2 = new TypeTuple[] {
      TypeTuple.make( tctl, tfull, tadd2X, txscl, txscl, tadd2X), //  ~S    ~S   [+int+flt+str] (__H,__H,__H) ; All  high, keep all, join
      TypeTuple.make( tctl, tfull, tadd2X, txscl, tabc , tadd2X), //  ~S    str  [+int+flt+str] (B_H,B_H,_GH) ; Some high, keep all, join
      TypeTuple.make( tctl, tfull, tadd2X, txscl, tscl , tadd2X), //  ~S     S   [+int+flt+str] (L_H,L_H,L_H) ; Mix H/L, no good, keep all, fidx/join
      TypeTuple.make( tctl, tfull, tadd2X, tnil , txscl, tadd2X), //   0    ~S   [+int+flt+str] (_GH,_GH,_GH) ; Some high, keep all, join
      TypeTuple.make( tctl, tfull, tadd2X, tnil , t3   , tnum2X), //   0     3   [+int+flt    ] (_G_,_G_,BG_) ; Some good, drop bad, fidx/join
      TypeTuple.make( tctl, tfull, tadd2X, tnil , tabc , tstr2X), //   0    str  [        ~str] (BG_,BG_,_G_) ; Some good, drop bad, fidx/join
      TypeTuple.make( tctl, tfull, tadd2X, tnil , tscl , tadd2 ), //   0     S   [ int,flt,str] (LG_,LG_,LG_) ; Some low , keep all, meet
      TypeTuple.make( tctl, tfull, tadd2X, t2   , txscl, tadd2X), //   2    ~S   [+int+flt+str] (_GH,_GH,B_H) ; Some high, keep all, join
      TypeTuple.make( tctl, tfull, tadd2X, t2   , t3   , tnum2X), //   2     3   [+int+flt    ] (_G_,_G_,B__) ; Some good, drop bad, fidx/join
      TypeTuple.make( tctl, tfull, tadd2X, t2   , tabc , tmul2E), //   2    str  [ int,flt,str] (BG_,BG_,BG_) ; All  bad , keep all, meet
      TypeTuple.make( tctl, tfull, tadd2X, t2   , tscl , tadd2 ), //   2     S   [ int,flt,str] (LG_,LG_,B__) ; Some low , keep all, meet
      TypeTuple.make( tctl, tfull, tadd2X, tabc , tabc , tstr2X), //  str   str  [        ~str] (B__,B__,_G_) ; Some good, drop bad, fidx/join
      TypeTuple.make( tctl, tfull, tadd2X, tscl , tscl , tadd2 ), //   S     S   [ int,flt,str] (L__,L__,L__) ; All  low , keep all, meet
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
    NewObjNode dsp_file = (NewObjNode)gvn.xform(new NewObjNode(true,TypeStruct.DISPLAY,ctl,dsp_prims));
    OProjNode dsp_file_obj = (OProjNode)gvn.xform(new OProjNode(dsp_file,0));
    ProjNode  dsp_file_ptr = ( ProjNode)gvn.xform(new  ProjNode(dsp_file,1));
    MemMergeNode dsp_merge = gvn.init(new MemMergeNode(mem,dsp_file_obj,dsp_file._alias));
    // The Fun and Fun._tf:
    Type[] args = TypeAry.get(3);
    args[0] = Type.SCALAR;            // Return
    args[1] = gvn.type(dsp_file_ptr).dual(); // File-scope display as arg0
    args[2] = Type.SCALAR;            // Some scalar arg1
    TypeFunPtr tf = TypeFunPtr.make_new(TypeStruct.make_args(new String[]{"->","^","x"},args));
    FunNode fun = new FunNode("fact",tf,BitsAlias.make0(dsp_file._alias));
    gvn.init(fun.add_def(ctl).add_def(ctl));
    // Parms for the Fun.  Note that the default type is "weak" because the
    // file-level display can not yet know about "fact".
    ParmNode parm_mem = new ParmNode(-2,"mem",fun,mem,null);
    ParmNode parm_dsp = new ParmNode( 0,"^"  ,fun,Type.SCALAR,dsp_file_ptr,null);
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
