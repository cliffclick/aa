package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.*;
import org.junit.Ignore;
import org.junit.Test;

import java.util.HashMap;
import java.util.Set;

import static com.cliffc.aa.AA.*;
import static com.cliffc.aa.type.TypeFld.Access;
import static com.cliffc.aa.type.TypeMemPtr.NO_DISP;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class TestNodeSmall {

  @Ignore  /* Ignored since changing call resolution strategy */
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

    Node uadd = Env.TOP.lookup("_+_"); // {int int -> int} and {flt flt -> flt} and {str str -> str}
    FunPtrNode aflt = (FunPtrNode)uadd.in(0);
    FunPtrNode aint = (FunPtrNode)uadd.in(1);
    FunPtrNode astr = (FunPtrNode)uadd.in(2);
    // Make a flt/int combo, drops off string.
    //Node anum = (UnresolvedNode)gvn.xform(new UnresolvedNode(null,aflt,aint));
    Node anum = null; // TODO

    // All nodes have this property: START >= {ALL.dual(),value(START)} >= value(ALL.dual()) >= value(ALL) >= ALL
    // Holds for both ITER and GCP.


    // Compute Node.all_type() and all_type.startype()
    Type uaddALL = uadd._val, uaddSTART = Type.ANY;
    Type anumALL = anum._val, anumSTART = Type.ANY;
    Type afltALL = aflt._val, afltSTART = Type.ANY;
    Type aintALL = aint._val, aintSTART = Type.ANY;
    Type astrALL = astr._val, astrSTART = Type.ANY;

    // Compute Node.value() where initial GVN is startype()
    uadd._val = uaddSTART;
    anum._val = anumSTART;
    aflt._val = afltSTART;
    aint._val = aintSTART;
    astr._val = astrSTART;
    Type uaddVAL1START = uadd.value();
    Type anumVAL1START = anum.value();
    Type afltVAL1START = aflt.value();
    Type aintVAL1START = aint.value();
    Type astrVAL1START = astr.value();
    Type uaddVAL2START = uadd.value();
    Type anumVAL2START = anum.value();
    Type afltVAL2START = aflt.value();
    Type aintVAL2START = aint.value();
    Type astrVAL2START = astr.value();

    // Compute Node.value() where initial GVN is all_type.dual()
    uadd._val = uaddALL.dual();
    anum._val = anumALL.dual();
    aflt._val = afltALL.dual();
    aint._val = aintALL.dual();
    astr._val = astrALL.dual();
    Type uaddVAL1XALL = uadd.value();
    Type anumVAL1XALL = anum.value();
    Type afltVAL1XALL = aflt.value();
    Type aintVAL1XALL = aint.value();
    Type astrVAL1XALL = astr.value();
    Type uaddVAL2XALL = uadd.value();
    Type anumVAL2XALL = anum.value();
    Type afltVAL2XALL = aflt.value();
    Type aintVAL2XALL = aint.value();
    Type astrVAL2XALL = astr.value();

    // Compute Node.value() where initial GVN is all_type()
    uadd._val = uaddALL;
    anum._val = uaddALL;
    aflt._val = afltALL;
    aint._val = aintALL;
    astr._val = astrALL;
    Type uaddVAL1ALL = uadd.value();
    Type anumVAL1ALL = anum.value();
    Type afltVAL1ALL = aflt.value();
    Type aintVAL1ALL = aint.value();
    Type astrVAL1ALL = astr.value();
    Type uaddVAL2ALL = uadd.value();
    Type anumVAL2ALL = anum.value();
    Type afltVAL2ALL = aflt.value();
    Type aintVAL2ALL = aint.value();
    Type astrVAL2ALL = astr.value();

    Type[] uadds = new Type[]{uaddSTART,uaddALL.dual(),uaddVAL1START,uaddVAL2START,uaddVAL1XALL,uaddVAL2XALL,uaddVAL1ALL,uaddVAL2ALL,uaddALL};
    Type[] anums = new Type[]{anumSTART,anumALL.dual(),anumVAL1START,anumVAL2START,anumVAL1XALL,anumVAL2XALL,anumVAL1ALL,anumVAL2ALL,anumALL};
    Type[] aflts = new Type[]{afltSTART,afltALL.dual(),afltVAL1START,afltVAL2START,afltVAL1XALL,afltVAL2XALL,afltVAL1ALL,afltVAL2ALL,afltALL};
    Type[] aints = new Type[]{aintSTART,aintALL.dual(),aintVAL1START,aintVAL2START,aintVAL1XALL,aintVAL2XALL,aintVAL1ALL,aintVAL2ALL,aintALL};
    Type[] astrs = new Type[]{astrSTART,astrALL.dual(),astrVAL1START,astrVAL2START,astrVAL1XALL,astrVAL2XALL,astrVAL1ALL,astrVAL2ALL,astrALL};
    Type[][] tfpss = new Type[][]{aflts,aints,astrs,anums,uadds};

    // All nodes have these properties:
    //    START >= {ALL.dual(),value1(START)} >= value1(ALL.dual()) >= value1(ALL) >= ALL
    //    START >= {ALL.dual(),value2(START)} >= value2(ALL.dual()) >= value2(ALL) >= ALL
    for( Type[] tfps : tfpss ) {
      Type start = tfps[0], xall  = tfps[1], val1s = tfps[2], val2s = tfps[3];
      Type val1x = tfps[4], val2x = tfps[5], val1a = tfps[6], val2a = tfps[7];
      Type all   = tfps[8];

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
    // is also 'isa'.  To allow the tests in any order, we check a slightly
    // strong condition: if all tuples are isa IN SOME ORDER, then the result
    // is also 'isa' IN THAT ORDER.
    int len = argss.length;
    int num = argss[0]._ts.length;
    for( int i=0; i<len; i++ ) {
      TypeTuple tti = argss[i];
      int order=0;              // no order picked
      midloop:
      for( int j=i+1; j<len; j++ ) { // Triangulate
        TypeTuple ttj = argss[j];
        for( int k=0; k<num-1; k++ ) { // Check all parts are 'isa', except the answer
          Type ttik = tti.at(k);
          Type ttjk = ttj.at(k);
          if( ttik==ttjk ) continue;      // Does not affect outcome
          if(      ttik.isa(ttjk) ) order |= 1;// i isa j
          else if( ttjk.isa(ttik) ) order |= 2;// j isa i
          else order |= 3; // Unordered
          if( order==3 )  continue midloop; // Mixed/unordered
        }
        assert order==1 || order==2;
        Type ttiN = tti.at(num-1); // Then check last answer element is 'isa'
        Type ttjN = ttj.at(num-1);
        if( order==1 ) assertTrue("Test is broken: "+tti+" isa "+ttj+", but "+ttiN+" !isa "+ttjN,ttiN.isa(ttjN));
        else           assertTrue("Test is broken: "+ttj+" isa "+tti+", but "+ttjN+" !isa "+ttiN,ttjN.isa(ttiN));
      }
    }


    // Now call Node.value()
    TypeTuple[] tns= new TypeTuple[argss.length];
    for( int i=0; i<argss.length; i++ ) {
      for( int j=0; j<ins.length; j++ )
        ins[j]._val = argss[i].at(j);
      tns[i] = (TypeTuple)n.value();
    }
    // Equals check after computing them all
    for( int i=0; i<argss.length; i++ ) {
      TypeFunPtr expect = (TypeFunPtr)argss[i].at(ins.length);
      TypeFunPtr actual = CallNode.ttfp(tns[i]); // Looking at the TFP from the Call, ignore ctrl,memory,args
      assertEquals("Expect "+expect+", but actual is "+actual+", for ("+argss[i].at(3)+", "+argss[i].at(4)+")",
                   expect.fidxs(),actual.fidxs());
    }
    return tns;
  }


  private static TypeFunPtr v(Node n, GVNGCM gvn) { return (TypeFunPtr)n.value(); }

  /** Validate monotonicity of CallNode.resolve().  There are only a couple of
   *  interesting variants; this test also tests e.g. XCTRL for correctness but
   *  its implementation is a simple cutout, same for the display arg "^" being
   *  NO_DISP.
   *
   *  === High mul fptr (e.g. GCP) ===
   *  arg1  arg2    fptr*      resolve
   *   ~S    ~S   [~int+flt]  [~int+flt]   Choices all around
   *    2    ~S   [~int+flt]  [~int+flt]   Choices all around; arg2 can fall to e.g. 3 or 3.14
   *    2     3   [~int+flt]  [~int+flt]   Valid to cutout flt or allow (least_cost will resolve)
   *    2     I   [~int+flt]  [ int    ]   Only int
   *    2     F   [~int+flt]  [     flt]   Only flt
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
  @Ignore  /* Ignored since changing call resolution strategy */
  @Test public void testCallNodeResolve() {
    GVNGCM gvn = Env.GVN;

    // Make a Unknown/CallNode/CallEpi combo.
    // Unwired.  Validate the resolve process and monotonicity.
    ConNode ctrl = (ConNode) gvn.xform(new ConNode<>(Type.CTRL));
    Node fp_mul = Env.TOP.lookup("*"); // {int int -> int} and {flt flt -> flt}
    FunPtrNode mflt = (FunPtrNode)fp_mul.in(0);
    FunPtrNode mint = (FunPtrNode)fp_mul.in(1);
    Node fp_add = Env.TOP.lookup("+"); // {int int -> int} and {flt flt -> flt} and {str str -> str}
    FunPtrNode aflt = (FunPtrNode)fp_add.in(0);
    FunPtrNode aint = (FunPtrNode)fp_add.in(1);
    FunPtrNode astr = (FunPtrNode)fp_add.in(2);
    // Make a flt/int combo, drops off string.
    ConNode mem  = gvn.init(new ConNode<>(TypeMem.ALLMEM));
    ConNode arg1 = gvn.init(new ConNode<>(TypeNil.SCALAR));
    ConNode arg2 = gvn.init(new ConNode<>(TypeNil.SCALAR));
    Node dsp = gvn.xform(new ConNode<>(TypeMemPtr.NO_DISP));
    CallNode call = (CallNode)gvn.xform(new CallNode(true, null, ctrl, mem, dsp, arg1, arg2, fp_mul));
    CallEpiNode cepi = (CallEpiNode)gvn.xform(new CallEpiNode(call)); // Unwired

    call.unelock();             // Will be hacking edges
    Node[] ins = new Node[]{ctrl,mem,fp_mul,arg1,arg2};

    // Args to calls
    Type tctl = Type.CTRL, txctl = Type.XCTRL;
    Type tscl = TypeNil.SCALAR, txscl = TypeNil.XSCALAR;
    Type tnil = TypeNil.NIL;
    TypeMem tfull = TypeMem.ALLMEM;
    Type t2 = TypeInt.con(2);   // Small ints are ambiguously either ints or floats
    Type t3 = TypeInt.con(3);
    Type tint=TypeInt.INT64;
    Type tflt=TypeFlt.FLT64;
    //Type tabc=TypeMemPtr.ABCPTR.simple_ptr();

    // iter(), not gcp().  Types always rise.  Very low types might lift to be
    // valid, but e.g. a 2:int will never lift to a str.

    // The various kinds of results we expect
    TypeFunPtr tmul1 = v(fp_mul,gvn), tmul1X = tmul1.dual();
    TypeFunPtr tadd1 = v(fp_add,gvn), tadd1X = tadd1.dual();

    //UnresolvedNode anum = gvn.init(new UnresolvedNode(null,aflt,aint));
    Node anum = null; // TODO
    TypeFunPtr tnum1 = v(anum,gvn), tnum1X = tnum1.dual();
    TypeFunPtr tflt1 = v(aflt,gvn), tflt1X = tflt1.dual();
    TypeFunPtr tint1 = v(aint,gvn), tint1X = tint1.dual();
    TypeFunPtr tstr1 = v(astr,gvn), tstr1X = tstr1.dual();
    TypeFunPtr tmint = v(mint,gvn), tmintX = tmint.dual();
    TypeFunPtr tmflt = v(mflt,gvn), tmfltX = tmflt.dual();

    TypeFunPtr tmul1E = TypeFunPtr.make(false,BitsFun.EMPTY,0,NO_DISP,null); // All bad choices

    assert tadd1X.isa(tnum1X) && tnum1X.isa(tflt1X) && tflt1X.isa(tnum1) && tnum1.isa(tadd1);

    // Check the fptr {int,flt} meet
    call.set_fdx(ins[2]=fp_mul);
    TypeTuple[] argss_mul1 = new TypeTuple[] {                   // arg1  arg2   resolve
      TypeTuple.make( tctl, tfull, tmul1, txscl, txscl, tmul1X), //  ~S    ~S   [+int+flt] ;          high
      TypeTuple.make( tctl, tfull, tmul1, t2   , txscl, tmul1X), //   2    ~S   [+int+flt] ;     good+high
      TypeTuple.make( tctl, tfull, tmul1, t2   , t3   , tmul1X), //   2     3   [+int+flt] ;     good, requires 'least cost' to resolve
      TypeTuple.make( tctl, tfull, tmul1, t2   , tint , tmintX), //   2     I   [+int    ] ;     good
      TypeTuple.make( tctl, tfull, tmul1, t2   , tflt , tmfltX), //   2     F   [    +flt] ;     good
      TypeTuple.make( tctl, tfull, tmul1, t2   , tscl , tmul1 ), //   2     S   [ int,flt] ; low+good
      TypeTuple.make( tctl, tfull, tmul1, tscl , tscl , tmul1 ), //   S     S   [ int,flt] ; low
      TypeTuple.make( tctl, tfull, tmul1, txscl, tscl , tmul1 ), //  ~S     S   [ int,flt] ; low     +high
      //TypeTuple.make( tctl, tfull, tmul1, txscl, tabc , tmul1X), //  ~S    str  [+int+flt] ; bad      high
      //TypeTuple.make( tctl, tfull, tmul1, tabc , tabc , tmul1 ), //  str   str  [        ] ; bad
      //TypeTuple.make( tctl, tfull, tmul1, t2   , tabc , tmul1 ), //   2    str  [+int+flt] ; bad+good
    };
    _testMonotonicChain(ins,call,argss_mul1);

    // Check the {int,flt,str} meet.
    // Rules:
    // - Some args High & no Low, keep all & join (ignore Good,Bad)
    // - Some args Low & no High, keep all & meet (ignore Good,Bad)
    // - Mix High/Low & no Good , keep all & fidx?join:meet
    // - Some Good, no Low, no High, drop Bad & fidx?join:meet
    // - All Bad, like Low: keep all & meet
    call.set_fdx(ins[2]=fp_add);
    TypeTuple[] argss_add1 = new TypeTuple[] {
      TypeTuple.make( tctl, tfull, tadd1, txscl, txscl, tadd1X), //  ~S    ~S   [+int+flt+str] (__H,__H,__H) ; All  high, keep all, join
      //TypeTuple.make( tctl, tfull, tadd1, txscl, tabc , tadd1X), //  ~S    str  [+int+flt+str] (B_H,B_H,_GH) ; Some high, keep all, join
      TypeTuple.make( tctl, tfull, tadd1, txscl, tscl , tadd1 ), //  ~S     S   [ int,flt,str] (L_H,L_H,L_H) ; Mix H/L no Good, fidx/meet
      TypeTuple.make( tctl, tfull, tadd1, tnil , txscl, tadd1X), //   0    ~S   [+int+flt+str] (_GH,_GH,_GH) ; Some high, keep all, join
      TypeTuple.make( tctl, tfull, tadd1, tnil , t3   , tnum1X), //   0     3   [+int+flt    ] (_G_,_G_,BG_) ; Some good, drop bad, fidx/meet
      //TypeTuple.make( tctl, tfull, tadd1, tnil , tabc , tstr1X), //   0    str  [        +str] (BG_,BG_,_G_) ; Some good, drop bad, fidx/meet
      TypeTuple.make( tctl, tfull, tadd1, tnil , tint , tint1X), //   0     3   [+int        ] (_G_,_G_,_G_) ; All good
      TypeTuple.make( tctl, tfull, tadd1, tnil , tscl , tadd1 ), //   0     S   [ int,flt,str] (LG_,LG_,LG_) ; Some low , keep all, meet
      TypeTuple.make( tctl, tfull, tadd1, t2   , txscl, tadd1X), //   2    ~S   [+int+flt+str] (_GH,_GH,B_H) ; Some high, keep all, join
      TypeTuple.make( tctl, tfull, tadd1, t2   , t3   , tnum1X), //   2     3   [+int+flt    ] (_G_,_G_,B__) ; Some good, drop bad, fidx/meet
      //TypeTuple.make( tctl, tfull, tadd1, t2   , tabc , tadd1 ), //   2    str  [ int,flt,str] (BG_,BG_,BG_) ; All  bad , keep all, meet
      TypeTuple.make( tctl, tfull, tadd1, t2   , tscl , tadd1 ), //   2     S   [ int,flt,str] (LG_,LG_,B__) ; Some low , keep all, meet
      //TypeTuple.make( tctl, tfull, tadd1, tabc , tabc , tstr1X), //  str   str  [        +str] (B__,B__,_G_) ; Some good, drop bad, fidx/meet
      TypeTuple.make( tctl, tfull, tadd1, tscl , tscl , tadd1 ), //   S     S   [ int,flt,str] (L__,L__,L__) ; All  low , keep all, meet
    };
    _testMonotonicChain(ins,call,argss_add1);


    // gcp(), not iter().  Types always lower.  Very high types might lower to be
    // valid, but e.g. a 2:int will never lower to a str.

    // The various kinds of results we expect
    TypeFunPtr tmul2X = v(fp_mul,gvn), tmul2 = tmul2X.dual();
    TypeFunPtr tadd2X = v(fp_add,gvn), tadd2 = tadd2X.dual();

    TypeFunPtr tnum2X = v(anum,gvn), tnum2 = tnum2X.dual();
    TypeFunPtr tflt2  = v(aflt,gvn), tflt2X= tflt2 .dual();
    TypeFunPtr tint2  = v(aint,gvn), tint2X= tint2 .dual();
    TypeFunPtr tstr2  = v(astr,gvn), tstr2X= tstr2 .dual();

    assert tadd2X.isa(tnum2X) && tnum2X.isa(tflt2X) && tflt2X.isa(tnum2) && tnum2.isa(tadd2);


    // Check the fptr {+int+flt} choices
    call.set_fdx(ins[2]=fp_mul);
    TypeTuple[] argss_mul2 = new TypeTuple[] {                  // arg2  arg2   resolve
      TypeTuple.make( tctl, tfull, tmul2X, txscl, txscl, tmul2X), //  ~S    ~S   [+int+flt]
      TypeTuple.make( tctl, tfull, tmul2X, t2   , txscl, tmul2X), //   2    ~S   [+int+flt]
      TypeTuple.make( tctl, tfull, tmul2X, t2   , t3   , tmul2X), //   2     3   [ int,flt]
      TypeTuple.make( tctl, tfull, tmul2X, t2   , tscl , tmul2 ), //   2     S   [ int,flt]
      TypeTuple.make( tctl, tfull, tmul2X, tscl , tscl , tmul2 ), //   S     S   [ int,flt]
      TypeTuple.make( tctl, tfull, tmul2X, txscl, tscl , tmul2X), //  ~S     S   [ int,flt]
      //TypeTuple.make( tctl, tfull, tmul2X, txscl, tabc , tmul2X), //  ~S    str  [ int,flt]
      //TypeTuple.make( tctl, tfull, tmul2X, t2   , tabc , tmul2 ), //   2    str  [ int,flt]
    };
    _testMonotonicChain(ins,call,argss_mul2);

    // Check the {+int+flt+str} choices
    call.set_fdx(ins[2]=fp_add);
    TypeTuple[] argss_add2 = new TypeTuple[] {
      TypeTuple.make( tctl, tfull, tadd2X, txscl, txscl, tadd2X), //  ~S    ~S   [+int+flt+str] (__H,__H,__H) ; All  high, keep all, join
      //TypeTuple.make( tctl, tfull, tadd2X, txscl, tabc , tadd2X), //  ~S    str  [+int+flt+str] (B_H,B_H,_GH) ; Some high, keep all, join
      TypeTuple.make( tctl, tfull, tadd2X, txscl, tscl , tadd2X), //  ~S     S   [+int+flt+str] (L_H,L_H,L_H) ; Mix H/L, no good, keep all, fidx/join
      TypeTuple.make( tctl, tfull, tadd2X, tnil , txscl, tadd2X), //   0    ~S   [+int+flt+str] (_GH,_GH,_GH) ; Some high, keep all, join
      TypeTuple.make( tctl, tfull, tadd2X, tnil , t3   , tnum2X), //   0     3   [+int+flt    ] (_G_,_G_,BG_) ; Some good, drop bad, fidx/join
      //TypeTuple.make( tctl, tfull, tadd2X, tnil , tabc , tstr2X), //   0    str  [        +str] (BG_,BG_,_G_) ; Some good, drop bad, fidx/join
      TypeTuple.make( tctl, tfull, tadd2X, tnil , tscl , tadd2 ), //   0     S   [ int,flt,str] (LG_,LG_,LG_) ; Some low , keep all, meet
      TypeTuple.make( tctl, tfull, tadd2X, t2   , txscl, tadd2X), //   2    ~S   [+int+flt+str] (_GH,_GH,B_H) ; Some high, keep all, join
      TypeTuple.make( tctl, tfull, tadd2X, t2   , t3   , tnum2X), //   2     3   [+int+flt    ] (_G_,_G_,B__) ; Some good, drop bad, fidx/join
      //TypeTuple.make( tctl, tfull, tadd2X, t2   , tabc , tadd2 ), //   2    str  [ int,flt,str] (BG_,BG_,BG_) ; All  bad , keep all, meet
      TypeTuple.make( tctl, tfull, tadd2X, t2   , tscl , tadd2 ), //   2     S   [ int,flt,str] (LG_,LG_,B__) ; Some low , keep all, meet
      //TypeTuple.make( tctl, tfull, tadd2X, tabc , tabc , tstr2X), //  str   str  [        +str] (B__,B__,_G_) ; Some good, drop bad, fidx/join
      TypeTuple.make( tctl, tfull, tadd2X, tscl , tscl , tadd2 ), //   S     S   [ int,flt,str] (L__,L__,L__) ; All  low , keep all, meet
    };
    _testMonotonicChain(ins,call,argss_add2);

    cepi.kill();
  }

  @Ignore /* Ignored since changing call resolution strategy */
  @Test public void testCallNodeResolve2() {
    GVNGCM gvn = Env.GVN;

    Node fp_add = Env.TOP.lookup("_+_"); // {int int -> int} and {flt flt -> flt} and {str str -> str}
    FunPtrNode aflt = (FunPtrNode)fp_add.in(0);
    FunPtrNode aint = (FunPtrNode)fp_add.in(1);
    FunPtrNode astr = (FunPtrNode)fp_add.in(2);

    // Make a Unknown/CallNode/CallEpi combo.  Unwired.
    ConNode ctrl = (ConNode)gvn.xform(new ConNode<>(Type.CTRL));
    ConNode mem  = (ConNode)gvn.xform(new ConNode<>(TypeMem.ALLMEM));
    ConNode dsp  = (ConNode)gvn.xform(new ConNode<>(TypeMemPtr.NO_DISP));
    ConNode arg3 = gvn.init(new ConNode<>(TypeNil.SCALAR));
    ConNode arg4 = gvn.init(new ConNode<>(TypeNil.SCALAR));
    ConNode fdx  = gvn.init(new ConNode<>(fp_add._val));
    CallNode call = gvn.init(new CallNode(true, null, ctrl, mem, dsp, arg3, arg4, fdx));
    CallEpiNode cepi = gvn.init(new CallEpiNode(call)); // Unwired

    // Types we see on inputs, choosen to walk across the sample space
    Type i32 = TypeInt.INT32;   // Subsets both int64 and flt64
    Type i64 = TypeInt.INT64;
    Type f64 = TypeFlt.FLT64;
    Type scl = TypeNil.SCALAR;
    //Type abc = TypeMemPtr.ABCPTR.simple_ptr(); // Constant string
    Type tup = TypeMemPtr.ISUSED.simple_ptr(); // Tuple pointer (always wrong)
    // All args, including duals
    Type[] targs = new Type[]{i64,i64.dual(),
                              f64,f64.dual(),
                              scl,scl.dual(),
                              //abc,abc.dual(),
                              //i32,i32.dual(),
                              //tup,tup.dual(),
    };
    // Functions we see, in all combos
    Type fint = aint._val;
    Type fflt = aflt._val;
    Type fstr = astr._val;
    Type fif_ = fint.meet(fflt);
    Type f_fs = fstr.meet(fflt);
    Type fi_s = fstr.meet(fint);
    Type fifs = fint.meet(fflt).meet(fstr);
    // All FDXS, including duals
    Type[] tfdxs = new Type[]{fint,fint.dual(),fflt,fflt.dual(),fstr,fstr.dual(),
                              fif_,fif_.dual(),f_fs,f_fs.dual(),
                              fi_s,fi_s.dual(),fifs,fifs.dual(),};

    // Pre-compute them all
    HashMap<TypeTuple,Type> cvals = new HashMap<>();
    for( Type targ3 : targs ) {
      arg3._val = targ3;
      for( Type targ4 : targs ) {
        arg4._val = targ4;
        for( Type tfdx : tfdxs ) {
          fdx._val = tfdx;
          Type tcall = call.value();
          TypeTuple args = TypeTuple.make(targ3,targ4,tfdx);
          cvals.put(args,tcall);
        }
      }
    }

    // Verify ISA relation
    Set<TypeTuple> keys = cvals.keySet();
    for( TypeTuple key0 : keys )
      for( TypeTuple key1 : keys )
        if( key0.isa(key1) )
          assertTrue(cvals.get(key0).isa(cvals.get(key1)));

    Env.top_reset();                   // Hard reset
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

    // Build the graph for a simple recursive function display.
    // Struct (display); inputs are prior display and FunPtr
    // Fun (and Fun._tf) - Just default control and some other control
    //   Parm:^   - Default display
    //   Parm:mem - Default mem
    //   Parm:rpc - Default
    //   Ret - {Fun,Parm:mem,Parm:^} - Not really fact() nor gen_ctr() code but upwards exposed closure
    //   FunPtr - Ret
    ConNode ctl = new ConNode<>(Type.CTRL).init();
    ConNode mem = new ConNode<>(TypeMem.ANYMEM).init();
    ConNode rpc = new ConNode<>(TypeRPC.ALL_CALL).init();
    // The file-scope display closing the graph-cycle.  Needs the FunPtr, not
    // yet built.
    ConNode dsp_prims = new ConNode<>(TypeMemPtr.DISP_SIMPLE).init();
    StructNode dsp_file = new StructNode(true,false,null,"",Type.ALL).add_fld("^",Access.Final,dsp_prims,null).init();
    NewNode dsp_file_ptr = new NewNode().init();
    Node dsp_file_mem = new StoreNode(mem,dsp_file_ptr,dsp_file,null).init();
    // Function header with nargs
    FunNode fun = new FunNode("fact",ARG_IDX).add_def(ctl).add_def(ctl).init();
    // Parms for the Fun.  Note that the default type is "weak" because the
    // file-level display can not yet know about "fact".
    ParmNode parm_mem     = new ParmNode(MEM_IDX,fun,null,mem._val,mem).add_def(dsp_file_mem).init();
    ParmNode parm_dsp_ptr = new ParmNode(DSP_IDX,fun,null,dsp_file_ptr._val,(ConNode)Node.con(dsp_file_ptr._val)).add_def(dsp_file_ptr).init();
    // Close the function up
    RetNode ret = new RetNode(fun,parm_mem,parm_dsp_ptr,rpc,fun).init();
    FunPtrNode fptr = new FunPtrNode(ret).init();
    fptr._name = "fact";
    // Close the cycle
    dsp_file.add_fld("fact",Access.Final,fptr,null);
    dsp_file.close();
    // Return the fptr to keep all alive
    ScopeNode env = new ScopeNode(true,null,ctl,mem,fptr,dsp_file_ptr,dsp_file).init();

    Node[] nodes = new Node[]{ctl,mem,rpc,dsp_prims,dsp_file,dsp_file_ptr,dsp_file_mem,fun,parm_mem,parm_dsp_ptr,ret,fptr,env};

    // Validate graph initial conditions.  No optimizations, as this
    // pile-o-bits is all dead and will vaporize if the optimizer is turned
    // loose on it.  Just check the types flow correctly.
    for( Node n : nodes ) {
      Type old = n._val;
      Type nnn = n.value();
      assert nnn.isa(old);
    }

    // Now run GCP to closure.  This is the key call being tested.
    DO_GCP=true;
    DO_HMT=false;
    Combo.opto();

    // Validate cyclic display/function type
    TypeFunPtr tfptr0 = (TypeFunPtr) fptr._val;
    Type tdptr0 = tfptr0.dsp();
    Type tret = ((TypeTuple) ret._val).at(REZ_IDX);
    assertEquals(tdptr0,tret); // Returning the display
    // Display contains 'fact' pointing to self
    TypeMem tmem = (TypeMem) dsp_file_mem._val;
    TypeStruct tdisp0 = tmem.ld((TypeMemPtr)tdptr0);
    assertEquals(tfptr0,tdisp0.at("fact"));

    // Cleanup after test
    env.kill();
    dsp_file.pop();
    Env.top_reset();                   // Hard reset
  }


  // Memory checks args "just like" normal args, except it changes contents of
  // memory to match incoming args.
  //
  // Single bad ptr + memory, e.g. [13]->obj and [13:@{x==1,y==2}] but the
  // formal is [2:Point:@{x,y}].  Can change memory directly here (no sharing):
  // [13:Point:@{x,y}] and leave the ptr alone.
  //
  // Can also make a new fake alias: 13, change both ptr and mem:
  // *[14]->obj, [14:Point:@{x,y}].  If [13] lifts to some other refinement
  // alias, may need new fake aliases.  If [13] lifts to a refinement with a
  // valid memory, no need to change memory.
  //
  // Must be monotonic towards correctness, if there is any chance to lift (fall)
  // and be correct.  If always an error, can go sideways but still monotonic
  // on the side path.
  //
  // Have to figure out how to handle N busted ptrs, and N busted memories.
  // Either fake aliases for all, or union the incompatible types?  Begs for a
  // custom test: Fun, Parm:mem, Parm:x, Parm:y.  Outputs always within formal
  // bounds, and always monotonic, and preserves shape if in-bounds.

  private static int ERR=0;
  @Ignore /* Ignored since Parm correctness now from H-M and not from flow */
  @Test public void testMemoryArgs() {
    GVNGCM gvn = Env.GVN;

    // Check Parm.value calls are monotonic, and within Fun.sig bounds -
    // including memory args.

    // Build a bunch of aliases.
    int a1 = BitsAlias.new_alias();
    int a2 = BitsAlias.new_alias();
    int a3 = BitsAlias.new_alias();
    TypeFld fmem = TypeFld.make(" mem",TypeMem.ALLMEM,Access.Final);
    TypeFld fint = TypeFld.make_arg(TypeInt.INT64,ARG_IDX);
    //TypeStruct ts_int_flt = TypeStruct.make(fmem,fint,TypeFld.make_arg(TypeFlt.FLT64,ARG_IDX+1));
    //TypeStruct ts_int_abc = TypeStruct.make(fmem,fint,TypeFld.make_arg(TypeMemPtr.ISUSED,ARG_IDX+1));
    //// @{ a:int; b:"abc" }
    //TypeStruct a_int_b_abc = TypeStruct.make_test("a",TypeInt.INT64,"b",TypeMemPtr.ISUSED);
    //TypeStruct ts_flt_str = TypeStruct.make(fmem,TypeFld.make_arg(TypeFlt.FLT64,ARG_IDX),TypeFld.make_arg(TypeMemPtr.make(BitsAlias.ALLX,a_int_b_abc),ARG_IDX+1));
    //
    //// Build a bunch of function type signatures
    //TypeFunPtr[] sigs = new TypeFunPtr[] {
    //  TypeFunPtr.make_sig(ts_int_flt,TypeTuple.RET), // {int flt   -> }
    //  TypeFunPtr.make_sig(ts_int_abc,TypeTuple.RET), // {int "abc" -> }
    //  TypeFunPtr.make_sig(ts_flt_str,TypeTuple.RET), // { flt @{a:int; b:"abc"} -> }
    //};
    //
    //// Build a bunch of memory parm types
    //TypeMem[] mems = new TypeMem[] {
    //  tmem(null),
    //  tmem(null).dual(),
    //  tmem(new int[]{a2},TypeStruct.ISUSED),
    //  tmem(new int[]{a1},a_int_b_abc),
    //};
    //
    //// Build a bunch of parameter types
    //Type[] args = new Type[] {
    //  Type.NIL,
    //  Type.XNIL,
    //  TypeInt.INT64,
    //  TypeInt.INT64.dual(),
    //  TypeInt.NINT64,
    //  //TypeMemPtr.ABCPTR.simple_ptr(),
    //  //TypeMemPtr.ABCPTR.dual().simple_ptr(),
    //  TypeMemPtr.make(a1,TypeStruct.ISUSED).simple_ptr(),
    //  TypeMemPtr.make(a1,TypeStruct.ISUSED).dual().simple_ptr(),
    //};
    //
    //// One-off jig for testing single combo
    //// Known easy fail: 0,0,0,[6,5]
    //// Known easy fail: 2,1,0,[6,7]
    //// Known easy fail: 1,0,0,[8,5]
    //// Known easy fail: 2,[1,0],0,7
    //Type[] rez1 = check(gvn,sigs[2],mems[1],args[0],args[8]);
    //Type[] rez2 = check(gvn,sigs[2],mems[0],args[0],args[8]);
    //for( int k=0; k<rez1.length; k++ )
    //  assertTrue(rez1[k].isa(rez2[k]));
    //
    //
    //// Call for all combos.
    //// Check results are isa-sig.
    //Type[][][][][] rezs = new Type[sigs.length][mems.length][args.length][args.length][];
    //for( int is = 0; is<sigs.length; is++ )
    //  for( int im = 0; im<mems.length; im++ )
    //    for( int ia0 = 0; ia0<args.length; ia0++ )
    //      for( int ia1 = 0; ia1<args.length; ia1++ )
    //        rezs[is][im][ia0][ia1] = check(gvn,sigs[is],mems[im],args[ia0],args[ia1]);
    //
    //// Check results are monotonic:
    //for( int is = 0; is<sigs.length; is++ )
    //  for( int js = 0; js<sigs.length; js++ )
    //    if( sigs[is].isa(sigs[js]) )
    //      for( int im = 0; im<mems.length; im++ )
    //        for( int jm = 0; jm<mems.length; jm++ )
    //          if( mems[im].isa(mems[jm]) )
    //            for( int ia0 = 0; ia0<args.length; ia0++ )
    //              for( int ja0 = 0; ja0<args.length; ja0++ )
    //                if( args[ia0].isa(args[ja0]) )
    //                  for( int ia1 = 0; ia1<args.length; ia1++ )
    //                    for( int ja1 = 0; ja1<args.length; ja1++ )
    //                      if( args[ia1].isa(args[ja1]) ) {
    //                        Type[] rezi = rezs[is][im][ia0][ia1];
    //                        Type[] rezj = rezs[js][jm][ja0][ja1];
    //                        for( int k=0; k<rezi.length; k++ )
    //                          if( !rezi[k].isa(rezj[k]) )
    //                            perror("Not monotonic",rezi[k],rezj[k]);
    //                      }
    //assertEquals(0,ERR);
    throw unimpl();
  }

  // Check that the Parm.value calls for these incoming args are monotonic, and
  // within the sig bounds.
  private static Type[] check( GVNGCM gvn, TypeFunPtr tsig, TypeMem tmem, Type targ1, Type targ2 ) {
    assert targ1.simple_ptr()==targ1;
    assert targ2.simple_ptr()==targ2;
    ConNode ctl = gvn.init(new ConNode<>(Type.CTRL));
    ConNode cmem= (ConNode)gvn.xform(new ConNode<>(TypeMem.ALLMEM));
    CallNode call = gvn.init(new CallNode(true, null, ctl, cmem, null/*fidx*/, null/*x*/, null/*y*/));
    CallEpiNode cepi = gvn.init(new CallEpiNode(call)); // Unwired
    Node    cpj = gvn.init(new CProjNode(call,0));
    ConNode mem = gvn.init(new ConNode<>(tmem ));
    ConNode arg1= gvn.init(new ConNode<>(targ1));
    ConNode arg2= gvn.init(new ConNode<>(targ2));

    //// Make nodes
    //FunNode fun = new FunNode(null,-1).unkeep();
    //gvn.xform(fun.add_def(cpj.unkeep(2)));
    //
    //ParmNode parmem= gvn.init(new ParmNode(MEM_IDX," mem",fun,mem .unkeep(2),null)).unkeep(2);
    //ParmNode parm1 = gvn.init(new ParmNode(ARG_IDX,  "x" ,fun,arg1.unkeep(2),null)).unkeep(2);
    //ParmNode parm2 = gvn.init(new ParmNode(ARG_IDX+1,"y" ,fun,arg2.unkeep(2),null)).unkeep(2);
    //
    //// Types for normal args before memory type
    //Type tpm = parmem.xval();
    //Type tp1 = parm1 .xval();
    //Type tp2 = parm2 .xval();
    //
    //// Check the isa(sig) on complex pointer args
    //Type actual1 = tpm.sharptr(tp1);
    //Type formal1 = fun.formal(ARG_IDX);
    //if( !actual1.above_center() && !actual1.isa(formal1) && !formal1.isa(actual1) )
    //  perror("arg1-vs-formal1",actual1,formal1);
    //Type actual2 = tpm.sharptr(tp2);
    //Type formal2 = fun.formal(ARG_IDX+1);
    //if( !actual2.above_center() && !actual2.isa(formal2) && !formal2.isa(actual2) )
    //  perror("arg2-vs-formal2",actual2,formal2);
    //
    //// Clean up
    //cepi.unkeep().unhook();
    //parmem.kill();
    //parm1.kill();
    //parm2.kill();
    //Env.GVN.iter_dead();
    //
    //// Record for later monotonic check
    //return new Type[]{tpm,tp1,tp2};
    throw unimpl();
  }

  static void perror( String msg, Type t1, Type t2 ) {
    if( ERR < 10 )
      System.out.println(msg+", "+t1+" is not "+t2);
    ERR++;
  }


  // Helper to make memory
  private static TypeMem tmem(int[] as, TypeStruct... ts) {
    //int max = BitsAlias.AARY;
    //if( as !=null && as.length> 0 ) max = Math.max(max,as[as.length-1]);
    //TypeObj[] tos = new TypeObj[max+1];
    //tos[BitsAlias.ALL] = TypeObj.OBJ;
    //tos[BitsAlias.REC]=TypeStruct.ALLSTRUCT;
    //tos[BitsAlias.ABC] = TypeStr.ABC; //
    //tos[BitsAlias.STR] = TypeStr.STR;
    //tos[BitsAlias.AARY] = TypeAry.ARY;
    //if( as != null )
    //  for( int i=0; i<as.length; i++ )
    //    tos[as[i]] = ts[i];
    //return TypeMem.make0(tos);
    throw unimpl();
  }
}

