package com.cliffc.aa.type;

import com.cliffc.aa.Env;
import org.junit.Ignore;
import org.junit.Test;

import java.util.HashMap;

import static com.cliffc.aa.AA.ARG_IDX;
import static com.cliffc.aa.AA.DSP_IDX;
import static org.junit.Assert.*;


public class TestApprox {
  // temp/junk holder for "instant" junits, when debugged moved into other tests
  @Test public void testType() {
  }

  private TypeFld make(BitsFun fidxs,Type ret) { return TypeFld.make("pred",TypeFunPtr.make(fidxs,1,TypeMemPtr.NO_DISP,ret)); }
  @Test public void testApproxAssociative() {
    // Proof approx is not associative with meet.
    // E.g. A.approx.meet(B) != A.meet(B).approx
    // Simple case:

    // A     : *[7]@{ x = 3   ; fld = *[7]@{ x = "abc"; } }
    // B     : *[7]@{ x = 4   ; fld = ALL; }
    // A.X   : *[7]@{ x = SCLR; fld = ALL; }  // Approx meets 3&"abc"; also loses 'fld='
    // A.X.B : *[7]@{ x = SCLR; fld = ALL; }  // Weak field 'x'
    // A.B   : *[7]@{ x = nint; fld = ALL; }  // Better field 'x', still loses 'fld='
    // A.B.X : *[7]@{ x = nint; fld = ALL; }


    int a14 = BitsAlias.new_alias(BitsAlias.ALLX);
    BitsAlias ba14 = BitsAlias.make0(a14);
    BitsFun f25 = BitsFun.make_new_fidx(BitsFun.ALLX);
    TypeFld p0 = make(BitsFun.ALL,Type.SCALAR);
    TypeMemPtr ptr0 = TypeMemPtr.make(ba14,TypeStruct.make(p0));
    TypeFld p1 = make(f25,ptr0);
    TypeStruct tsa = TypeStruct.make(p1);
    TypeMemPtr ptra = TypeMemPtr.make(ba14,tsa);

    TypeFld pb = make(f25,Type.SCALAR);
    TypeStruct tsb = TypeStruct.make(pb);
    TypeMemPtr ptrb = TypeMemPtr.make(BitsAlias.EMPTY,tsb);

    TypeStruct ax  = tsa.approx1(1,ba14);
    TypeStruct axb = (TypeStruct)ax.meet(tsb);

    TypeStruct ab = (TypeStruct)tsa.meet(tsb);
    TypeStruct abx = ab.approx1(1,ba14);

    assertNotEquals(axb,abx); // Would like this to be equals!!!!
  }

  // Check TypeStruct.meet for a more complex recursive case
  @Test public void testTSMeet() {
    Object dummy = TypeMemPtr.TYPES; // <clinit> before RECURSIVE_MEET
    int alias0 = BitsAlias.new_alias(BitsAlias.ALLX);

    // Build two structs pointing to each other.
    //   -> [,int] -> * -> [,flt] -> * ->
    TypeFld fbint = TypeFld.make("b",TypeInt.INT64,TypeFld.oBot);
    TypeFld fbflt = TypeFld.make("b",TypeFlt.FLT64,TypeFld.oBot);
    Type.RECURSIVE_MEET++;
    TypeFld f01 = TypeFld.malloc("a");
    TypeFld f10 = TypeFld.malloc("a");
    TypeStruct t0 = TypeStruct.malloc_test(f01,fbint);
    TypeStruct t1 = TypeStruct.malloc_test(f10,fbflt);
    TypeMemPtr p0 = TypeMemPtr.make(alias0,t0);
    TypeMemPtr p1 = TypeMemPtr.make(alias0,t1);
    f01.setX(p1);
    f10.setX(p0);
    Type.RECURSIVE_MEET--;
    t0 = t0.install();

    // Meet them
    TypeStruct mt = (TypeStruct)t0.meet(t1);

    // End result should be a cycle of length 1: [,real] -> * ->
    // And NOT: [,real] -> * -> [,real] -> * ->
    assertEquals(Type.SCALAR,mt.at("b"));
    TypeMemPtr pmt = (TypeMemPtr)mt.at("a");
    assertSame(mt,pmt._obj);
  }

  // Test approximating infinite recursive types.  Most simple test case: a
  // single linked-list chain of depth == CUTOFF.
  @Test public void testApprox1() {
    final int CUTOFF = 3;
    int alias0 = BitsAlias.new_alias(BitsAlias.ALLX);

    // Build a depth-CUTOFF linked list chain
    TypeStruct t0 = TypeStruct.make(TypeFld.make("a",Type.XNIL      ,TypeFld.oBot),
                                    TypeFld.make("b",TypeInt.con(99),TypeFld.oBot));
    TypeMemPtr p0 = TypeMemPtr.make(alias0,t0);
    HashMap<Type,Integer> ds = p0.depth();
    assertEquals(0,(int)ds.get(t0));

    TypeStruct t1 = TypeStruct.make(TypeFld.make("a",p0), TypeFld.make("b",TypeInt.con(98)));
    TypeMemPtr p1 = TypeMemPtr.make(alias0,t1);
    ds = p1.depth();
    assertEquals(1,(int)ds.get(t0));
    assertEquals(0,(int)ds.get(t1));
    assertEquals(1,(int)ds.get(p0));

    TypeStruct t2 = TypeStruct.make(TypeFld.make("a",p1), TypeFld.make("b",TypeInt.con(97)));
    TypeMemPtr p2 = TypeMemPtr.make(alias0,t2);
    ds = p2.depth();
    assertEquals(2,(int)ds.get(t0));

    TypeStruct t3 = TypeStruct.make(TypeFld.make("a",p2), TypeFld.make("b",TypeInt.con(96)));
    TypeMemPtr p3 = TypeMemPtr.make(alias0,t3);
    ds = p3.depth();
    assertEquals(CUTOFF  ,(int)ds.get(t0));
    assertEquals(CUTOFF-1,(int)ds.get(t1));
    assertEquals(1,(int)ds.get(t2));
    assertEquals(0,(int)ds.get(t3));
    // No single depth is beyond cutoff
    assertEquals(CUTOFF,p3.max(ds));

    // For all TypeStruct X at depth CUTOFF-1, make a clone of X and X's sub-
    // graph, except every edge to a type at depth CUTOFF is replaced with the
    // X clone.

    // original, too deep
    // t3[,99] -> p2 -> t2[,99] -> p1 -> t1[,flt] -> p0 -> t0[,int] -> nil

    // replace ptrs to t0 with ptrs to t1
    // t3[,99] -> p2 -> t2[,99] -> p1 -> t1[,flt] -> p0 -> t1*

    // collapse redundant ptrs to t1, and MEET t0-tail and t1-tail
    // t3[,99] -> p2 -> t2[,99] -> {p0,p1} -> t1[,{flt&int}] -> {p0,p1}

    TypeStruct tax = t3.approx(CUTOFF,p3._aliases);
    TypeMemPtr pax = TypeMemPtr.make(alias0,tax);
    HashMap<Type,Integer> ds2 = pax.depth();
    assertEquals(CUTOFF-1,p3.max(ds2));
    TypeMemPtr txp1 = (TypeMemPtr)tax.at("a");
    assertEquals(1,(int)ds2.get(txp1));
    TypeStruct txs1 = txp1._obj;
    assertEquals(1,(int)ds2.get(txs1));
    TypeMemPtr txp2 = (TypeMemPtr)txs1.at("a");
    assertEquals(2,(int)ds2.get(txp2));
    TypeStruct txs2 = txp2._obj;
    assertEquals(2,(int)ds2.get(txs2));
    assertEquals(TypeInt.con(98),txs2.at("b"));
    Type txp3 = txs2.at("a");
    //assertEquals(2,(int)ds2.get(txp3));
    //// Weakened expected results after NIL expands to [0]->obj
    //assertEquals(txs2,txp3._obj);
    ////assertEquals(TypeStruct.OBJ,txp3._obj);
    //
    assertTrue(t3.isa(tax));
  }

  // Test approximating infinite recursive types.  End of chain is already
  // cyclic, and we add a few more depth.
  @Test public void testApprox2() {
    Object dummy = TypeMemPtr.TYPES; // <clinit> before RECURSIVE_MEET
    final int CUTOFF = 3;
    int alias0 = BitsAlias.new_alias(BitsAlias.ALLX);
    BitsAlias alias = BitsAlias.make0(alias0);

    // p3 -> t3[,99] -> p2 -> t2[,99] -> p1 -> t1[,flt] -> p0 -> t0[,int] -> p1*

    // Build two structs pointing to each other
    Type.RECURSIVE_MEET++;
    TypeStruct t0 = TypeStruct.malloc_test(TypeFld.malloc("a"),TypeFld.malloc("b"));
    TypeStruct t1 = TypeStruct.malloc_test(TypeFld.malloc("a"),TypeFld.malloc("b"));
    TypeMemPtr p0 = TypeMemPtr.make(alias0,t0);
    TypeMemPtr p1 = TypeMemPtr.make(alias0,t1);
    t0.get("a").setX(p1           );
    t0.get("b").setX(TypeInt.INT64);
    t1.get("a").setX(p0           );
    t1.get("b").setX(TypeFlt.FLT64);
    Type.RECURSIVE_MEET--;
    t0 = t0.install();
    p1 = (TypeMemPtr)t0.at("a");

    HashMap<Type,Integer> ds = p1.depth();
    assertEquals(1,(int)ds.get(t0));
    assertEquals(0,(int)ds.get(t1));

    // Build a depth-CUTOFF linked list chain
    TypeStruct t2 = TypeStruct.make(TypeFld.make("a",p1), TypeFld.make("b",TypeInt.con(99)));
    TypeMemPtr p2 = TypeMemPtr.make(alias0,t2);
    ds = p2.depth();
    assertEquals(2,(int)ds.get(t0));

    TypeStruct t3 = TypeStruct.make(TypeFld.make("a",p2), TypeFld.make("b",TypeInt.con(98)));
    TypeMemPtr p3 = TypeMemPtr.make(alias0,t3);
    ds = p3.depth();
    assertEquals(CUTOFF  ,(int)ds.get(t0));
    assertEquals(CUTOFF-1,(int)ds.get(t1));
    assertEquals(1,(int)ds.get(t2));
    assertEquals(0,(int)ds.get(t3));
    // No single depth is beyond cutoff
    assertEquals(CUTOFF,p3.max(ds));

    // For all TypeStruct X at depth CUTOFF-1, make a clone of X and X's sub-
    // graph, except every edge to a type at depth CUTOFF is replaced with the
    // X clone.

    // original, too deep
    // t3[,98] -> p2 -> t2[,99] -> p1 -> t1[,flt] -> p0 -> t0[,int] -> p1*

    // replace ptrs to t0 with ptrs to t1
    // t3[,98] -> p2 -> t2[,99] -> p1 -> t1[,flt] -> p0 -> t1*

    // collapse redundant ptrs to t1, and MEET t0-tail and t1-tail
    // t3[,98] -> p2 -> t2[,99] -> {p0,p1} -> t1[,{flt&int}] -> {p0,p1}

    TypeStruct tax = t3.approx(CUTOFF,alias);
    TypeMemPtr pax = TypeMemPtr.make(alias0,tax);

    HashMap<Type,Integer> ds2 = pax.depth();
    assertEquals(CUTOFF-1,p3.max(ds2));
    TypeMemPtr txp1 = (TypeMemPtr)tax.at("a");
    assertEquals(1,(int)ds2.get(txp1));
    TypeStruct txs1 = txp1._obj;
    assertEquals(1,(int)ds2.get(txs1));
    TypeMemPtr txp2 = (TypeMemPtr)txs1.at("a");
    assertEquals(2,(int)ds2.get(txp2));
    TypeStruct txs2 = txp2._obj;
    assertEquals(CUTOFF-1,(int)ds2.get(txs2));
    assertEquals(TypeFlt.FLT64,txs2.at("b"));
    Type txp3 = txs2.at("a");
    // Pointer-equals; 'equals()' is not good enough
    //assertSame(txp2, txp3);
    //assertSame(txs2, txp3._obj);
    assertTrue(t3.isa(tax));

    // Add another layer, and approx again
    TypeStruct t4 = TypeStruct.make(TypeFld.make("a",pax), TypeFld.make("b",TypeInt.con(97)));
    TypeMemPtr p4 = TypeMemPtr.make(alias0,t4);
    ds = p4.depth();
    assertEquals(CUTOFF,(int)ds.get(txs2)); // Structure too deep
    TypeStruct tax4 = t4.approx(CUTOFF,alias);
    TypeMemPtr pax4 = TypeMemPtr.make(alias0,tax4);

    ds2 = pax4.depth();
    assertEquals(CUTOFF-1,p3.max(ds2));
    TypeMemPtr t4p1 = (TypeMemPtr)tax4.at("a");
    assertEquals(1,(int)ds2.get(t4p1));
    TypeStruct t4s1 = t4p1._obj;
    assertEquals(1,(int)ds2.get(t4s1));
    TypeMemPtr t4p2 = (TypeMemPtr)t4s1.at("a");
    assertEquals(2,(int)ds2.get(t4p2));
    TypeStruct t4s2 = t4p2._obj;
    assertEquals(CUTOFF-1,(int)ds2.get(t4s2));
    assertEquals(TypeInt.con(99),t4s2.at("b"));
    Type t4p3 = t4s2.at("a");
    //assertEquals(2,(int)ds2.get(t4p3));
    //assertEquals(t4s2,t4p3._obj);
    assertTrue(t4.isa(tax4));
  }

  // Interleaving unrelated type X, and approximating type A which is too deep.
  // A0 -> (X0 <-> X1) -> A1 -> X2 -> A2 -> (X3 <-> X4 ) -> A3 -> X5
  // Approx:
  // A0 -> (X0 <-> X1) -> A1 -> X2 -> A23-> (X35<-> X45) -> A23
  @Test public void testApprox3() {
    int alias0 = BitsAlias.new_alias(BitsAlias.ALLX);
    int alias1 = BitsAlias.new_alias(BitsAlias.ALLX);

    // ......................................................... -> X5
    Type str_x5 = TypeInt.con(55);
    TypeStruct  x5 = TypeStruct.make(TypeFld.make("v",str_x5   ),
                                     TypeFld.make("x",Type.XNIL),
                                     TypeFld.make("a",Type.XNIL));
    TypeMemPtr px5 = TypeMemPtr.make(alias1,x5);

    // ................................................... -> A3 -> X5
    TypeInt str_a3 = TypeInt.con(3);
    TypeStruct  a3 = TypeStruct.make(TypeFld.make("v",str_a3),
                                     TypeFld.make("x",px5   ));
    TypeMemPtr pa3 = TypeMemPtr.make(alias0,a3);

    // Build two structs pointing to each other
    // ...................................... (X3 <-> X4 ) -> A3 -> X5
    Type i13 = TypeInt.con(33);
    Type i14 = TypeInt.con(44);
    TypeFld fi13 = TypeFld.make("v",i13);
    TypeFld fi14 = TypeFld.make("v",i14);
    TypeFld fpa3 = TypeFld.make("a",pa3);
    Type.RECURSIVE_MEET++;
    TypeStruct x3 = TypeStruct.malloc_test(fi13,TypeFld.malloc("x"),fpa3);
    TypeStruct x4 = TypeStruct.malloc_test(fi14,TypeFld.malloc("x"),fpa3);
    TypeMemPtr px3 = TypeMemPtr.make(alias1,x3);
    TypeMemPtr px4 = TypeMemPtr.make(alias1,x4);
    x3.get("x").setX(px4);
    x4.get("x").setX(px3);
    Type.RECURSIVE_MEET--;
    x3 = x3.install();
    px3 = (TypeMemPtr)x4.at("x");

    // ................................ A2 -> (X3 <-> X4 ) -> A3 -> X5
    TypeInt str_a2 = TypeInt.con(2);
    TypeStruct  a2 = TypeStruct.make(TypeFld.make("v",str_a2),
                                     TypeFld.make("x",px3   ));
    TypeMemPtr pa2 = TypeMemPtr.make(alias0,a2);

    // Check sanity
    HashMap<Type,Integer> depths = pa2.depth();
    int maxd = pa2.max(depths);
    assertEquals(1,maxd);
    assertEquals(1,(int)depths.get(a3));

    // .......................... X2 -> A2 -> (X3 <-> X4 ) -> A3 -> X5
    TypeStruct  x2 = TypeStruct.make(TypeFld.make("v",TypeInt.con(22)),
                                     TypeFld.make("x",Type.NIL),
                                     TypeFld.make("a",pa2));
    TypeMemPtr px2 = TypeMemPtr.make(alias1,x2);

    // .................... A1 -> X2 -> A2 -> (X3 <-> X4 ) -> A3 -> X5
    TypeStruct  a1 = TypeStruct.make(TypeFld.make("v",TypeInt.con(1)),
                                     TypeFld.make("x",px2));
    TypeMemPtr pa1 = TypeMemPtr.make(alias0,a1);

    // Build two structs pointing to each other
    // ..... (X0 <-> X1) -> A1 -> X2 -> A2 -> (X3 <-> X4 ) -> A3 -> X5
    Type i10 = TypeInt.con(-100);
    Type i11 = TypeInt.con(11);
    TypeFld fil0 = TypeFld.make("v",i10);
    TypeFld fil1 = TypeFld.make("v",i11);
    TypeFld fpa1 = TypeFld.make("a",pa1);
    Type.RECURSIVE_MEET++;
    TypeStruct x0 = TypeStruct.malloc_test(fil0, TypeFld.malloc("x"), fpa1);
    TypeStruct x1 = TypeStruct.malloc_test(fil1, TypeFld.malloc("x"), fpa1);
    TypeMemPtr px0 = TypeMemPtr.make(alias1,x0);
    TypeMemPtr px1 = TypeMemPtr.make(alias1,x1);
    x0.get("x").setX(px1);
    x1.get("x").setX(px0);
    Type.RECURSIVE_MEET--;
    x0 = x0.install();
    px0 = (TypeMemPtr)x1.at("x");

    // A0 -> (X0 <-> X1) -> A1 -> X2 -> A2 -> (X3 <-> X4 ) -> A3 -> X5
    TypeStruct  a0 = TypeStruct.make(TypeFld.make("v",TypeInt.con(-101)),
                                     TypeFld.make("x",px0));
    TypeMemPtr pa0 = TypeMemPtr.make(alias0,a0);

    // Check sanity
    depths = pa0.depth();
    assertEquals(0,(int)depths.get(a0));
    assertEquals(1,(int)depths.get(a1));
    assertEquals(2,(int)depths.get(a2));
    assertEquals(3,(int)depths.get(a3));
    assertEquals(3,pa0.max(depths));

    // Approximate
    TypeStruct  zsa0 = a0.approx(3,BitsAlias.make0(alias0));
    TypeMemPtr pzsa0 = TypeMemPtr.make(alias0,zsa0);

    // Check sanity!
    // Was: A0 -> (X0 <-> X1) -> A1 -> X2 -> A2 -> (X3 <->  X4) -> A3 -> X5
    // Apx: A0 -> (X0 <-> X1) -> A1 -> X2 -> A23->  X35 -> (X4 <-> X3) -> A23
    assertSame(TypeInt.con(-101), zsa0.at("v"));
    TypeMemPtr zpx0 = (TypeMemPtr)zsa0.at("x");

    TypeStruct zsx0 =             zpx0._obj;
    assertSame  (i10 ,            zsx0.at("v"));
    TypeMemPtr zpx1 = (TypeMemPtr)zsx0.at("x");
    TypeMemPtr zpa1 = (TypeMemPtr)zsx0.at("a");

    TypeStruct zsx1 =             zpx1._obj;
    assertSame  (i11 ,            zsx1.at("v"));
    assertSame  (zpx0,            zsx1.at("x"));
    assertSame  (zpa1,            zsx1.at("a"));

    TypeStruct zsa1 =             zpa1._obj;
    assertSame(TypeInt.con(1),    zsa1.at("v"));
    TypeMemPtr zpx2 = (TypeMemPtr)zsa1.at("x");

    TypeStruct zsx2 =             zpx2._obj;
    assertSame(TypeInt.con(22),   zsx2.at("v"));
    assertSame(Type.NIL,          zsx2.at("x"));
    TypeMemPtr zpa23= (TypeMemPtr)zsx2.at("a");

    TypeStruct zsa23=             zpa23._obj;
    assertSame(TypeInt.con(2),    zsa23.at("v"));
    TypeMemPtr zpx35= (TypeMemPtr)zsa23.at("x");

    TypeStruct zsx35=             zpx35._obj;
    assertSame(TypeInt.con(33),   zsx35.at("v"));
    TypeMemPtr zpa4 = (TypeMemPtr)zsx35.at("x") ;
    Type zpa23q=zsx35.at("a") ;
    // Weakened expected results after NIL expands to [0]->obj
    //assertSame(zsa23,             zpa23q._obj);
    //assertSame(TypeStruct.OBJ,       zpa23q._obj);
    TypeStruct zsx4 =             zpa4._obj;
    assertSame(i14,               zsx4.at("v"));
    assertSame(zpx35,             zsx4.at("x"));
    assertSame(Type.SCALAR,       zsx4.at("a"));

    depths = pzsa0.depth();
    assertEquals(0,(int)depths.get(zsa0));
    assertEquals(1,(int)depths.get(zsa1));
    assertEquals(2,(int)depths.get(zsa23));
    assertEquals(2,pa0.max(depths));
    assertTrue(a0.isa(zsa0));
  }


  // Type A expands tree-like and gets too deep.
  // A1 -> A2 -> A4
  //          -> A5
  //       A3 -> A6
  //          -> A7
  // And then:
  // A1 -> A2 -> A4 -> A8
  // A1 -> A2 -> A4 -> A9
  // A1 -> A2 -> A5 -> A10
  // A1 -> A2 -> A6 -> A12
  // Approx:
  // A1 -> A2 -> A4.8.9      A1.l -> A2.l ->   (nint8, T?, T?)
  //          -> A5.10               A2.r -> T:(nint8, T?, nil)
  //       A3 -> A6.12       A1.r -> A3.l -> T
  //          -> A7               -> A3.r -> (nint8, nil, nil)
  // ... and so forth.
  // The first few tree layers remain expanded, but the tree tail collapses.
  @Test public void testApprox4() {
    final int CUTOFF = 3;
    int alias = BitsAlias.new_alias(BitsAlias.ALLX);
    TypeFld lnil = TypeFld.make("l",Type.NIL);
    TypeFld rnil = TypeFld.make("r",Type.NIL);

    TypeStruct  x12= TypeStruct.make(TypeFld.make("v",TypeInt.con(12)),lnil,rnil);
    TypeMemPtr px12= TypeMemPtr.make(alias,x12);

    TypeStruct  x10= TypeStruct.make(TypeFld.make("v",TypeInt.con(10)),lnil,rnil);
    TypeMemPtr px10= TypeMemPtr.make(alias,x10);

    TypeStruct  x9 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 9)),lnil,rnil);
    TypeMemPtr px9 = TypeMemPtr.make(alias,x9 );

    TypeStruct  x8 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 8)),lnil,rnil);
    TypeMemPtr px8 = TypeMemPtr.make(alias,x8 );

    TypeStruct  x7 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 7)),lnil,rnil);
    TypeMemPtr px7 = TypeMemPtr.make(alias,x7 );

    TypeStruct  x6 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 6)),TypeFld.make("l",px12),rnil);
    TypeMemPtr px6 = TypeMemPtr.make(alias,x6 );

    TypeStruct  x5 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 5)),TypeFld.make("l",px10),rnil);
    TypeMemPtr px5 = TypeMemPtr.make(alias,x5 );

    TypeStruct  x4 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 4)),TypeFld.make("l",px8 ),TypeFld.make("r",px9) );
    TypeMemPtr px4 = TypeMemPtr.make(alias,x4 );

    TypeStruct  x3 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 3)),TypeFld.make("l",px6 ),TypeFld.make("r",px7) );
    TypeMemPtr px3 = TypeMemPtr.make(alias,x3 );

    TypeStruct  x2 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 2)),TypeFld.make("l",px4 ),TypeFld.make("r",px5) );
    TypeMemPtr px2 = TypeMemPtr.make(alias,x2 );

    TypeStruct  x1 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 1)),TypeFld.make("l",px2 ),TypeFld.make("r",px3) );
    TypeMemPtr px1 = TypeMemPtr.make(alias,x1 );

    // Check sanity
    HashMap<Type,Integer> depths = px1.depth();
    assertEquals(0,(int)depths.get(x1));
    assertEquals(1,(int)depths.get(x2));
    assertEquals(1,(int)depths.get(x3));
    assertEquals(2,(int)depths.get(x4));
    assertEquals(2,(int)depths.get(x5));
    assertEquals(2,(int)depths.get(x6));
    assertEquals(2,(int)depths.get(x7));
    assertEquals(3,(int)depths.get(x8));
    assertEquals(3,(int)depths.get(x9));
    assertEquals(3,(int)depths.get(x10));
    assertEquals(3,(int)depths.get(x12));
    assertEquals(3,px1.max(depths));

    // Approximate
    TypeStruct z1 = x1.approx(CUTOFF,BitsAlias.make0(alias));
    TypeMemPtr pz1 = TypeMemPtr.make(alias,z1);
    assertSame( TypeInt.con(1), z1.at("v"));
    TypeMemPtr p2 = (TypeMemPtr)z1.at("l") ;
    TypeMemPtr p3 = (TypeMemPtr)z1.at("r") ;

    TypeStruct z2 =             p2._obj   ;
    assertSame( TypeInt.con(2), z2.at("v"));
    TypeMemPtr p4 = (TypeMemPtr)z2.at("l") ;
    TypeMemPtr p5 = (TypeMemPtr)z2.at("r") ;

    TypeStruct z3 =             p3._obj   ;
    assertSame( TypeInt.con(3), z3.at("v"));
    TypeMemPtr p6 = (TypeMemPtr)z3.at("l") ;
    TypeMemPtr p7 = (TypeMemPtr)z3.at("r") ;

    check_leaf(p4,alias,TypeInt.con(4));
    check_leaf(p5,alias,TypeInt.con(5));
    check_leaf(p6,alias,TypeInt.con(6));
    check_leaf(p7,alias,TypeInt.con(7));

    depths = pz1.depth();
    assertEquals(2,px1.max(depths));
  }

  // Leaf is a TypeInt.NINT8, and both pointer fields are either NIL or contain
  // alias 8 (and optionally nil) and point to a leaf type.
  private void check_leaf( TypeMemPtr p, int alias, TypeInt vt ) {
    TypeStruct z = p._obj;
    assertSame( vt, z.at("v"));
    Type x1 = z.at("l");
    if( x1 != Type.NIL && x1!=Type.SCALAR) {
      TypeMemPtr px = (TypeMemPtr) x1;
      assertTrue(px._aliases.test(alias));
    }
    Type x2 = z.at("r");
    if( x2 != Type.NIL && x2!=Type.SCALAR ) {
      TypeMemPtr px = (TypeMemPtr)x2;
      assertTrue(px._aliases.test(alias));
    }
  }

  // Type A expands tree-like and gets too deep; CUTOFF=2
  // A1 -> {l=S ,r=S ,v} depth=1
  // A2 -> {l=A1,r=S ,v} depth=2
  // A3 -> {l=A1,r=A1,v} depth=2
  // A4 -> {l=A2,r=A3,v} depth=3
  // Should approx to:
  // Z1 -> {l=A1,r=A1,v} depth=2, and Z1=A3
  @Test public void testApprox5() {
    final int CUTOFF = 2;
    int alias = BitsAlias.new_alias(BitsAlias.ALLX);

    TypeStruct  x1= TypeStruct.make(TypeFld.make("l",Type.SCALAR),TypeFld.make("r",Type.SCALAR),TypeFld.make("v",Type.SCALAR));
    TypeMemPtr px1= TypeMemPtr.make(alias,x1);
    assertEquals(0,px1.max(px1.depth()));

    TypeStruct  x2= TypeStruct.make(TypeFld.make("l",   px1     ),TypeFld.make("r",Type.SCALAR),TypeFld.make("v",Type.SCALAR));
    TypeMemPtr px2= TypeMemPtr.make(alias,x2);
    assertEquals(1,px1.max(px2.depth()));

    TypeStruct  x3= TypeStruct.make(TypeFld.make("l",   px1     ),TypeFld.make("r",     px1   ),TypeFld.make("v",Type.SCALAR));
    TypeMemPtr px3= TypeMemPtr.make(alias,x3);
    assertEquals(1,px1.max(px3.depth()));

    TypeStruct  x4= TypeStruct.make(TypeFld.make("l",   px2     ),TypeFld.make("r",     px3   ),TypeFld.make("v",Type.SCALAR));
    TypeMemPtr px4= TypeMemPtr.make(alias,x4);
    assertEquals(2,px1.max(px4.depth()));

    // Approximate
    TypeStruct z1 = x4.approx(CUTOFF,BitsAlias.make0(alias));
    TypeMemPtr pz1 = TypeMemPtr.make(alias,z1);
    assertEquals(1,pz1.max(pz1.depth()));
    assertSame(x3,z1);
  }

  // Type A expands tree-like and gets too deep; CUTOFF=2
  // A1[0,18] -> {l=0 ,r=A1,v} depth=1, cyclic
  // A2[0,18] -> {l=A1,r=A1,v} depth=2, not cyclic
  //             {l=A1,r=A2,v} depth=3, not cyclic
  // Should approx to:
  // A3[0,18] -> {l=A3,r=A3,v} depth=1, cyclic
  //             {l=A1,r=A3,v} depth=2
  @Ignore // invalid, after the change to approx
  @Test public void testApprox6() {
    Object dummy0 = TypeStruct.TYPES;
    Object dummy1 = TypeMemPtr.TYPES;
    final int CUTOFF = 2;
    int alias = BitsAlias.new_alias(BitsAlias.ALLX);

    Type.RECURSIVE_MEET++;
    TypeStruct  x1 = TypeStruct.malloc_test(TypeFld.malloc("l"), TypeFld.malloc("r"), TypeFld.malloc("v"));
    TypeMemPtr px1 = TypeMemPtr.make_nil(alias,x1);
    x1.get("l").setX(Type.XNIL  );
    x1.get("r").setX(px1        );
    x1.get("v").setX(Type.SCALAR);
    Type.RECURSIVE_MEET--;
    x1 = x1.install();
    assertSame(px1,x1.at("r"));

    TypeStruct  x2= TypeStruct.make(TypeFld.make("l",px1),TypeFld.make("r",px1),TypeFld.make("v",Type.SCALAR));
    TypeMemPtr px2= TypeMemPtr.make_nil(alias,x2);

    TypeStruct  z0= TypeStruct.make(TypeFld.make("l",px1),TypeFld.make("r",px2),TypeFld.make("v",Type.SCALAR));
    // Approximate
    TypeStruct z1 = z0.approx1(CUTOFF,BitsAlias.make0(alias));

    Type.RECURSIVE_MEET++;
    TypeStruct  x3 = TypeStruct.malloc_test(TypeFld.malloc("l"), TypeFld.malloc("r"), TypeFld.malloc("v"));
    TypeMemPtr px3 = TypeMemPtr.make_nil(alias,x3);
    x3.get("l").setX(px3);//TypeMemPtr.make_nil(alias,TypeStruct.OBJ);
    x3.get("r").setX(px3);
    x3.get("v").setX(Type.SCALAR);
    Type.RECURSIVE_MEET--;
    x3 = x3.install();
    px3 = (TypeMemPtr)x3.at("l");

    TypeStruct x4= TypeStruct.make(TypeFld.make("l",px1),TypeFld.make("r",px3),TypeFld.make("v",Type.SCALAR));
    assertSame(x4,z1);
  }

  // Regression test.  Verify that a closed DATA cycle in the Node graph makes
  // a finite Type graph.  Basically, endless applying NewObj results to a
  // NewObj (as happens when making simple cyclic structures via storing fields
  // from one into the other) ends with a simple cyclic graph and not an
  // endlessly growing or endlessly "ping ponging" result.
  @Test public void testApprox7() {

    // Make a short cycle using alias RECORD.  Repeated add instances & approx,
    // until fixed point.
    final int CUTOFF=3;
    TypeStruct ts0 = TypeStruct.make(TypeFld.NO_DISP);
    TypeMemPtr tmp0 = TypeMemPtr.make(BitsAlias.ALL0,ts0), tmp1=null;

    int cnt=0;
    while( tmp0 != tmp1 && cnt < 100 ) {
      TypeStruct ts1 = TypeStruct.make(TypeFld.make("^",tmp1=tmp0));
      TypeStruct ts1x = ts1.approx(CUTOFF-1,BitsAlias.NALL);
      // Extend with nil-or-not endlessly.
      tmp0 = TypeMemPtr.make(BitsAlias.ALL0,ts1x);
      cnt++;
    }
    // End result has no prefix, since NIL is allowed at every step.  i.e., we
    // added NIL-or-ptr-to-self 3 times, which is exactly approximated by a
    // tight loop with no prefix.
    assertEquals(CUTOFF,cnt);


    // Make some child aliases.
    final int alias6 = BitsAlias.new_alias(BitsAlias.ALLX);
    final int alias7 = BitsAlias.new_alias(BitsAlias.ALLX);
    final int alias8 = BitsAlias.new_alias(BitsAlias.ALLX);
    final BitsAlias ba6 = BitsAlias.make0(alias6);
    final BitsAlias ba7 = BitsAlias.make0(alias7);
    final BitsAlias ba8 = BitsAlias.make0(alias8);
    final BitsAlias ba60 = ba6.meet_nil();
    final BitsAlias ba70 = ba7.meet_nil();
    final BitsAlias ba80 = ba8.meet_nil();

    // Add a struct with alias6 & approx.  Expect no change, despite alias6
    // being a child of RECORD.
    TypeStruct ts6 = TypeStruct.make(TypeFld.make("^",tmp0));
    TypeStruct ts6x = ts6.approx(CUTOFF,ba6);
    assertEquals(ts6,ts6x);
    TypeMemPtr tmp6 = TypeMemPtr.make(ba60,ts6);
    // Again with alias7
    TypeStruct ts7 = TypeStruct.make(TypeFld.make("^",tmp6));
    TypeStruct ts7x = ts7.approx(CUTOFF,ba7);
    assertEquals(ts7,ts7x);
    TypeMemPtr tmp7 = TypeMemPtr.make(ba70,ts7);
    // Again with alias8
    TypeStruct ts8 = TypeStruct.make(TypeFld.make("^",tmp7));
    TypeStruct ts8x = ts8.approx(CUTOFF,ba8);
    assertEquals(ts8,ts8x);


    // Start with short cycle:
    //  10_( 11_* );  11#2 -> 10
    // Add this on top (alias#4 and#3 are children of #2):
    //   12#4 -> 13; 13_( 17_*, 14_* );  14#3 -> 15;  15_( 16_*, 2.3 ); 16#4 -> 10;  17#5 -> 18; 18_(nil,1.2)
    // Approx alias#4 should do nothing (only depth 2 for alias#4 till hit cycle).
    // Then add it again & approx at depth 2 for alias#2.


    // Start with: A -> A
    // A is basic RECORD type, actually equal to TypeStruct.DISPLAY.
    // B,C,D are child aliases of A and are alias6,7,8.
    // D is a LHS end type: D -> (nil,88)
    TypeStruct tsD = TypeStruct.make(TypeFld.NO_DISP, TypeFld.make_tup(TypeInt.con(88),ARG_IDX));
    TypeMemPtr tmpD = TypeMemPtr.make(ba8,tsD); // Note not nil
    // Add (alternating the repeating field left and right):
    //   B1 = ( A , 99 )
    TypeStruct tsB1 = TypeStruct.make(TypeFld.make("^",tmp0,DSP_IDX),TypeFld.make_tup(TypeInt.con(99),ARG_IDX));
    assertEquals(tsB1,tsB1.approx(CUTOFF,ba6));
    TypeMemPtr tmpB1= TypeMemPtr.make(ba6,tsB1); // Note not nil
    //   C1 = ( D , B1 )
    TypeStruct tsC1 = TypeStruct.make(TypeFld.make("^",tmpD,DSP_IDX),TypeFld.make_tup(tmpB1,ARG_IDX));
    assertEquals(tsC1,tsC1.approx(CUTOFF,ba7));
    TypeMemPtr tmpC1= TypeMemPtr.make(ba7,tsC1); // Note not nil

    // Add repeatedly until stable:
    //   B2 = ( C1, 99 )
    //   C2 = ( D , B2 )
    // This should approx by meeting a C with an A, which should drop off the
    // RHS of the C.  The C LHS is a D, which again meets with A to finish the
    // collapse.  Bug is that types flip-flop between 2 variants endlessly.
    cnt = 0;  tmp1 = null;
    while( tmpC1 != tmp1 && cnt < 100 ) {
      tmp1 = tmpC1;
      //   B2 = ( C1, 99 )
      TypeStruct tsB2 = TypeStruct.make(TypeFld.make("^",tmpC1,DSP_IDX),TypeFld.make_tup(TypeInt.con(99),ARG_IDX));
      TypeStruct tsB2x = tsB2.approx(CUTOFF,ba6);
      TypeMemPtr tmpB2= TypeMemPtr.make(ba6,tsB2x); // Note not nil

      //   C2 = ( D , B2 )
      TypeStruct tsC2 = TypeStruct.make(TypeFld.make("^",tmpD,DSP_IDX),TypeFld.make_tup(tmpB2,ARG_IDX));
      TypeStruct tsC2x = tsC2.approx(CUTOFF,ba7);
      TypeMemPtr tmpC2= TypeMemPtr.make(ba7,tsC2x); // Note not nil
      tmpC1 = tmpC2;
      cnt++;
    }
    assertEquals(CUTOFF,cnt);
  }

  @Test public void testApprox8() {
    Object dummy0 = TypeStruct.TYPES;
    Object dummy1 = TypeFunPtr.TYPES;
    Object dummy2 = Env.GVN;
    final int CUTOFF=2;
    final int fidx = BitsFun.new_fidx(1), fidx0 = BitsFun.new_fidx(fidx), fidx1 = BitsFun.new_fidx(fidx);
    final BitsFun fidxs = BitsFun.make0(fidx0,fidx1).dual();
    final int alias = BitsAlias.new_alias(BitsAlias.ALLX);

    // Args for the forward-ref fib(^ ->Scalar).  This has to start as hi-args
    // for this test, as the cyclic approx is supposed to be low - and it has
    // args known post-parse but not pre-parse.
    TypeStruct tfp0_args = TypeStruct.make("", true, TypeMemPtr.DISP_FLD);

    TypeFunPtr tfp0 = TypeFunPtr.make(BitsFun.ANY0,2,TypeFunPtr.DISP.simple_ptr(),Type.SCALAR); // fib with generic display
    TypeStruct dsp0 = TypeStruct.make(TypeMemPtr.DISP_FLD,TypeFld.make("fib",tfp0));// The display with weak fib-type
    TypeMemPtr ptr0 = TypeMemPtr.make(alias,dsp0);
    // Args for a strong fib: { ^:ptr0 x:int64 -> ~Scalar } // LOW
    TypeStruct arg0 = TypeStruct.make(TypeFld.make("->",Type.SCALAR),
                                      TypeFld.make("^",ptr0.simple_ptr()),
                                      TypeFld.make("x",TypeInt.INT64));

    TypeFunPtr tfp1 = TypeFunPtr.make(fidxs,2,ptr0.simple_ptr(),Type.SCALAR); // FIB with weak display
    TypeStruct dsp1 = TypeStruct.make(TypeMemPtr.DISP_FLD,TypeFld.make("fib",tfp1)); // Display with stronger FIB-type
    TypeMemPtr ptr1 = TypeMemPtr.make(alias,dsp1);
    // Args for a strong fib: { ^:ptr x:int -> ~Scalar } // LOW.  Display still not recursive.
    TypeStruct arg1 = TypeStruct.make(TypeFld.make("->",Type.SCALAR),
                                      TypeFld.make("^",ptr1.simple_ptr()),
                                      TypeFld.make("x",TypeInt.INT64));

    TypeFunPtr tfp2 = TypeFunPtr.make(fidxs,2,ptr1.simple_ptr(),Type.SCALAR); // fib2->dsp1->fib1->dsp0->fib0->generic_display
    TypeStruct dsp2 = TypeStruct.make(TypeMemPtr.DISP_FLD,TypeFld.make("fib",tfp2)); // dsp2->fib2->dsp1->fib1->dsp0->fib0->generic_display

    // The approx that gets built: fib3->dsp3->fib3->dsp3->...
    Type.RECURSIVE_MEET++;
    TypeStruct dsp3 = TypeStruct.malloc_test(TypeFld.malloc("^",null, TypeFld.Access.Final,DSP_IDX), TypeFld.malloc("fib"));
    TypeMemPtr ptr3 = TypeMemPtr.make(alias,dsp3);
    TypeStruct arg3 = TypeStruct.make(TypeFld.make("->",Type.SCALAR),
                                      TypeFld.make("^",ptr3.simple_ptr()),
                                      TypeFld.make("x",TypeInt.INT64));
    TypeFunPtr tfp3 = TypeFunPtr.make(fidxs,2,ptr3.simple_ptr(),Type.SCALAR);
    dsp3.get("^").setX(TypeMemPtr.DISPLAY_PTR);
    dsp3.get("fib").setX(tfp3);
    Type.RECURSIVE_MEET--;
    dsp3 = dsp3.install();

    // This should pass an isa-test (was crashing)
    Type mt0 = dsp0.meet(dsp3);

    // This should pass an isa-test (was crashing)
    Type mt1 = dsp1.meet(dsp3);

    // Check the isa
    Type mt = dsp2.meet(dsp3);
    assertEquals(dsp3,mt);

    // Build the approx
    TypeStruct rez = dsp2.approx1(CUTOFF,BitsAlias.make0(alias));
    assertEquals(dsp3,rez);
  }


  // Regression test from TestHM.test58; both HM and GCP, rseed==0; Asserts
  // doing a complex approx call that "!this.isa(rez)"; the returned type is
  // not isa the 'this' type.  This looks like: "this.meet(rez)" does not
  // minimize cycles properly, and this ISA rez but the standard isa test fails
  // because "this.meet(rez)" is not minimized properly.
  @Test public void testApprox9() {
    Object dummy0 = TypeStruct.TYPES;

    int alias13 = BitsAlias.new_alias(BitsAlias.ALLX);
    int alias14 = BitsAlias.new_alias(BitsAlias.ALLX);
    BitsAlias a14   = BitsAlias.ALL0.make(        alias14);
    BitsAlias a1314 = BitsAlias.ALL0.make(alias13,alias14);
    int fidx14 = BitsFun.new_fidx();
    int fidx25 = BitsFun.new_fidx();
    BitsFun f1425 = BitsFun.make0(fidx14,fidx25);
    int fidx22 = BitsFun.new_fidx();
    int fidx26 = BitsFun.new_fidx();
    BitsFun f2226 = BitsFun.make0(fidx22,fidx26);

    //REZ (shortened); result of approx, alias=14, depth=1
    //C:@{
    //  pred  =[14,25]{any ->*[13,14]C$ };
    //  succ  =[22,26]{any ->*[   14]C$ }
    //}
    TypeStruct rez;
    {
      Type.RECURSIVE_MEET++;
      TypeFld pred = TypeFld.malloc("pred");
      TypeFld succ = TypeFld.malloc("succ");
      rez = TypeStruct.make(pred,succ).set_hash();
      _help0(pred,f1425,a1314,rez);
      _help0(succ,f2226,a14  ,rez);
      Type.RECURSIVE_MEET--;
      rez = rez.install();
    }

    TypeStruct thismeetrez;
    {
      Type.RECURSIVE_MEET++;
      TypeFld pred2 = TypeFld.malloc("pred");
      TypeFld succ1 = TypeFld.malloc("succ");
      TypeStruct str1 = TypeStruct.make(rez.get("pred"),succ1).set_hash();
      TypeStruct str2 = TypeStruct.make(pred2,rez.get("succ")).set_hash();
      _help0(pred2,f1425,a1314,str1);
      _help0(succ1,f2226,a14  ,str2);
      Type.RECURSIVE_MEET--;
      thismeetrez = str2.install();
    }

    // Install shrinks
    assertEquals(rez,thismeetrez);
  }

  // Make the field point at the struct
  private static void _help0( TypeFld fld, BitsFun fidx, BitsAlias alias, TypeStruct rez ) {
    TypeMemPtr ptr = TypeMemPtr.make(alias,rez);
    fld.setX(TypeFunPtr.make(fidx,1,TypeMemPtr.NO_DISP,ptr));
  }

}
