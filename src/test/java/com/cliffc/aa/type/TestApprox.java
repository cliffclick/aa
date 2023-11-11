package com.cliffc.aa.type;

import org.junit.Ignore;
import org.junit.Test;

import static com.cliffc.aa.AA.ARG_IDX;
import static com.cliffc.aa.AA.TODO;
import static org.junit.Assert.assertTrue;

// CNC: As of 02/20/2022 I have dropped approx from the whole Type analysis
// algorithm.  Mostly dropped because I could not "make it work", see more
// notes in TypeStruct.  Either the approx was not monotonic, or it "sucked" -
// had to produce extremely conservative values.  These tests still exist for
// documentation but are all turned off.


@Ignore
public class TestApprox {
//  // temp/junk holder for "instant" junits, when debugged moved into other tests
//  @Test public void testType() {
//    Object ignore = TypeMemPtr.TYPES; // <clinit> before RECURSIVE_MEET
//    // BASE TYPE:
//    // *[3]@{n1=*[0,3]@{FA:n1=*[0,2]@{n1=*[0,3]@{FA; v1=~str}; v1=~str}; v1=~Scalar}; v1=~Scalar}
//    int a5 = BitsAlias.new_alias();
//    int a6 = BitsAlias.new_alias();
//    int astr = TypeMemPtr.STRPTR._aliases.abit();
//    if( astr > a6 ) BitsAlias.new_alias();
//
//    TypeFld FC = TypeFld.make("v1",TypeMemPtr.STRPTR.dual());
//    TypeFld FD = TypeFld.make("v1",Type.XSCALAR);
//
//    Type.RECURSIVE_MEET++;
//    TypeFld FB = TypeFld.malloc("n1");
//    TypeMemPtr P60 = TypeMemPtr.make_nil(a6,TypeStruct.malloc_test(FB,FC));
//    TypeStruct SB  = TypeStruct.malloc_test(TypeFld.make("n1",P60),FC);
//    TypeMemPtr P50 = TypeMemPtr.make_nil(a5,SB);
//    FB.setX(P50);
//    Type.RECURSIVE_MEET--;
//    SB = Cyclic.install(SB);
//
//    TypeMemPtr P6X = TypeMemPtr.make_nil(a6,TypeStruct.make(FB,FD));
//    TypeMemPtr P6 = TypeMemPtr.make(a6,TypeStruct.make(TypeFld.make("n1",P6X),FD));
//
//    TypeStruct ts = P6._obj.approx(P6._aliases);
//
//    // APPROX IS:
//    //*[3]@{n1=*[0,3]SA:@{n1=*[0,2,3]SA; v1=~Scalar}; v1=~Scalar}
//    // Which fails internally for v1=~Scalar being too high.
//    // Path: *[3]@{n1=*[0,3]@{n1=*[0,2,3]@{v1=???}}}
//
//
//
//  }
  // Test approx of fcns-returning-fcns
  @Test public void testFunctionReturn() {
    // ND = ^=any,   D = ^=Scalar
    // XS = ~Scalar, S =   Scalar
    // XA = [17]{any,3 ->*[3](XS, XS) }
    // XB = [17]{any,3 ->*[3](XS,  S) }
    //
    //
    // TS0:  *[3]( XA, [17]{any,3 ->*[3](S,XS) } )
    // APX2: *[3]( XB, [17]{any,3 ->*[3](S, S) } )
    //
    // TS1:  *[3]( XA, [17]{any,3 ->*[3](S, S) } )
    // APX2: *[3]( XA, [17]{any,3 ->*[3](S, S) } )
    //
    // TS0>>TS1, because last 'XS' falls to 'S'
    // TS0>>TS0.apx
    // TS1>>TS1.apx

    int a3 = BitsAlias.new_alias(BitsAlias.ALLX);
    int f7 = BitsFun.new_fidx(BitsFun.ALLX);
    int f2 = BitsFun.new_fidx(BitsFun.ALLX);
    Type ND = TypeNil.NO_DSP;
    TypeFld S0 = TypeFld.make_tup(TypeNil. SCALAR,ARG_IDX+0);
    TypeFld X0 = TypeFld.make_tup(TypeNil.XSCALAR,ARG_IDX+0);
    TypeFld S1 = TypeFld.make_tup(TypeNil. SCALAR,ARG_IDX+1);
    TypeFld X1 = TypeFld.make_tup(TypeNil.XSCALAR,ARG_IDX+1);
    TypeFld S2 = TypeFld.make_tup(TypeNil. SCALAR,ARG_IDX+2);
    TypeFld X2 = TypeFld.make_tup(TypeNil.XSCALAR,ARG_IDX+2);
    //TypeMemPtr tmpa = TypeMemPtr.make(a3,TypeStruct.make(X0,X1));
    //TypeFunPtr tfpa = TypeFunPtr.make(f7,3,ND,tmpa);
    //
    //TypeMemPtr tmp0 = TypeMemPtr.make(a3,TypeStruct.make(S0,X1));
    //TypeFunPtr tfp0 = TypeFunPtr.make(f7,3,ND,tmp0);
    //TypeMemPtr ts0  = TypeMemPtr.make(a3,TypeStruct.make(TypeFld.make_tup(tfpa,ARG_IDX+1),TypeFld.make_tup(tfp0,ARG_IDX+2)));
    //
    //TypeMemPtr tmp1 = TypeMemPtr.make(a3,TypeStruct.make(S0,S1));
    //TypeFunPtr tfp1 = TypeFunPtr.make(f7,3,ND,tmp1);
    //TypeMemPtr ts1  = TypeMemPtr.make(a3,TypeStruct.make(TypeFld.make_tup(tfpa,ARG_IDX+1),TypeFld.make_tup(tfp1,ARG_IDX+2)));
    //
    //assertTrue(tmp0.isa(tmp1));
    ////TypeStruct ax0 = ts0._obj.approx(ts0._aliases);
    ////TypeStruct ax1 = ts1._obj.approx(ts1._aliases);
    ////assertTrue(ts0._obj.isa(ax0));
    ////assertTrue(ts1._obj.isa(ax1));
    ////
    ////assertTrue(ax0.isa(ax1));
    //
    //
    //// Make a collection of probably function-to-functions
    //Ary<TypeFunPtr> tfps = new Ary<>(TypeFunPtr.class);
    //tfps.push(tfpa);
    //tfps.push(tfp0);
    //tfps.push(tfp1);
    //tfps.push(TypeFunPtr.make(f2,1,ND,Type.XSCALAR));
    //tfps.push(TypeFunPtr.make(f2,1,ND,Type. SCALAR));
    //tfps.push(TypeFunPtr.make(f7,1,ND,Type.XSCALAR));
    //tfps.push(TypeFunPtr.make(f7,1,ND,Type. SCALAR));
    //BitsFun bf2  = BitsFun.make0(f2);
    //BitsFun bf7  = BitsFun.make0(f7);
    //BitsFun bf27 = BitsFun.make0(f2,f7);
    //tfps.push(TypeFunPtr.make_cycle(bf2 ,1,ND));
    //tfps.push(TypeFunPtr.make_cycle(bf7 ,1,ND));
    //tfps.push(TypeFunPtr.make_cycle(bf27,1,ND));
    //tfps.push(TypeFunPtr.make(f2,1,ND,TypeFunPtr.make(f7,1,ND,Type.XSCALAR)));
    //tfps.push(TypeFunPtr.make(f2,1,ND,TypeFunPtr.make(f7,1,ND,Type. SCALAR)));
    //tfps.push(TypeFunPtr.make(f7,1,ND,TypeFunPtr.make(f2,1,ND,Type.XSCALAR)));
    //tfps.push(TypeFunPtr.make(f7,1,ND,TypeFunPtr.make(f2,1,ND,Type. SCALAR)));
    //
    //// Check that we can wrap sanely
    //for( int i=0; i<tfps._len; i++ ) {
    //  TypeFunPtr tfpi = tfps.at(i);
    //  for( int j=i+1; j<tfps._len; j++ ) {
    //    TypeFunPtr tfpj = tfps.at(j);
    //    assert tfpi!=tfpj;      // No dups
    //    if( tfpi.isa(tfpj) ) {
    //      TypeFunPtr tfpi2  = TypeFunPtr.makex(bf2 ,1,ND,tfpi);
    //      TypeFunPtr tfpj2  = TypeFunPtr.makex(bf2 ,1,ND,tfpj);
    //      assert tfpi2 .isa(tfpj2 );
    //      TypeFunPtr tfpi7  = TypeFunPtr.makex(bf7 ,1,ND,tfpi);
    //      TypeFunPtr tfpj7  = TypeFunPtr.makex(bf7 ,1,ND,tfpj);
    //      assert tfpi7 .isa(tfpj7 );
    //      TypeFunPtr tfpi27 = TypeFunPtr.makex(bf27,1,ND,tfpi);
    //      TypeFunPtr tfpj27 = TypeFunPtr.makex(bf27,1,ND,tfpj);
    //      assert tfpi27.isa(tfpj27);
    //    }
    //  }
    //}
    throw TODO();

  }

//  private TypeFld make(BitsFun fidxs,Type ret) { return TypeFld.make("pred",TypeFunPtr.make(fidxs,1,TypeMemPtr.NO_DISP,ret)); }
//  @Ignore
//  @Test public void testApproxAssociative() {
//    // Proof approx is not associative with meet.
//    // E.g. A.approx.meet(B) != A.meet(B).approx
//    // Simple case:
//
//    // A     : *[7]@{ x = 3   ; fld = *[7]@{ x = "abc"; } }
//    // B     : *[7]@{ x = 4   ; fld = ALL; }
//    // A.X   : *[7]@{ x = SCLR; fld = ALL; }  // Approx meets 3&"abc"; also loses 'fld='
//    // A.X.B : *[7]@{ x = SCLR; fld = ALL; }  // Weak field 'x'
//    // A.B   : *[7]@{ x = nint; fld = ALL; }  // Better field 'x', still loses 'fld='
//    // A.B.X : *[7]@{ x = nint; fld = ALL; }
//
//    // Current Approx is a little different.
//    // For A.X, since 3 <<!>> "abc", 'fld' cannot cycle in either direction, falls to NSCALAR;
//    // A.X   : *[7]@{ x = 3   ; fld = NSCALR; }  // Approx loses 'fld='
//    // A.X.B : *[7]@{ x = nint; fld = ALL; }
//    // A.B   : *[7]@{ x = nint; fld = ALL; }  // Unchanged from above, same as B
//    // A.B.X : *[7]@{ x = nint; fld = ALL; }
//    int a14 = BitsAlias.new_alias(BitsAlias.ALLX);
//    BitsAlias ba14 = BitsAlias.make0(a14);
//    BitsFun f25 = BitsFun.make_new_fidx(BitsFun.ALLX);
//    TypeFld p0 = make(BitsFun.ALL,Type.SCALAR);
//    TypeMemPtr ptr0 = TypeMemPtr.make(ba14,TypeStruct.make(p0));
//    TypeFld p1 = make(f25,ptr0);
//    TypeStruct tsa = TypeStruct.make(p1);
//    TypeMemPtr ptra = TypeMemPtr.make(ba14,tsa);
//
//    TypeFld pb = make(f25,Type.SCALAR);
//    TypeStruct tsb = TypeStruct.make(pb);
//    TypeMemPtr ptrb = TypeMemPtr.make(BitsAlias.EMPTY,tsb);
//
//    TypeStruct ax  = tsa.approx(ba14);
//    TypeStruct axb = (TypeStruct)ax.meet(tsb);
//
//    TypeStruct ab = (TypeStruct)tsa.meet(tsb);
//    TypeStruct abx = ab.approx(ba14);
//
//    assertEquals(axb,abx); // Would like this to be equals!!!!
//  }
//
//  // Test of a cutoff=1 for a depth=1 cycle
//  @Ignore
//  @Test public void testCycle1() {
//    Object dummy = TypeMemPtr.TYPES; // <clinit> before RECURSIVE_MEET
//    int alias = BitsAlias.new_alias(BitsAlias.ALLX);
//    TypeFld dummy2 = TypeFld.make("dummy",Type.SCALAR);
//    Type.RECURSIVE_MEET++;
//    TypeFld fld = TypeFld.malloc("fld");
//    TypeStruct ts = TypeStruct.malloc_test(fld);
//    TypeMemPtr p = TypeMemPtr.make(alias,ts);
//    fld.setX(p);
//    Type.RECURSIVE_MEET--;
//    ts = Cyclic.install(ts);
//
//    TypeStruct t2 = ts.approx(p._aliases);
//    assertEquals(ts,t2);
//  }
//
//  // Check TypeStruct.meet for a more complex recursive case
//  @Test public void testTSMeet() {
//    Object dummy = TypeMemPtr.TYPES; // <clinit> before RECURSIVE_MEET
//    int alias0 = BitsAlias.new_alias(BitsAlias.ALLX);
//
//    // Build two structs pointing to each other.
//    //   -> [,int] -> * -> [,flt] -> * ->
//    TypeFld fbint = TypeFld.make("b",TypeInt.INT64,TypeFld.oBot);
//    TypeFld fbflt = TypeFld.make("b",TypeFlt.FLT64,TypeFld.oBot);
//    Type.RECURSIVE_MEET++;
//    TypeFld f01 = TypeFld.malloc("a");
//    TypeFld f10 = TypeFld.malloc("a");
//    TypeStruct t0 = TypeStruct.malloc_test(f01,fbint);
//    TypeStruct t1 = TypeStruct.malloc_test(f10,fbflt);
//    TypeMemPtr p0 = TypeMemPtr.make(alias0,t0);
//    TypeMemPtr p1 = TypeMemPtr.make(alias0,t1);
//    f01.setX(p1);
//    f10.setX(p0);
//    Type.RECURSIVE_MEET--;
//    t0 = Cyclic.install(t0);
//
//    // Meet them
//    TypeStruct mt = (TypeStruct)t0.meet(t1);
//
//    // End result should be a cycle of length 1: [,real] -> * ->
//    // And NOT: [,real] -> * -> [,real] -> * ->
//    assertEquals(Type.SCALAR,mt.at("b"));
//    TypeMemPtr pmt = (TypeMemPtr)mt.at("a");
//    assertSame(mt,pmt._obj);
//  }
//
//  // Test approximating infinite recursive types.  Most simple test case: a
//  // single linked-list chain of depth == CUTOFF.
//  @Ignore
//  @Test public void testApprox1() {
//    final int CUTOFF = 3;
//    int alias0 = BitsAlias.new_alias(BitsAlias.ALLX);
//
//    // Build a depth-CUTOFF linked list chain
//    TypeStruct t0 = TypeStruct.make(TypeFld.make("a",Type.NIL       ,TypeFld.oBot),
//                                    TypeFld.make("b",TypeInt.con(99),TypeFld.oBot));
//    TypeMemPtr p0 = TypeMemPtr.make(alias0,t0);
//    HashMap<Type,Integer> ds = p0.depth();
//    assertEquals(0,(int)ds.get(t0));
//
//    TypeStruct t1 = TypeStruct.make(TypeFld.make("a",p0), TypeFld.make("b",TypeInt.con(98)));
//    TypeMemPtr p1 = TypeMemPtr.make(alias0,t1);
//    ds = p1.depth();
//    assertEquals(1,(int)ds.get(t0));
//    assertEquals(0,(int)ds.get(t1));
//    assertEquals(1,(int)ds.get(p0));
//
//    TypeStruct t2 = TypeStruct.make(TypeFld.make("a",p1), TypeFld.make("b",TypeInt.con(97)));
//    TypeMemPtr p2 = TypeMemPtr.make(alias0,t2);
//    ds = p2.depth();
//    assertEquals(2,(int)ds.get(t0));
//
//    TypeStruct t3 = TypeStruct.make(TypeFld.make("a",p2), TypeFld.make("b",TypeInt.con(96)));
//    TypeMemPtr p3 = TypeMemPtr.make(alias0,t3);
//    ds = p3.depth();
//    assertEquals(CUTOFF  ,(int)ds.get(t0));
//    assertEquals(CUTOFF-1,(int)ds.get(t1));
//    assertEquals(1,(int)ds.get(t2));
//    assertEquals(0,(int)ds.get(t3));
//    // No single depth is beyond cutoff
//    assertEquals(CUTOFF,p3.max(ds));
//
//    // For all TypeStruct X at depth CUTOFF-1, make a clone of X and X's sub-
//    // graph, except every edge to a type at depth CUTOFF is replaced with the
//    // X clone.
//
//    // original, too deep
//    // t3[,99] -> p2 -> t2[,99] -> p1 -> t1[,flt] -> p0 -> t0[,int] -> nil
//
//    // replace ptrs to t0 with ptrs to t1
//    // t3[,99] -> p2 -> t2[,99] -> p1 -> t1[,flt] -> p0 -> t1*
//
//    // collapse redundant ptrs to t1, and MEET t0-tail and t1-tail
//    // t3[,99] -> p2 -> t2[,99] -> {p0,p1} -> t1[,{flt&int}] -> {p0,p1}
//
//    TypeStruct tax = t3.approx(p3._aliases);
//    TypeMemPtr pax = TypeMemPtr.make(alias0,tax);
//    HashMap<Type,Integer> ds2 = pax.depth();
//    // CNC, as of 2/14/2022 approx chops at any point where the alias is seen
//    // and ISA fails in either direction.  Also, CUTOFF is fixed at 1.
//    assertEquals(0,p3.max(ds2));
//    //assertEquals(CUTOFF-1,p3.max(ds2));
//    //TypeMemPtr txp1 = (TypeMemPtr)tax.at("a");
//    //assertEquals(1,(int)ds2.get(txp1));
//    //TypeStruct txs1 = txp1._obj;
//    //assertEquals(1,(int)ds2.get(txs1));
//    //TypeMemPtr txp2 = (TypeMemPtr)txs1.at("a");
//    //assertEquals(2,(int)ds2.get(txp2));
//    //TypeStruct txs2 = txp2._obj;
//    //assertEquals(2,(int)ds2.get(txs2));
//    //assertEquals(TypeInt.NINT8,txs2.at("b"));
//    //Type txp3 = txs2.at("a");
//    ////assertEquals(2,(int)ds2.get(txp3));
//    ////// Weakened expected results after NIL expands to [0]->obj
//    ////assertEquals(txs2,txp3._obj);
//    //////assertEquals(TypeStruct.OBJ,txp3._obj);
//    ////
//    //assertTrue(t3.isa(tax));
//  }
//
//  // Test approximating infinite recursive types.  End of chain is already
//  // cyclic, and we add a few more depth.
//  @Ignore
//  @Test public void testApprox2() {
//    Object dummy = TypeMemPtr.TYPES; // <clinit> before RECURSIVE_MEET
//    final int CUTOFF = 3;
//    int alias0 = BitsAlias.new_alias(BitsAlias.ALLX);
//    BitsAlias alias = BitsAlias.make0(alias0);
//
//    // p3 -> t3[,99] -> p2 -> t2[,99] -> p1 -> t1[,flt] -> p0 -> t0[,int] -> p1*
//
//    // Build two structs pointing to each other
//    Type.RECURSIVE_MEET++;
//    TypeStruct t0 = TypeStruct.malloc_test(TypeFld.malloc("a"),TypeFld.malloc("b"));
//    TypeStruct t1 = TypeStruct.malloc_test(TypeFld.malloc("a"),TypeFld.malloc("b"));
//    TypeMemPtr p0 = TypeMemPtr.make(alias0,t0);
//    TypeMemPtr p1 = TypeMemPtr.make(alias0,t1);
//    t0.get("a").setX(p1           );
//    t0.get("b").setX(TypeInt.INT64);
//    t1.get("a").setX(p0           );
//    t1.get("b").setX(TypeFlt.FLT64);
//    Type.RECURSIVE_MEET--;
//    t0 = Cyclic.install(t0);
//    p1 = (TypeMemPtr)t0.at("a");
//
//    HashMap<Type,Integer> ds = p1.depth();
//    assertEquals(1,(int)ds.get(t0));
//    assertEquals(0,(int)ds.get(t1));
//
//    // Build a depth-CUTOFF linked list chain
//    TypeStruct t2 = TypeStruct.make(TypeFld.make("a",p1), TypeFld.make("b",TypeInt.con(99)));
//    TypeMemPtr p2 = TypeMemPtr.make(alias0,t2);
//    ds = p2.depth();
//    assertEquals(2,(int)ds.get(t0));
//
//    TypeStruct t3 = TypeStruct.make(TypeFld.make("a",p2), TypeFld.make("b",TypeInt.con(98)));
//    TypeMemPtr p3 = TypeMemPtr.make(alias0,t3);
//    ds = p3.depth();
//    assertEquals(CUTOFF  ,(int)ds.get(t0));
//    assertEquals(CUTOFF-1,(int)ds.get(t1));
//    assertEquals(1,(int)ds.get(t2));
//    assertEquals(0,(int)ds.get(t3));
//    // No single depth is beyond cutoff
//    assertEquals(CUTOFF,p3.max(ds));
//
//    // For all TypeStruct X at depth CUTOFF-1, make a clone of X and X's sub-
//    // graph, except every edge to a type at depth CUTOFF is replaced with the
//    // X clone.
//
//    // original, too deep
//    // t3[,98] -> p2 -> t2[,99] -> p1 -> t1[,flt] -> p0 -> t0[,int] -> p1*
//
//    // replace ptrs to t0 with ptrs to t1
//    // t3[,98] -> p2 -> t2[,99] -> p1 -> t1[,flt] -> p0 -> t1*
//
//    // collapse redundant ptrs to t1, and MEET t0-tail and t1-tail
//    // t3[,98] -> p2 -> t2[,99] -> {p0,p1} -> t1[,{flt&int}] -> {p0,p1}
//
//    TypeStruct tax = t3.approx(alias);
//    TypeMemPtr pax = TypeMemPtr.make(alias0,tax);
//
//    HashMap<Type,Integer> ds2 = pax.depth();
//    assertEquals(CUTOFF-1,p3.max(ds2));
//    TypeMemPtr txp1 = (TypeMemPtr)tax.at("a");
//    assertEquals(1,(int)ds2.get(txp1));
//    TypeStruct txs1 = txp1._obj;
//    assertEquals(1,(int)ds2.get(txs1));
//    TypeMemPtr txp2 = (TypeMemPtr)txs1.at("a");
//    assertEquals(2,(int)ds2.get(txp2));
//    TypeStruct txs2 = txp2._obj;
//    assertEquals(CUTOFF-1,(int)ds2.get(txs2));
//    assertEquals(Type.SCALAR,txs2.at("b"));
//    Type txp3 = txs2.at("a");
//    // Pointer-equals; 'equals()' is not good enough
//    assertSame(txp2, txp3);
//    assertSame(txs2, ((TypeMemPtr)txp3)._obj);
//    assertTrue(t3.isa(tax));
//
//    // Add another layer, and approx again
//    TypeStruct t4 = TypeStruct.make(TypeFld.make("a",pax), TypeFld.make("b",TypeInt.con(97)));
//    TypeMemPtr p4 = TypeMemPtr.make(alias0,t4);
//    ds = p4.depth();
//    assertEquals(CUTOFF,(int)ds.get(txs2)); // Structure too deep
//    TypeStruct tax4 = t4.approx(alias);
//    TypeMemPtr pax4 = TypeMemPtr.make(alias0,tax4);
//
//    ds2 = pax4.depth();
//    assertEquals(CUTOFF-1,p3.max(ds2));
//    TypeMemPtr t4p1 = (TypeMemPtr)tax4.at("a");
//    assertEquals(1,(int)ds2.get(t4p1));
//    TypeStruct t4s1 = t4p1._obj;
//    assertEquals(1,(int)ds2.get(t4s1));
//    TypeMemPtr t4p2 = (TypeMemPtr)t4s1.at("a");
//    assertEquals(2,(int)ds2.get(t4p2));
//    TypeStruct t4s2 = t4p2._obj;
//    assertEquals(CUTOFF-1,(int)ds2.get(t4s2));
//    assertEquals(Type.SCALAR,t4s2.at("b"));
//    Type t4p3 = t4s2.at("a");
//    assertEquals(2,(int)ds2.get(t4p3));
//    assertEquals(t4s2,((TypeMemPtr)t4p3)._obj);
//    assertTrue(t4.isa(tax4));
//  }
//
//  // Interleaving unrelated type X, and approximating type A which is too deep.
//  // A0 -> (X0 <-> X1) -> A1 -> X2 -> A2 -> (X3 <-> X4 ) -> A3 -> X5
//  // Approx:
//  // A0 -> (X0 <-> X1) -> A1 -> X2 -> A23-> (X35<-> X45) -> A23
//  @Ignore
//  @Test public void testApprox3() {
//    int alias0 = BitsAlias.new_alias(BitsAlias.ALLX);
//    int alias1 = BitsAlias.new_alias(BitsAlias.ALLX);
//
//    // ......................................................... -> X5
//    Type str_x5 = TypeInt.con(55);
//    TypeStruct  x5 = TypeStruct.make(TypeFld.make("v",str_x5   ),
//                                     TypeFld.make("x",Type.NIL),
//                                     TypeFld.make("a",Type.NIL));
//    TypeMemPtr px5 = TypeMemPtr.make(alias1,x5);
//
//    // ................................................... -> A3 -> X5
//    TypeInt str_a3 = TypeInt.con(3);
//    TypeStruct  a3 = TypeStruct.make(TypeFld.make("v",str_a3),
//                                     TypeFld.make("x",px5   ));
//    TypeMemPtr pa3 = TypeMemPtr.make(alias0,a3);
//
//    // Build two structs pointing to each other
//    // ...................................... (X3 <-> X4 ) -> A3 -> X5
//    Type i13 = TypeInt.con(33);
//    Type i14 = TypeInt.con(44);
//    TypeFld fi13 = TypeFld.make("v",i13);
//    TypeFld fi14 = TypeFld.make("v",i14);
//    TypeFld fpa3 = TypeFld.make("a",pa3);
//    Type.RECURSIVE_MEET++;
//    TypeStruct x3 = TypeStruct.malloc_test(fi13,TypeFld.malloc("x"),fpa3);
//    TypeStruct x4 = TypeStruct.malloc_test(fi14,TypeFld.malloc("x"),fpa3);
//    TypeMemPtr px3 = TypeMemPtr.make(alias1,x3);
//    TypeMemPtr px4 = TypeMemPtr.make(alias1,x4);
//    x3.get("x").setX(px4);
//    x4.get("x").setX(px3);
//    Type.RECURSIVE_MEET--;
//    x3 = Cyclic.install(x3);
//    px3 = (TypeMemPtr)x4.at("x");
//
//    // ................................ A2 -> (X3 <-> X4 ) -> A3 -> X5
//    TypeInt str_a2 = TypeInt.con(2);
//    TypeStruct  a2 = TypeStruct.make(TypeFld.make("v",str_a2),
//                                     TypeFld.make("x",px3   ));
//    TypeMemPtr pa2 = TypeMemPtr.make(alias0,a2);
//
//    // Check sanity
//    HashMap<Type,Integer> depths = pa2.depth();
//    int maxd = pa2.max(depths);
//    assertEquals(1,maxd);
//    assertEquals(1,(int)depths.get(a3));
//
//    // .......................... X2 -> A2 -> (X3 <-> X4 ) -> A3 -> X5
//    TypeStruct  x2 = TypeStruct.make(TypeFld.make("v",TypeInt.con(22)),
//                                     TypeFld.make("x",Type.NIL),
//                                     TypeFld.make("a",pa2));
//    TypeMemPtr px2 = TypeMemPtr.make(alias1,x2);
//
//    // .................... A1 -> X2 -> A2 -> (X3 <-> X4 ) -> A3 -> X5
//    TypeStruct  a1 = TypeStruct.make(TypeFld.make("v",TypeInt.con(1)),
//                                     TypeFld.make("x",px2));
//    TypeMemPtr pa1 = TypeMemPtr.make(alias0,a1);
//
//    // Build two structs pointing to each other
//    // ..... (X0 <-> X1) -> A1 -> X2 -> A2 -> (X3 <-> X4 ) -> A3 -> X5
//    Type i10 = TypeInt.con(-100);
//    Type i11 = TypeInt.con(11);
//    TypeFld fil0 = TypeFld.make("v",i10);
//    TypeFld fil1 = TypeFld.make("v",i11);
//    TypeFld fpa1 = TypeFld.make("a",pa1);
//    Type.RECURSIVE_MEET++;
//    TypeStruct x0 = TypeStruct.malloc_test(fil0, TypeFld.malloc("x"), fpa1);
//    TypeStruct x1 = TypeStruct.malloc_test(fil1, TypeFld.malloc("x"), fpa1);
//    TypeMemPtr px0 = TypeMemPtr.make(alias1,x0);
//    TypeMemPtr px1 = TypeMemPtr.make(alias1,x1);
//    x0.get("x").setX(px1);
//    x1.get("x").setX(px0);
//    Type.RECURSIVE_MEET--;
//    x0 = Cyclic.install(x0);
//    px0 = (TypeMemPtr)x1.at("x");
//
//    // A0 -> (X0 <-> X1) -> A1 -> X2 -> A2 -> (X3 <-> X4 ) -> A3 -> X5
//    TypeStruct  a0 = TypeStruct.make(TypeFld.make("v",TypeInt.con(-101)),
//                                     TypeFld.make("x",px0));
//    TypeMemPtr pa0 = TypeMemPtr.make(alias0,a0);
//
//    // Check sanity
//    depths = pa0.depth();
//    assertEquals(0,(int)depths.get(a0));
//    assertEquals(1,(int)depths.get(a1));
//    assertEquals(2,(int)depths.get(a2));
//    assertEquals(3,(int)depths.get(a3));
//    assertEquals(3,pa0.max(depths));
//
//    // Approximate
//    TypeStruct  zsa0 = a0.approx(BitsAlias.make0(alias0));
//    TypeMemPtr pzsa0 = TypeMemPtr.make(alias0,zsa0);
//
//    // Check sanity!
//    // Was: A0 -> (X0 <-> X1) -> A1 -> X2 -> A2 -> (X3 <->  X4) -> A3 -> X5
//    // Apx: A0 -> (X0 <-> X1) -> A1 -> X2 -> A23->  X35 -> (X4 <-> X3) -> A23
//    assertSame(TypeInt.con(-101), zsa0.at("v"));
//    TypeMemPtr zpx0 = (TypeMemPtr)zsa0.at("x");
//
//    TypeStruct zsx0 =             zpx0._obj;
//    assertSame  (i10 ,            zsx0.at("v"));
//    TypeMemPtr zpx1 = (TypeMemPtr)zsx0.at("x");
//    TypeMemPtr zpa1 = (TypeMemPtr)zsx0.at("a");
//
//    TypeStruct zsx1 =             zpx1._obj;
//    assertSame  (i11 ,            zsx1.at("v"));
//    assertSame  (zpx0,            zsx1.at("x"));
//    assertSame  (zpa1,            zsx1.at("a"));
//
//    TypeStruct zsa1 =             zpa1._obj;
//    assertSame(TypeInt.con(1),    zsa1.at("v"));
//    TypeMemPtr zpx2 = (TypeMemPtr)zsa1.at("x");
//
//    TypeStruct zsx2 =             zpx2._obj;
//    assertSame(TypeInt.con(22),   zsx2.at("v"));
//    assertSame(Type.NIL,          zsx2.at("x"));
//    TypeMemPtr zpa23= (TypeMemPtr)zsx2.at("a");
//
//    TypeStruct zsa23=             zpa23._obj;
//    assertSame(TypeInt.NINT8,     zsa23.at("v"));
//    TypeMemPtr zpx35= (TypeMemPtr)zsa23.at("x");
//
//    TypeStruct zsx35=             zpx35._obj;
//    assertSame(TypeInt.NINT8,     zsx35.at("v"));
//    TypeMemPtr zpa4 = (TypeMemPtr)zsx35.at("x") ;
//    TypeMemPtr zpa23q= (TypeMemPtr)zsx35.at("a") ;
//    // Weakened expected results after NIL expands to [0]->obj
//    assertSame(zsa23,             zpa23q._obj);
//    //assertSame(TypeStruct.ISUSED, zpa23q._obj);
//    TypeStruct zsx4 =             zpa4._obj;
//    assertSame(i14,               zsx4.at("v"));
//    assertSame(zpx35,             zsx4.at("x"));
//    assertSame(zpa23,             zsx4.at("a"));
//
//    depths = pzsa0.depth();
//    assertEquals(0,(int)depths.get(zsa0));
//    assertEquals(1,(int)depths.get(zsa1));
//    assertEquals(2,(int)depths.get(zsa23));
//    assertEquals(2,pa0.max(depths));
//    assertTrue(a0.isa(zsa0));
//  }
//
//
//  // Type A expands tree-like and gets too deep.
//  // A1 -> A2 -> A4
//  //          -> A5
//  //       A3 -> A6
//  //          -> A7
//  // And then:
//  // A1 -> A2 -> A4 -> A8
//  // A1 -> A2 -> A4 -> A9
//  // A1 -> A2 -> A5 -> A10
//  // A1 -> A2 -> A6 -> A12
//  // Approx:
//  // A1 -> A2 -> A4.8.9      A1.l -> A2.l ->   (nint8, T?, T?)
//  //          -> A5.10               A2.r -> T:(nint8, T?, nil)
//  //       A3 -> A6.12       A1.r -> A3.l -> T
//  //          -> A7               -> A3.r -> (nint8, nil, nil)
//  // ... and so forth.
//  // The first few tree layers remain expanded, but the tree tail collapses.
//  @Ignore
//  @Test public void testApprox4() {
//    final int CUTOFF = 3;
//    int alias = BitsAlias.new_alias(BitsAlias.ALLX);
//    TypeFld lnil = TypeFld.make("l",Type.NIL);
//    TypeFld rnil = TypeFld.make("r",Type.NIL);
//
//    TypeStruct  x12= TypeStruct.make(TypeFld.make("v",TypeInt.con(12)),lnil,rnil);
//    TypeMemPtr px12= TypeMemPtr.make(alias,x12);
//
//    TypeStruct  x10= TypeStruct.make(TypeFld.make("v",TypeInt.con(10)),lnil,rnil);
//    TypeMemPtr px10= TypeMemPtr.make(alias,x10);
//
//    TypeStruct  x9 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 9)),lnil,rnil);
//    TypeMemPtr px9 = TypeMemPtr.make(alias,x9 );
//
//    TypeStruct  x8 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 8)),lnil,rnil);
//    TypeMemPtr px8 = TypeMemPtr.make(alias,x8 );
//
//    TypeStruct  x7 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 7)),lnil,rnil);
//    TypeMemPtr px7 = TypeMemPtr.make(alias,x7 );
//
//    TypeStruct  x6 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 6)),TypeFld.make("l",px12),rnil);
//    TypeMemPtr px6 = TypeMemPtr.make(alias,x6 );
//
//    TypeStruct  x5 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 5)),TypeFld.make("l",px10),rnil);
//    TypeMemPtr px5 = TypeMemPtr.make(alias,x5 );
//
//    TypeStruct  x4 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 4)),TypeFld.make("l",px8 ),TypeFld.make("r",px9) );
//    TypeMemPtr px4 = TypeMemPtr.make(alias,x4 );
//
//    TypeStruct  x3 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 3)),TypeFld.make("l",px6 ),TypeFld.make("r",px7) );
//    TypeMemPtr px3 = TypeMemPtr.make(alias,x3 );
//
//    TypeStruct  x2 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 2)),TypeFld.make("l",px4 ),TypeFld.make("r",px5) );
//    TypeMemPtr px2 = TypeMemPtr.make(alias,x2 );
//
//    TypeStruct  x1 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 1)),TypeFld.make("l",px2 ),TypeFld.make("r",px3) );
//    TypeMemPtr px1 = TypeMemPtr.make(alias,x1 );
//
//    // Check sanity
//    HashMap<Type,Integer> depths = px1.depth();
//    assertEquals(0,(int)depths.get(x1));
//    assertEquals(1,(int)depths.get(x2));
//    assertEquals(1,(int)depths.get(x3));
//    assertEquals(2,(int)depths.get(x4));
//    assertEquals(2,(int)depths.get(x5));
//    assertEquals(2,(int)depths.get(x6));
//    assertEquals(2,(int)depths.get(x7));
//    assertEquals(3,(int)depths.get(x8));
//    assertEquals(3,(int)depths.get(x9));
//    assertEquals(3,(int)depths.get(x10));
//    assertEquals(3,(int)depths.get(x12));
//    assertEquals(3,px1.max(depths));
//
//    // Approximate
//    TypeStruct z1 = x1.approx(BitsAlias.make0(alias));
//    TypeMemPtr pz1 = TypeMemPtr.make(alias,z1);
//    assertSame( TypeInt.con(1), z1.at("v"));
//    TypeMemPtr p2 = (TypeMemPtr)z1.at("l") ;
//    TypeMemPtr p3 = (TypeMemPtr)z1.at("r") ;
//
//    TypeStruct z2 =             p2._obj   ;
//    assertSame( TypeInt.con(2), z2.at("v"));
//    TypeMemPtr p4 = (TypeMemPtr)z2.at("l") ;
//    TypeMemPtr p5 = (TypeMemPtr)z2.at("r") ;
//
//    TypeStruct z3 =             p3._obj   ;
//    assertSame( TypeInt.con(3), z3.at("v"));
//    TypeMemPtr p6 = (TypeMemPtr)z3.at("l") ;
//    TypeMemPtr p7 = (TypeMemPtr)z3.at("r") ;
//
//    check_leaf(p4,alias,TypeInt.NINT8);
//    check_leaf(p5,alias,TypeInt.NINT8);
//    check_leaf(p6,alias,TypeInt.NINT8);
//    check_leaf(p7,alias,TypeInt.con(7));
//
//    depths = pz1.depth();
//    assertEquals(2,px1.max(depths));
//  }
//
//  // Leaf is a TypeInt.NINT8, and both pointer fields are either NIL or contain
//  // alias 8 (and optionally nil) and point to a leaf type.
//  private void check_leaf( TypeMemPtr p, int alias, TypeInt vt ) {
//    TypeStruct z = p._obj;
//    assertSame( vt, z.at("v"));
//    Type x1 = z.at("l");
//    if( x1 != Type.NIL && x1!=Type.SCALAR) {
//      TypeMemPtr px = (TypeMemPtr) x1;
//      assertTrue(px._aliases.test(alias));
//    }
//    Type x2 = z.at("r");
//    if( x2 != Type.NIL && x2!=Type.SCALAR ) {
//      TypeMemPtr px = (TypeMemPtr)x2;
//      assertTrue(px._aliases.test(alias));
//    }
//  }
//
//  // Type A expands tree-like and gets too deep; CUTOFF=2
//  // A1 -> {l=S ,r=S ,v} depth=1
//  // A2 -> {l=A1,r=S ,v} depth=2
//  // A3 -> {l=A1,r=A1,v} depth=2
//  // A4 -> {l=A2,r=A3,v} depth=3
//  // Should approx to:
//  // Z1 -> {l=A1,r=A1,v} depth=2, and Z1=A3
//  @Ignore
//  @Test public void testApprox5() {
//    final int CUTOFF = 2;
//    int alias = BitsAlias.new_alias(BitsAlias.ALLX);
//
//    TypeStruct  x1= TypeStruct.make(TypeFld.make("l",Type.SCALAR),TypeFld.make("r",Type.SCALAR));
//    TypeMemPtr px1= TypeMemPtr.make(alias,x1);
//    assertEquals(0,px1.max(px1.depth()));
//
//    TypeStruct  x2= TypeStruct.make(TypeFld.make("l",   px1     ),TypeFld.make("r",Type.SCALAR));
//    TypeMemPtr px2= TypeMemPtr.make(alias,x2);
//    assertEquals(1,px1.max(px2.depth()));
//
//    TypeStruct  x3= TypeStruct.make(TypeFld.make("l",   px1     ),TypeFld.make("r",     px1   ));
//    TypeMemPtr px3= TypeMemPtr.make(alias,x3);
//    assertEquals(1,px1.max(px3.depth()));
//
//    TypeStruct  x4= TypeStruct.make(TypeFld.make("l",   px2     ),TypeFld.make("r",     px3   ));
//    TypeMemPtr px4= TypeMemPtr.make(alias,x4);
//    assertEquals(2,px1.max(px4.depth()));
//
//    // Approximate
//    TypeStruct z1 = x4.approx(BitsAlias.make0(alias));
//    TypeMemPtr pz1 = TypeMemPtr.make(alias,z1);
//    assertEquals(1,pz1.max(pz1.depth()));
//    assertSame(x3,z1);
//  }
//
//  // Type A expands tree-like and gets too deep; CUTOFF=2
//  // A1[0,18] -> {l=0 ,r=A1,v} depth=1, cyclic
//  // A2[0,18] -> {l=A1,r=A1,v} depth=2, not cyclic
//  //             {l=A1,r=A2,v} depth=3, not cyclic
//  // Should approx to:
//  // A3[0,18] -> {l=A3,r=A3,v} depth=1, cyclic
//  //             {l=A1,r=A3,v} depth=2
//  @Ignore // invalid, after the change to approx
//  @Test public void testApprox6() {
//    Object dummy0 = TypeStruct.TYPES;
//    Object dummy1 = TypeMemPtr.TYPES;
//    final int CUTOFF = 2;
//    int alias = BitsAlias.new_alias(BitsAlias.ALLX);
//
//    Type.RECURSIVE_MEET++;
//    TypeStruct  x1 = TypeStruct.malloc_test(TypeFld.malloc("l"), TypeFld.malloc("r"), TypeFld.malloc("v"));
//    TypeMemPtr px1 = TypeMemPtr.make_nil(alias,x1);
//    x1.get("l").setX(Type.NIL   );
//    x1.get("r").setX(px1        );
//    x1.get("v").setX(Type.SCALAR);
//    Type.RECURSIVE_MEET--;
//    x1 = Cyclic.install(x1);
//    assertSame(px1,x1.at("r"));
//
//    TypeStruct  x2= TypeStruct.make(TypeFld.make("l",px1),TypeFld.make("r",px1),TypeFld.make("v",Type.SCALAR));
//    TypeMemPtr px2= TypeMemPtr.make_nil(alias,x2);
//
//    TypeStruct  z0= TypeStruct.make(TypeFld.make("l",px1),TypeFld.make("r",px2),TypeFld.make("v",Type.SCALAR));
//    // Approximate
//    TypeStruct z1 = z0.approx(BitsAlias.make0(alias));
//
//    //Type.RECURSIVE_MEET++;
//    //TypeStruct  x3 = TypeStruct.malloc_test(TypeFld.malloc("l"), TypeFld.malloc("r"), TypeFld.malloc("v"));
//    //TypeMemPtr px3 = TypeMemPtr.make_nil(alias,x3);
//    //x3.get("l").setX(px3);//TypeMemPtr.make_nil(alias,TypeStruct.OBJ);
//    //x3.get("r").setX(px3);
//    //x3.get("v").setX(Type.SCALAR);
//    //Type.RECURSIVE_MEET--;
//    //x3 = x3.install();
//    //px3 = (TypeMemPtr)x3.at("l");
//    TypeFld frs = TypeFld.make("r"), fvs = TypeFld.make("v");
//    TypeStruct axl = TypeStruct.make(TypeFld.make("l"),frs,fvs);
//    Type.RECURSIVE_MEET++;
//    TypeFld flx = TypeFld.malloc("l");
//    TypeStruct  axr = TypeStruct.malloc_test(flx,frs,fvs);
//    TypeMemPtr paxr = TypeMemPtr.make_nil(alias,axr);
//    flx.setX(paxr);
//    Type.RECURSIVE_MEET--;
//    axr = Cyclic.install(axr);
//    paxr = TypeMemPtr.make_nil(alias,axr);
//
//    TypeStruct x4= TypeStruct.make(TypeFld.make("l",TypeMemPtr.make_nil(alias,axl)),TypeFld.make("r",paxr),fvs);
//    assertSame(x4,z1);
//  }
//
//  // Regression test.  Verify that a closed DATA cycle in the Node graph makes
//  // a finite Type graph.  Basically, endless applying NewObj results to a
//  // NewObj (as happens when making simple cyclic structures via storing fields
//  // from one into the other) ends with a simple cyclic graph and not an
//  // endlessly growing or endlessly "ping ponging" result.
//  @Ignore
//  @Test public void testApprox7() {
//
//    // Make a short cycle using alias RECORD.  Repeated add instances & approx,
//    // until fixed point.
//    final int CUTOFF=3;
//    TypeStruct ts0 = TypeStruct.make(TypeFld.NO_DISP);
//    TypeMemPtr tmp0 = TypeMemPtr.make(BitsAlias.ALL0,ts0), tmp1=null;
//
//    int cnt=0;
//    while( tmp0 != tmp1 && cnt < 100 ) {
//      TypeStruct ts1 = TypeStruct.make(TypeFld.make("^",tmp1=tmp0));
//      TypeStruct ts1x = ts1.approx(BitsAlias.NALL);
//      // Extend with nil-or-not endlessly.
//      tmp0 = TypeMemPtr.make(BitsAlias.ALL0,ts1x);
//      cnt++;
//    }
//    // End result has no prefix, since NIL is allowed at every step.  i.e., we
//    // added NIL-or-ptr-to-self 3 times, which is exactly approximated by a
//    // tight loop with no prefix.
//    assertEquals(CUTOFF,cnt);
//
//
//    // Make some child aliases.
//    final int alias6 = BitsAlias.new_alias(BitsAlias.ALLX);
//    final int alias7 = BitsAlias.new_alias(BitsAlias.ALLX);
//    final int alias8 = BitsAlias.new_alias(BitsAlias.ALLX);
//    final BitsAlias ba6 = BitsAlias.make0(alias6);
//    final BitsAlias ba7 = BitsAlias.make0(alias7);
//    final BitsAlias ba8 = BitsAlias.make0(alias8);
//    final BitsAlias ba60 = ba6.meet_nil();
//    final BitsAlias ba70 = ba7.meet_nil();
//    final BitsAlias ba80 = ba8.meet_nil();
//
//    // Add a struct with alias6 & approx.  Expect no change, despite alias6
//    // being a child of RECORD.
//    TypeStruct ts6 = TypeStruct.make(TypeFld.make("^",tmp0));
//    TypeStruct ts6x = ts6.approx(ba6);
//    assertEquals(ts6,ts6x);
//    TypeMemPtr tmp6 = TypeMemPtr.make(ba60,ts6);
//    // Again with alias7
//    TypeStruct ts7 = TypeStruct.make(TypeFld.make("^",tmp6));
//    TypeStruct ts7x = ts7.approx(ba7);
//    assertEquals(ts7,ts7x);
//    TypeMemPtr tmp7 = TypeMemPtr.make(ba70,ts7);
//    // Again with alias8
//    TypeStruct ts8 = TypeStruct.make(TypeFld.make("^",tmp7));
//    TypeStruct ts8x = ts8.approx(ba8);
//    assertEquals(ts8,ts8x);
//
//
//    // Start with short cycle:
//    //  10_( 11_* );  11#2 -> 10
//    // Add this on top (alias#4 and#3 are children of #2):
//    //   12#4 -> 13; 13_( 17_*, 14_* );  14#3 -> 15;  15_( 16_*, 2.3 ); 16#4 -> 10;  17#5 -> 18; 18_(nil,1.2)
//    // Approx alias#4 should do nothing (only depth 2 for alias#4 till hit cycle).
//    // Then add it again & approx at depth 2 for alias#2.
//
//
//    // Start with: A -> A
//    // A is basic RECORD type, actually equal to TypeStruct.DISPLAY.
//    // B,C,D are child aliases of A and are alias6,7,8.
//    // D is a LHS end type: D -> (nil,88)
//    TypeStruct tsD = TypeStruct.make(TypeFld.NO_DISP, TypeFld.make_tup(TypeInt.con(88),ARG_IDX));
//    TypeMemPtr tmpD = TypeMemPtr.make(ba8,tsD); // Note not nil
//    // Add (alternating the repeating field left and right):
//    //   B1 = ( A , 99 )
//    TypeStruct tsB1 = TypeStruct.make(TypeFld.make("^",tmp0,DSP_IDX),TypeFld.make_tup(TypeInt.con(99),ARG_IDX));
//    assertEquals(tsB1,tsB1.approx(ba6));
//    TypeMemPtr tmpB1= TypeMemPtr.make(ba6,tsB1); // Note not nil
//    //   C1 = ( D , B1 )
//    TypeStruct tsC1 = TypeStruct.make(TypeFld.make("^",tmpD,DSP_IDX),TypeFld.make_tup(tmpB1,ARG_IDX));
//    assertEquals(tsC1,tsC1.approx(ba7));
//    TypeMemPtr tmpC1= TypeMemPtr.make(ba7,tsC1); // Note not nil
//
//    // Add repeatedly until stable:
//    //   B2 = ( C1, 99 )
//    //   C2 = ( D , B2 )
//    // This should approx by meeting a C with an A, which should drop off the
//    // RHS of the C.  The C LHS is a D, which again meets with A to finish the
//    // collapse.  Bug is that types flip-flop between 2 variants endlessly.
//    cnt = 0;  tmp1 = null;
//    while( tmpC1 != tmp1 && cnt < 100 ) {
//      tmp1 = tmpC1;
//      //   B2 = ( C1, 99 )
//      TypeStruct tsB2 = TypeStruct.make(TypeFld.make("^",tmpC1,DSP_IDX),TypeFld.make_tup(TypeInt.con(99),ARG_IDX));
//      TypeStruct tsB2x = tsB2.approx(ba6);
//      TypeMemPtr tmpB2= TypeMemPtr.make(ba6,tsB2x); // Note not nil
//
//      //   C2 = ( D , B2 )
//      TypeStruct tsC2 = TypeStruct.make(TypeFld.make("^",tmpD,DSP_IDX),TypeFld.make_tup(tmpB2,ARG_IDX));
//      TypeStruct tsC2x = tsC2.approx(ba7);
//      TypeMemPtr tmpC2= TypeMemPtr.make(ba7,tsC2x); // Note not nil
//      tmpC1 = tmpC2;
//      cnt++;
//    }
//    assertEquals(CUTOFF-1,cnt);
//  }
//
//  @Ignore
//  @Test public void testApprox8() {
//    Object dummy2 = Env.GVN;
//    final int CUTOFF=2;
//    final int fidx = BitsFun.new_fidx(1), fidx0 = BitsFun.new_fidx(fidx), fidx1 = BitsFun.new_fidx(fidx);
//    final BitsFun fidxs = BitsFun.make0(fidx0,fidx1).dual();
//    final int alias = BitsAlias.new_alias(BitsAlias.ALLX);
//
//    // Args for the forward-ref fib(^ ->Scalar).  This has to start as hi-args
//    // for this test, as the cyclic approx is supposed to be low - and it has
//    // args known post-parse but not pre-parse.
//    TypeStruct tfp0_args = TypeStruct.make("", true, TypeMemPtr.DISP_FLD);
//
//    TypeFunPtr tfp0 = TypeFunPtr.make(BitsFun.ANY0,2,TypeFunPtr.DISP.simple_ptr(),Type.SCALAR); // fib with generic display
//    TypeStruct dsp0 = TypeStruct.make(TypeMemPtr.DISP_FLD,TypeFld.make("fib",tfp0));// The display with weak fib-type
//    TypeMemPtr ptr0 = TypeMemPtr.make(alias,dsp0);
//    // Args for a strong fib: { ^:ptr0 x:int64 -> ~Scalar } // LOW
//    TypeStruct arg0 = TypeStruct.make(TypeFld.make("->",Type.SCALAR),
//                                      TypeFld.make("^",ptr0.simple_ptr()),
//                                      TypeFld.make("x",TypeInt.INT64));
//
//    TypeFunPtr tfp1 = TypeFunPtr.make(fidxs,2,ptr0.simple_ptr(),Type.SCALAR); // FIB with weak display
//    TypeStruct dsp1 = TypeStruct.make(TypeMemPtr.DISP_FLD,TypeFld.make("fib",tfp1)); // Display with stronger FIB-type
//    TypeMemPtr ptr1 = TypeMemPtr.make(alias,dsp1);
//    // Args for a strong fib: { ^:ptr x:int -> ~Scalar } // LOW.  Display still not recursive.
//    TypeStruct arg1 = TypeStruct.make(TypeFld.make("->",Type.SCALAR),
//                                      TypeFld.make("^",ptr1.simple_ptr()),
//                                      TypeFld.make("x",TypeInt.INT64));
//
//    TypeFunPtr tfp2 = TypeFunPtr.make(fidxs,2,ptr1.simple_ptr(),Type.SCALAR); // fib2->dsp1->fib1->dsp0->fib0->generic_display
//    TypeStruct dsp2 = TypeStruct.make(TypeMemPtr.DISP_FLD,TypeFld.make("fib",tfp2)); // dsp2->fib2->dsp1->fib1->dsp0->fib0->generic_display
//
//    // The approx that gets built: fib3->dsp3->fib3->dsp3->...
//    Type.RECURSIVE_MEET++;
//    TypeStruct dsp3 = TypeStruct.malloc_test(TypeFld.malloc("^",null, TypeFld.Access.Final,DSP_IDX), TypeFld.malloc("fib"));
//    TypeMemPtr ptr3 = TypeMemPtr.make(alias,dsp3);
//    TypeStruct arg3 = TypeStruct.make(TypeFld.make("->",Type.SCALAR),
//                                      TypeFld.make("^",ptr3.simple_ptr()),
//                                      TypeFld.make("x",TypeInt.INT64));
//    TypeFunPtr tfp3 = TypeFunPtr.make(fidxs,2,ptr3.simple_ptr(),Type.SCALAR);
//    dsp3.get("^").setX(TypeMemPtr.DISPLAY_PTR);
//    dsp3.get("fib").setX(tfp3);
//    Type.RECURSIVE_MEET--;
//    dsp3 = Cyclic.install(dsp3);
//
//    // This should pass an isa-test (was crashing)
//    Type mt0 = dsp0.meet(dsp3);
//
//    // This should pass an isa-test (was crashing)
//    Type mt1 = dsp1.meet(dsp3);
//
//    // Check the isa
//    Type mt = dsp2.meet(dsp3);
//    assertEquals(dsp3,mt);
//
//    // Build the approx
//    TypeStruct rez = dsp2.approx(BitsAlias.make0(alias));
//    assertEquals(dsp3,rez);
//  }
//
//
//  // Regression test from TestHM.test58; both HM and GCP, rseed==0; Asserts
//  // doing a complex approx call that "!this.isa(rez)"; the returned type is
//  // not isa the 'this' type.  This looks like: "this.meet(rez)" does not
//  // minimize cycles properly, and this ISA rez but the standard isa test fails
//  // because "this.meet(rez)" is not minimized properly.
//  @Test public void testApprox9() {
//    Object dummy0 = TypeStruct.TYPES;
//
//    int alias13 = BitsAlias.new_alias(BitsAlias.ALLX);
//    int alias14 = BitsAlias.new_alias(BitsAlias.ALLX);
//    BitsAlias a14   = BitsAlias.ALL0.make(        alias14);
//    BitsAlias a1314 = BitsAlias.ALL0.make(alias13,alias14);
//    int fidx14 = BitsFun.new_fidx();
//    int fidx25 = BitsFun.new_fidx();
//    BitsFun f1425 = BitsFun.make0(fidx14,fidx25);
//    int fidx22 = BitsFun.new_fidx();
//    int fidx26 = BitsFun.new_fidx();
//    BitsFun f2226 = BitsFun.make0(fidx22,fidx26);
//
//    //REZ (shortened); result of approx, alias=14, depth=1
//    //C:@{
//    //  pred  =[14,25]{any ->*[13,14]C$ };
//    //  succ  =[22,26]{any ->*[   14]C$ }
//    //}
//    TypeStruct rez;
//    {
//      Type.RECURSIVE_MEET++;
//      TypeFld pred = TypeFld.malloc("pred");
//      TypeFld succ = TypeFld.malloc("succ");
//      rez = TypeStruct.make(pred,succ);
//      _help0(pred,f1425,a1314,rez);
//      _help0(succ,f2226,a14  ,rez);
//      Type.RECURSIVE_MEET--;
//      rez = Cyclic.install(rez);
//    }
//
//    TypeStruct thismeetrez;
//    {
//      Type.RECURSIVE_MEET++;
//      TypeFld pred2 = TypeFld.malloc("pred");
//      TypeFld succ1 = TypeFld.malloc("succ");
//      TypeStruct str1 = TypeStruct.make(rez.get("pred"),succ1);
//      TypeStruct str2 = TypeStruct.make(pred2,rez.get("succ"));
//      _help0(pred2,f1425,a1314,str1);
//      _help0(succ1,f2226,a14  ,str2);
//      Type.RECURSIVE_MEET--;
//      thismeetrez = Cyclic.install(str2);
//    }
//
//    // Install shrinks
//    assertEquals(rez,thismeetrez);
//  }
//
//  // Make the field point at the struct
//  private static void _help0( TypeFld fld, BitsFun fidx, BitsAlias alias, TypeStruct rez ) {
//    TypeMemPtr ptr = TypeMemPtr.make(alias,rez);
//    fld.setX(TypeFunPtr.make(fidx,1,TypeMemPtr.NO_DISP,ptr));
//  }
//
//
//  // The following case the tstr0 >> tstr1, BUT !(tstr0.apx >. tstr1.apx)
//  @Ignore
//  @Test public void testApprox10() {
//    Object dummy0 = TypeStruct.TYPES;
//
//    BitsAlias a6 = BitsAlias.make0(BitsAlias.new_alias());
//    BitsFun f16 = BitsFun.make_new_fidx(BitsFun.ALLX);
//    BitsFun f17 = BitsFun.make_new_fidx(BitsFun.ALLX);
//    BitsFun f18 = BitsFun.make_new_fidx(BitsFun.ALLX);
//    BitsFun f19 = BitsFun.make_new_fidx(BitsFun.ALLX);
//
//    TypeFld fand = TypeFld.make("and",TypeFunPtr.make(f16,1,TypeMemPtr.NO_DISP,Type.SCALAR));
//    TypeFld fthn = TypeFld.make("thn",TypeFunPtr.make(f19,2,TypeMemPtr.NO_DISP,Type.SCALAR));
//    TypeFld fthx = TypeFld.make("thn",TypeFunPtr.make(f19,2,TypeMemPtr.NO_DISP,Type.XSCALAR));
//    Type.RECURSIVE_MEET++;
//    TypeFld fnot0 = TypeFld.malloc("not");
//    TypeFld ffor0 = TypeFld.malloc("or_");
//
//    TypeFld fnot1 = TypeFld.malloc("not");
//    TypeFld ffor1 = TypeFld.malloc("or_");
//
//    TypeStruct sa2 = TypeStruct.make(TypeFld.NO_DISP,fand,fnot1,ffor1,fthx);
//    _help0(fnot1,f18,a6,sa2);
//    _help0(ffor1,f17,a6,sa2);
//
//    TypeStruct sa1 = TypeStruct.make(TypeFld.NO_DISP,fand,fnot1,ffor1,fthn);
//    _help0(ffor0,f17,a6,sa1);
//
//    TypeStruct sa0 = TypeStruct.make(TypeFld.NO_DISP,fand,fnot0,ffor0,fthn);
//    _help0(fnot0,f18,a6,sa0);
//    Type.RECURSIVE_MEET--;
//    sa0 = Cyclic.install(sa0);
//
//    TypeStruct apx = sa0.approx(a6);
//    assertTrue(sa0.isa(apx));
//  }
//
////@{ f0=~Scalar,
////   f1=*[2]@{
////     f0=3,
////     f1=*[2]@{f0=3, f1=~Scalar}
////   }
////}
////
//  @Ignore
//  @Test public void testApprox11() {
//    Object dummy0 = TypeStruct.TYPES;
//
//    BitsAlias a2 = BitsAlias.make0(BitsAlias.new_alias());
//
//    TypeFld    f0c = TypeFld.make("f0",TypeInt.con(3));
//    TypeFld    f1x = TypeFld.make("f1",Type.XSCALAR);
//    TypeStruct s2  = TypeStruct.make(f0c,f1x);
//
//    TypeFld    f1p = TypeFld.make("f1",TypeMemPtr.make(a2,s2));
//    TypeStruct s1  = TypeStruct.make(f0c,f1x);
//
//    TypeFld    f0x = TypeFld.make("f0",Type.XSCALAR);
//    TypeFld    f1q = TypeFld.make("f1",TypeMemPtr.make(a2,s1));
//    TypeStruct s0  = TypeStruct.make(f0x,f1q);
//
//    TypeStruct apx = s0.approx(a2);
//    assertTrue(s0.isa(apx));
//  }
//
//  @Ignore
//  @Test public void testRegression1() {
//    int a6 = BitsAlias.new_alias();
//    TypeFld FG = TypeFld.make("or_",TypeFunPtr.make(17,1,Type.ANY,Type.XSCALAR));
//    Type.RECURSIVE_MEET++;
//    TypeFld FF = TypeFld.malloc("not");
//    TypeFld FO = TypeFld.malloc("or_");
//    TypeStruct SB = TypeStruct.malloc_test(FO,FF);
//    TypeMemPtr PB = TypeMemPtr.make(a6,SB);
//    FO.setX(TypeFunPtr.make(17,1,Type.ANY,PB));
//    FF.setX(TypeFunPtr.make(18,1,Type.ANY,PB));
//    Type.RECURSIVE_MEET--;
//    Cyclic.install(SB);
//
//    Type.RECURSIVE_MEET++;
//    TypeFld FC = TypeFld.malloc("not");
//    TypeStruct SA = TypeStruct.malloc_test(FG,FC);
//    TypeMemPtr PA = TypeMemPtr.make(a6,SA);
//    FC.setX(TypeFunPtr.make(18,1,Type.ANY,PA));
//    Type.RECURSIVE_MEET--;
//    Cyclic.install(SA);
//
//    TypeFld FE = TypeFld.make("or_",TypeFunPtr.make(17,1,Type.ANY,PA));
//    TypeMemPtr PN = TypeMemPtr.make(a6,TypeStruct.make(FE,FF));
//    TypeFld FN = TypeFld.make("not",TypeFunPtr.make(18,1,Type.ANY,PN));
//    TypeMemPtr PM = TypeMemPtr.make(a6,TypeStruct.make(FE,FC));
//    TypeFld FM = TypeFld.make("or_",TypeFunPtr.make(17,1,Type.ANY,PM));
//    TypeMemPtr PZ = TypeMemPtr.make(a6,TypeStruct.make(FM,FN));
//
//    TypeStruct apx = PZ._obj.approx(PZ._aliases);
//    assertTrue(PZ._obj.isa(apx));
//  }
//
//
//  // Make a psuedo-random selection of types, and verify that approx is
//  // monotonic.
//  private static final long RSEED = 1234L;
//  private static final int NRAND = 199;      // Number of random types.  Raise this to test more.
//  private static final int NSTRUCTS = 3;     // Number of structs per type.  Raise this to test larger type nests
//  @Ignore
//  @Test public void testApproxRand() {
//    Object dummy = TypeMemPtr.TYPES; // <clinit> before RECURSIVE_MEET
//
//    final Random R=new Random(RSEED);
//
//    int a0 = BitsAlias.new_alias();
//    int a1 = BitsAlias.new_alias();
//    int f0 = BitsFun.new_fidx();
//    int f1 = BitsFun.new_fidx();
//    // Pre-build some random small integers
//    for( int i=0; i<10; i++ ) TypeInt.con(i);
//
//    // Make NRAND random types, without dups
//    TypeStruct[] ts = new TypeStruct[NRAND];
//    for( int i=0; i<NRAND; i++ ) {
//      ts[i] = make_rand(R,a0,a1,f0,f1);
//      for( int j=0; j<i; j++ ) if( ts[j]==ts[i] ) { i--; break; } // Dup, try again
//    }
//
//    // Make NRAND approximation types
//    TypeStruct[] ax1s = new TypeStruct[NRAND];
//    for( int i=0; i<NRAND; i++ ) {
//      ax1s[i] = ts[i].approx(BitsAlias.make0(a0));
//      if( ax1s[i]==null ) continue;
//      assertTrue(ts[i].isa(ax1s[i])); // Verify self-monotonic
//    }
//
//    int cnt=0, ecnt=0;
//    for( int i=0; i<NRAND; i++ ) {
//      if( ax1s[i]==null ) continue;
//      for( int j=0; j<i; j++ ) {
//        if( ax1s[j]==null ) continue;
//        Type mt = ts[i].meet(ts[j]);
//        if( mt==ts[i] ) ecnt = _check_apx( ax1s[j], ax1s[i], ecnt, cnt++, j, i );
//        if( mt==ts[j] ) ecnt = _check_apx( ax1s[i], ax1s[j], ecnt, cnt++, i, j );
//      }
//    }
//
//    assertTrue( cnt>0 ); // Nothing tested!
//    assertEquals(0, ecnt);
//  }
//
//  private static final Ary<TypeStruct> TSRANDS = new Ary<>(TypeStruct.class);
//  private static TypeStruct rand_struct( Random R) { return TSRANDS.at(R.nextInt(TSRANDS.len())); }
//  private static TypeMemPtr rand_tmp( int ax, Random R) { return TypeMemPtr.make(ax,rand_struct(R)); }
//
//  private static TypeStruct make_rand(Random R, int a0, int a1, int f0, int f1) {
//    TSRANDS.clear();
//    int nts = Math.min(NSTRUCTS,R.nextInt(NSTRUCTS)+R.nextInt(NSTRUCTS)+1); // random from 1-NSTRUCTS, but favoring larger counts
//    Type.RECURSIVE_MEET++;
//    for( int i=0; i<nts; i++ )
//      TSRANDS.push(TypeStruct.malloc_test(TypeFld.malloc("f0"),TypeFld.malloc("f1"),TypeFld.malloc("f2")));
//    for( int i=0; i<nts; i++ ) {
//      TypeStruct ts = TSRANDS.at(i);
//      ts._fld_idx(0).setX(_make_rand_fld(R,a0,a1,f0,f1,true));
//      ts._fld_idx(1).setX(_make_rand_fld(R,a0,a1,f0,f1,true));
//      ts._fld_idx(2).setX(_make_rand_fld(R,a0,a1,f0,f1,true));
//    }
//    Type.RECURSIVE_MEET--;
//    return Cyclic.install(TSRANDS.at(0));
//  }
//  private static Type _make_rand_fld(Random R, int a0, int a1, int f0, int f1, boolean fptrs) {
//    return switch( R.nextInt(fptrs ? 13 : 10) ) {
//    case  0 -> Type. SCALAR;
//    case  1 -> Type. NSCALR;
//    case  2 -> Type.XSCALAR;
//    case  3 -> Type.XNSCALR;
//    case  4 -> Type.XSCALAR;
//    case  5 -> Type.XNSCALR;
//    case  6 -> rand_tmp(a0,R);  // *[a0] rand
//    case  7 -> rand_tmp(a1,R);  // *[a1] rand
//    case  8 -> rand_tmp(a0,R).meet_nil(Type.NIL);  // *[0,a0] rand
//    case  9 -> rand_tmp(a1,R).meet_nil(Type.NIL);  // *[0,a1] rand
//    case 10 -> TypeFunPtr.make(f0,2, _make_rand_fld(R,a0,a1,f0,f1,false), _make_rand_fld(R,a0,a1,f0,f1,false));
//    case 11 -> TypeFunPtr.make(f1,2, _make_rand_fld(R,a0,a1,f0,f1,false), _make_rand_fld(R,a0,a1,f0,f1,false));
//    default -> TypeInt.con(2+R.nextInt(2));
//    };
//  }
//
//  private static int _check_apx( Type ax0, Type ax1, int ecnt, int ignore, int i, int j ) {
//    if( ax0.isa(ax1) )
//      return ecnt;
//    System.out.println("Failed approx for seeds "+i+" and "+j+", use testJig to repro");
//    System.out.println(ax0);
//    System.out.println("is not isa ");
//    System.out.println(ax1);
//    System.out.println();
//    return ecnt+1;
//  }
//
//  // Use this to make a quick test from the two failed test numbers given
//  @Ignore
//  @Test public void testJig() {
//    Object dummy = TypeMemPtr.TYPES; // <clinit> before RECURSIVE_MEET
//    Object dumm2 = TypeFunPtr.GENERIC_FUNPTR;
//    int a0 = BitsAlias.new_alias();
//    int a1 = BitsAlias.new_alias();
//    int f0 = BitsFun.new_fidx();
//    int f1 = BitsFun.new_fidx();
//    BitsAlias b0 = BitsAlias.make0(a0);
//    // Pre-build some random small integers
//    for( int k=0; k<10; k++ ) TypeInt.con(k);
//
//    final Random R=new Random(RSEED);
//    TypeStruct[] ts = new TypeStruct[NRAND];
//    for( int i=0; i<NRAND; i++ ) {
//      ts[i] = make_rand(R,a0,a1,f0,f1);
//      for( int j=0; j<i; j++ ) if( ts[j]==ts[i] ) { i--; break; } // Dup, try again
//    }
//
//    // HACK IN THE FAILED TEST NUMBERS HERE
//    TypeStruct ts0 = ts[39];
//    TypeStruct ts1 = ts[39];
//
//    TypeStruct ax1 = ts1.approx(b0);
//    TypeStruct ax0 = ts0.approx(b0);
//
//    assertTrue( ts0.isa(ts1) );
//    if( ax0!=null && ax1!=null ) {
//      assertTrue( ts0.isa(ax0) );
//      assertTrue( ts1.isa(ax1) );
//      assertTrue( ax0.isa(ax1) );
//    }
//
//    // Some regression tests, but dependent on the rand function
//    TypeStruct ts2 = ts[15];    // Problems with infinite growth
//    TypeStruct ax2 = ts2.approx(b0);
//
//    TypeStruct ts3 = ts[73];
//    TypeStruct ax3 = ts3.approx(b0);
//
//    TypeStruct ts4 = ts[154];
//    TypeStruct ts5 = ts[197];
//    ts4 = ts4.replace_fld(TypeFld.make("f1",TypeInt.con(4)));
//
//    TypeFld ts4_f0 = ts4.get("f0");
//    TypeMemPtr ts4_p0 = (TypeMemPtr)ts4_f0._t;
//    TypeStruct ts4_s0 = ts4_p0._obj;
//    ts4_s0 = ts4_s0.replace_fld(TypeFld.make("f1",TypeInt.con(5)));
//    ts4_p0 = ts4_p0.make_from(ts4_s0);
//    ts4 = ts4.replace_fld(TypeFld.make("f0",ts4_p0));
//
//    TypeStruct ax4 = ts4.approx(b0);
//    TypeStruct ax5 = ts5.approx(b0);
//
//    assertTrue( ts4.isa(ts5) );
//    assertTrue( ts4.isa(ax4) );
//    assertTrue( ts5.isa(ax5) );
//
//    assertTrue( ax4.isa(ax5) );
//  }
}
