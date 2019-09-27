package com.cliffc.aa.type;

import org.junit.Test;

import java.util.HashMap;

import static org.junit.Assert.*;


public class TestApprox {
  // temp/junk holder for "instant" junits, when debugged moved into other tests
  @Test public void testType() {
    Type.init0(new HashMap<>());
  }

  // Check TypeStruct.meet for a more complex recursive case
  @Test public void testTSMeet() {
    Type.init0(new HashMap<>());
    final int CUTOFF = 3;
    int alias0 = BitsAlias.new_alias(BitsAlias.REC);
    BitsAlias alias = BitsAlias.make0(alias0);
    String[] flds = new String[]{"a","b"};
    byte[] finals = new byte[]{1,1};

    // Build two structs pointing to each other.
    //   -> [,int] -> * -> [,flt] -> * ->
    Type.RECURSIVE_MEET++;
    TypeStruct t0 = TypeStruct.malloc(false,flds,new Type[2],finals,alias);
    TypeStruct t1 = TypeStruct.malloc(false,flds,new Type[2],finals,alias);
    t0._hash = t0.compute_hash();  t0._cyclic = true;
    t1._hash = t1.compute_hash();  t1._cyclic = true;
    TypeMemPtr p0 = TypeMemPtr.make(alias0,t0);  p0._cyclic = true;
    TypeMemPtr p1 = TypeMemPtr.make(alias0,t1);  p1._cyclic = true;
    t0._ts[0] = p1;
    t0._ts[1] = TypeInt.INT64;
    t1._ts[0] = p0;
    t1._ts[1] = TypeFlt.FLT64;
    Type.RECURSIVE_MEET--;
    t0 = t0.install_cyclic();
    t1 = t1.install_cyclic();

    // Meet them
    TypeStruct mt = (TypeStruct)t0.meet(t1);

    // End result should be a cycle of length 1: [,real] -> * ->
    // And NOT: [,real] -> * -> [,real] -> * ->
    assertEquals(Type.REAL,mt.at(1));
    TypeMemPtr pmt = (TypeMemPtr)mt.at(0);
    assertSame(mt,pmt._obj);
    TypeStruct head = mt.repeats_in_cycles();
    assertNull(head);
  }

  // Test approximating infinite recursive types.  Most simple test case: a
  // single linked-list chain of depth == CUTOFF.
  @Test public void testApprox1() {
    Type.init0(new HashMap<>());
    final int CUTOFF = 3;
    int alias0 = BitsAlias.new_alias(BitsAlias.REC);
    String[] flds = new String[]{"a","b"};
    byte[] finals = new byte[]{1,1};

    // Build a depth-CUTOFF linked list chain
    TypeStruct t0 = TypeStruct.make(flds,new Type[]{Type.NIL,TypeInt.con(99)},finals,alias0);
    TypeMemPtr p0 = TypeMemPtr.make(alias0,t0);
    HashMap<Type,Integer> ds = t0.depth(alias0);
    assertEquals(0,(int)ds.get(t0));

    TypeStruct t1 = TypeStruct.make(flds,new Type[]{p0,TypeInt.con(98)},finals,alias0);
    TypeMemPtr p1 = TypeMemPtr.make(alias0,t1);
    ds = t1.depth(alias0);
    assertEquals(1,(int)ds.get(t0));
    assertEquals(0,(int)ds.get(t1));
    assertEquals(1,(int)ds.get(p0));

    TypeStruct t2 = TypeStruct.make(flds,new Type[]{p1,TypeInt.con(97)},finals,alias0);
    TypeMemPtr p2 = TypeMemPtr.make(alias0,t2);
    ds = t2.depth(alias0);
    assertEquals(2,(int)ds.get(t0));

    TypeStruct t3 = TypeStruct.make(flds,new Type[]{p2,TypeInt.con(96)},finals,alias0);
    ds = t3.depth(alias0);
    assertEquals(CUTOFF  ,(int)ds.get(t0));
    assertEquals(CUTOFF-1,(int)ds.get(t1));
    assertEquals(1,(int)ds.get(t2));
    assertEquals(0,(int)ds.get(t3));
    // No single depth is beyond cutoff
    assertEquals(CUTOFF,TypeStruct.max(alias0,ds));

    // For all TypeStruct X at depth CUTOFF-1, make a clone of X and X's sub-
    // graph, except every edge to a type at depth CUTOFF is replaced with the
    // X clone.

    // original, too deep
    // t3[,99] -> p2 -> t2[,99] -> p1 -> t1[,flt] -> p0 -> t0[,int] -> nil

    // replace ptrs to t0 with ptrs to t1
    // t3[,99] -> p2 -> t2[,99] -> p1 -> t1[,flt] -> p0 -> t1*

    // collapse redundant ptrs to t1, and MEET t0-tail and t1-tail
    // t3[,99] -> p2 -> t2[,99] -> {p0,p1} -> t1[,{flt&int}] -> {p0,p1}

    TypeStruct tax = t3.approx(CUTOFF);
    HashMap<Type,Integer> ds2 = tax.depth(alias0);
    assertEquals(CUTOFF-1,TypeStruct.max(alias0,ds2));
    TypeMemPtr txp1 = (TypeMemPtr)tax.at(0);
    assertEquals(1,(int)ds2.get(txp1));
    TypeStruct txs1 = (TypeStruct)txp1._obj;
    assertEquals(1,(int)ds2.get(txs1));
    TypeMemPtr txp2 = (TypeMemPtr)txs1.at(0);
    assertEquals(2,(int)ds2.get(txp2));
    TypeStruct txs2 = (TypeStruct)txp2._obj;
    assertEquals(2,(int)ds2.get(txs2));
    assertEquals(TypeInt.NINT8,txs2.at(1));
    TypeMemPtr txp3 = (TypeMemPtr)txs2.at(0);
    assertEquals(3,(int)ds2.get(txp3));
    assertEquals(txs2,txp3._obj);

    assertTrue(t3.isa(tax));
  }

  // Test approximating infinite recursive types.  End of chain is already
  // cyclic, and we add a few more depth.
  @Test public void testApprox2() {
    Type.init0(new HashMap<>());
    final int CUTOFF = 3;
    int alias0 = BitsAlias.new_alias(BitsAlias.REC);
    BitsAlias alias = BitsAlias.make0(alias0);
    String[] flds = new String[]{"a","b"};
    byte[] finals = new byte[]{1,1};

    // p3 -> t3[,99] -> p2 -> t2[,99] -> p1 -> t1[,flt] -> p0 -> t0[,int] -> p1*

    // Build two structs pointing to each other
    Type.RECURSIVE_MEET++;
    TypeStruct t0 = TypeStruct.malloc(false,flds,new Type[2],finals,alias);
    TypeStruct t1 = TypeStruct.malloc(false,flds,new Type[2],finals,alias);
    t0._hash = t0.compute_hash();  t0._cyclic = true;
    t1._hash = t1.compute_hash();  t1._cyclic = true;
    TypeMemPtr p0 = TypeMemPtr.make(alias0,t0);  p0._cyclic = true;
    TypeMemPtr p1 = TypeMemPtr.make(alias0,t1);  p1._cyclic = true;
    t0._ts[0] = p1;
    t0._ts[1] = TypeInt.INT64;
    t1._ts[0] = p0;
    t1._ts[1] = TypeFlt.FLT64;
    Type.RECURSIVE_MEET--;
    t0 = t0.install_cyclic();
    t1 = t1.install_cyclic();
    p1 = (TypeMemPtr)t0._ts[0];
    p0 = (TypeMemPtr)t1._ts[0];

    HashMap<Type,Integer> ds = t1.depth(alias0);
    assertEquals(1,(int)ds.get(t0));
    assertEquals(0,(int)ds.get(t1));

    // Build a depth-CUTOFF linked list chain
    TypeStruct t2 = TypeStruct.make(flds,new Type[]{p1,TypeInt.con(99)},finals,alias0);
    TypeMemPtr p2 = TypeMemPtr.make(alias0,t2);
    ds = t2.depth(alias0);
    assertEquals(2,(int)ds.get(t0));

    TypeStruct t3 = TypeStruct.make(flds,new Type[]{p2,TypeInt.con(98)},finals,alias0);
    ds = t3.depth(alias0);
    assertEquals(CUTOFF  ,(int)ds.get(t0));
    assertEquals(CUTOFF-1,(int)ds.get(t1));
    assertEquals(1,(int)ds.get(t2));
    assertEquals(0,(int)ds.get(t3));
    // No single depth is beyond cutoff
    assertEquals(CUTOFF,TypeStruct.max(alias0,ds));

    // For all TypeStruct X at depth CUTOFF-1, make a clone of X and X's sub-
    // graph, except every edge to a type at depth CUTOFF is replaced with the
    // X clone.

    // original, too deep
    // t3[,98] -> p2 -> t2[,99] -> p1 -> t1[,flt] -> p0 -> t0[,int] -> p1*

    // replace ptrs to t0 with ptrs to t1
    // t3[,98] -> p2 -> t2[,99] -> p1 -> t1[,flt] -> p0 -> t1*

    // collapse redundant ptrs to t1, and MEET t0-tail and t1-tail
    // t3[,98] -> p2 -> t2[,99] -> {p0,p1} -> t1[,{flt&int}] -> {p0,p1}

    TypeStruct tax = t3.approx(CUTOFF);
    TypeMemPtr p3 = TypeMemPtr.make(alias0,tax);

    HashMap<Type,Integer> ds2 = tax.depth(alias0);
    assertEquals(CUTOFF-1,TypeStruct.max(alias0,ds2));
    TypeMemPtr txp1 = (TypeMemPtr)tax.at(0);
    assertEquals(1,(int)ds2.get(txp1));
    TypeStruct txs1 = (TypeStruct)txp1._obj;
    assertEquals(1,(int)ds2.get(txs1));
    TypeMemPtr txp2 = (TypeMemPtr)txs1.at(0);
    assertEquals(CUTOFF-1,(int)ds2.get(txp2));
    TypeStruct txs2 = (TypeStruct)txp2._obj;
    assertEquals(CUTOFF-1,(int)ds2.get(txs2));
    assertEquals(Type.REAL,txs2.at(1));
    TypeMemPtr txp3 = (TypeMemPtr)txs2.at(0);
    // Pointer-equals; 'equals()' is not good enough
    assertSame(txp2, txp3);
    assertSame(txs2, txp3._obj);
    assertTrue(t3.isa(tax));

    // Add another layer, and approx again
    TypeStruct t4 = TypeStruct.make(flds,new Type[]{p3,TypeInt.con(97)},finals,alias0);
    ds = t4.depth(alias0);
    assertEquals(CUTOFF,(int)ds.get(txs2)); // Structure too deep
    TypeStruct tax4 = t4.approx(CUTOFF);

    ds2 = tax4.depth(alias0);
    assertEquals(CUTOFF-1,TypeStruct.max(alias0,ds2));
    TypeMemPtr t4p1 = (TypeMemPtr)tax4.at(0);
    assertEquals(1,(int)ds2.get(t4p1));
    TypeStruct t4s1 = (TypeStruct)t4p1._obj;
    assertEquals(1,(int)ds2.get(t4s1));
    TypeMemPtr t4p2 = (TypeMemPtr)t4s1.at(0);
    assertEquals(CUTOFF-1,(int)ds2.get(t4p2));
    TypeStruct t4s2 = (TypeStruct)t4p2._obj;
    assertEquals(CUTOFF-1,(int)ds2.get(t4s2));
    assertEquals(Type.REAL,t4s2.at(1));
    TypeMemPtr t4p3 = (TypeMemPtr)t4s2.at(0);
    assertEquals(CUTOFF-1,(int)ds2.get(t4p3));
    assertEquals(t4s2,t4p3._obj);
    assertTrue(t4.isa(tax4));
  }

  // Interleaving unrelated type X, and approximating type A which is too deep.
  // A0 -> (X0 <-> X1) -> A1 -> X2 -> A2 -> (X3 <-> X4 ) -> A3 -> X5
  // Approx:
  // A0 -> (X0 <-> X1) -> A1 -> X2 -> A23-> (X35<-> X45) -> A23
  @Test public void testApprox3() {
    Type.init0(new HashMap<>());
    final int CUTOFF = 3;
    int alias0 = BitsAlias.new_alias(BitsAlias.REC);
    int alias1 = BitsAlias.new_alias(BitsAlias.REC);
    BitsAlias ba0 = BitsAlias.make0(alias0);
    BitsAlias ba1 = BitsAlias.make0(alias1);
    String[] flds2 = new String[]{"x","v"};
    String[] flds3 = new String[]{"a","x","v"};
    byte[] finals2 = new byte[]{1,1};
    byte[] finals3 = new byte[]{1,1,1};

    // ......................................................... -> X5
    TypeStruct  x5 = TypeStruct.make(flds3,new Type[]{Type.NIL,Type.NIL,TypeInt.con(15)},finals3,alias1);
    TypeMemPtr px5 = TypeMemPtr.make(alias1,x5);

    // ................................................... -> A3 -> X5
    TypeStruct  a3 = TypeStruct.make(flds2,new Type[]{px5,TypeInt.con(3)},finals2,alias0);
    TypeMemPtr pa3 = TypeMemPtr.make(alias0,a3);

    // Build two structs pointing to each other
    // ...................................... (X3 <-> X4 ) -> A3 -> X5
    Type i13 = TypeInt.con(13);
    Type i14 = TypeInt.con(14);
    Type.RECURSIVE_MEET++;
    TypeStruct x3 = TypeStruct.malloc(false,flds3,new Type[3],finals3,ba1);
    TypeStruct x4 = TypeStruct.malloc(false,flds3,new Type[3],finals3,ba1);
    x3._hash = x3.compute_hash();  x3._cyclic = true;
    x4._hash = x4.compute_hash();  x4._cyclic = true;
    TypeMemPtr px3 = TypeMemPtr.make(alias1,x3);  px3._cyclic = true;
    TypeMemPtr px4 = TypeMemPtr.make(alias1,x4);  px4._cyclic = true;
    x3._ts[0] = pa3;
    x3._ts[1] = px4;
    x3._ts[2] = i13;
    x4._ts[0] = pa3;
    x4._ts[1] = px3;
    x4._ts[2] = i14;
    Type.RECURSIVE_MEET--;
    x3 = x3.install_cyclic();
    x4 = x4.install_cyclic();
    px4 = (TypeMemPtr)x3._ts[1]; // Reload after cyclic install normalizes
    px3 = (TypeMemPtr)x4._ts[1];

    // ................................ A2 -> (X3 <-> X4 ) -> A3 -> X5
    TypeStruct  a2 = TypeStruct.make(flds2,new Type[]{px3,TypeInt.con(2)},finals2,alias0);
    TypeMemPtr pa2 = TypeMemPtr.make(alias0,a2);

    // Check sanity
    HashMap<Type,Integer> depths = a2.depth(alias0);
    int maxd = TypeStruct.max(alias0,depths);
    assertEquals(1,maxd);
    assertEquals(1,(int)depths.get(a3));

    // .......................... X2 -> A2 -> (X3 <-> X4 ) -> A3 -> X5
    TypeStruct  x2 = TypeStruct.make(flds3,new Type[]{pa2,Type.NIL,TypeInt.con(12)},finals3,alias1);
    TypeMemPtr px2 = TypeMemPtr.make(alias1,x2);

    // .................... A1 -> X2 -> A2 -> (X3 <-> X4 ) -> A3 -> X5
    TypeStruct  a1 = TypeStruct.make(flds2,new Type[]{px2,TypeInt.con(1)},finals2,alias0);
    TypeMemPtr pa1 = TypeMemPtr.make(alias0,a1);

    // Build two structs pointing to each other
    // ..... (X0 <-> X1) -> A1 -> X2 -> A2 -> (X3 <-> X4 ) -> A3 -> X5
    Type i10 = TypeInt.con(10);
    Type i11 = TypeInt.con(11);
    Type.RECURSIVE_MEET++;
    TypeStruct x0 = TypeStruct.malloc(false,flds3,new Type[3],finals3,ba1);
    TypeStruct x1 = TypeStruct.malloc(false,flds3,new Type[3],finals3,ba1);
    x0._hash = x0.compute_hash();  x0._cyclic = true;
    x1._hash = x1.compute_hash();  x1._cyclic = true;
    TypeMemPtr px0 = TypeMemPtr.make(alias1,x0);  px0._cyclic = true;
    TypeMemPtr px1 = TypeMemPtr.make(alias1,x1);  px1._cyclic = true;
    x0._ts[0] = pa1;
    x0._ts[1] = px1;
    x0._ts[2] = i10;
    x1._ts[0] = pa1;
    x1._ts[1] = px0;
    x1._ts[2] = i11;
    Type.RECURSIVE_MEET--;
    x0 = x0.install_cyclic();
    x1 = x1.install_cyclic();
    px1 = (TypeMemPtr)x0._ts[1]; // Reload after cyclic install normalizes
    px0 = (TypeMemPtr)x1._ts[1];

    // A0 -> (X0 <-> X1) -> A1 -> X2 -> A2 -> (X3 <-> X4 ) -> A3 -> X5
    TypeStruct  a0 = TypeStruct.make(flds2,new Type[]{px0,TypeInt.con(0)},finals2,alias0);
    TypeMemPtr pa0 = TypeMemPtr.make(alias0,a0);

    // Check sanity
    depths = a0.depth(alias0);
    assertEquals(0,(int)depths.get(a0));
    assertEquals(1,(int)depths.get(a1));
    assertEquals(2,(int)depths.get(a2));
    assertEquals(3,(int)depths.get(a3));
    assertEquals(3,TypeStruct.max(alias0,depths));

    // Approximate
    TypeStruct zsa0 = a0.approx(3);

    // Check sanity
    // A0 -> (X0 <-> X1) -> A1 -> X2 -> A23-> (X35<-> X45) -> A23
    TypeMemPtr zpx0 = (TypeMemPtr)zsa0._ts[0];
    assertSame  (TypeInt.con(0) , zsa0._ts[1]);

    TypeStruct zsx0 = (TypeStruct)zpx0._obj;
    TypeMemPtr zpa1 = (TypeMemPtr)zsx0._ts[0];
    TypeMemPtr zpx1 = (TypeMemPtr)zsx0._ts[1];
    assertSame  (i10 ,            zsx0._ts[2]);

    TypeStruct zsx1 = (TypeStruct)zpx1._obj;
    assertSame  (zpa1,            zsx1._ts[0]);
    assertSame  (zpx0,            zsx1._ts[1]);
    assertSame  (i11 ,            zsx1._ts[2]);

    TypeStruct zsa1 = (TypeStruct)zpa1._obj;
    TypeMemPtr zpx2 = (TypeMemPtr)zsa1._ts[0];
    assertSame  (TypeInt.con(1),  zsa1._ts[1]);

    TypeStruct zsx2 = (TypeStruct)zpx2._obj;
    TypeMemPtr zpa23= (TypeMemPtr)zsx2._ts[0];
    assertSame  (Type.NIL,        zsx2._ts[1]);
    assertSame  (TypeInt.con(12), zsx2._ts[2]);

    TypeStruct zsa23= (TypeStruct)zpa23._obj;
    TypeMemPtr zpx35= (TypeMemPtr)zsa23._ts[0];
    assertSame  (TypeInt.NINT8,   zsa23._ts[1]);

    TypeStruct zsx35= (TypeStruct)zpx35._obj;
    TypeMemPtr zpa45= (TypeMemPtr)zsx35._ts[1];
    assertSame  (TypeInt.NINT8,   zsx35._ts[2]);

    TypeStruct zsx45= (TypeStruct)zpa45._obj;
    assertSame  (zpa23,           zsx45._ts[0]);
    assertSame  (TypeInt.con(14), zsx45._ts[2]);

    assertTrue(a0.isa(zsa0));
    depths = zsa0.depth(alias0);
    assertEquals(0,(int)depths.get(zsa0));
    assertEquals(1,(int)depths.get(zsa1));
    assertEquals(2,(int)depths.get(zsa23));
    assertEquals(2,TypeStruct.max(alias0,depths));
  }


  // Type A expands tree-like and gets too deep.
  // A0 -> A00 -> A000
  //           -> A001
  //       A01 -> A010
  //           -> A011
  // And then:
  // A0 -> A00 -> A000 -> A0000
  // Approx:
  // A0 -> A00 -> A000/A0000
  //           -> A001
  //       A01 -> A010
  //           -> A011
  // ... and so forth.  The first few tree layers remain expanded, but the tree
  // tail collapses.
  @Test public void testApprox4() {
    assertTrue(false);
  }


}
