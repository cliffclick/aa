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

    // End result should be a cycle of lenght 1: [,real] -> * ->
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
  }
}
