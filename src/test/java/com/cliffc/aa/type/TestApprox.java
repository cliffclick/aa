package com.cliffc.aa.type;

import org.junit.Test;

import java.util.HashMap;

import static org.junit.Assert.assertEquals;


public class TestApprox {
  // temp/junk holder for "instant" junits, when debugged moved into other tests
  @Test public void testType() {
    Type.init0(new HashMap<>());
  }

  // Test approximating infinite recursive types.
  @Test public void testApprox1() {
    Type.init0(new HashMap<>());
    int alias0 = BitsAlias.new_alias(BitsAlias.REC);
    String[] flds = new String[]{"a","b","c"};
    final int CUTOFF = 3;

    // Build a depth-CUTOFF linked list chain
    Type[] ts0 = TypeStruct.ts(Type.NIL,Type.NIL,TypeInt.con(99)); // Field 'c' is a int
    TypeStruct t0 = TypeStruct.make(flds,ts0,TypeStruct.bs(ts0),alias0);
    TypeMemPtr p0 = TypeMemPtr.make(alias0,t0);
    HashMap<Type,Integer> ds = t0.depth(alias0);
    assertEquals(0,(int)ds.get(t0));

    Type[] ts1 = TypeStruct.ts(p0,Type.NIL,TypeFlt.PI); // Field 'c' is a float
    TypeStruct t1 = TypeStruct.make(flds,ts1,TypeStruct.bs(ts1),alias0);
    TypeMemPtr p1 = TypeMemPtr.make(alias0,t1);
    ds = t1.depth(alias0);
    assertEquals(1,(int)ds.get(t0));
    assertEquals(0,(int)ds.get(t1));
    assertEquals(1,(int)ds.get(p0));

    Type[] ts2 = TypeStruct.ts(p1,Type.NIL,TypeInt.con(99));
    TypeStruct t2 = TypeStruct.make(flds,ts2,TypeStruct.bs(ts2),alias0);
    TypeMemPtr p2 = TypeMemPtr.make(alias0,t2);
    ds = t2.depth(alias0);
    assertEquals(2,(int)ds.get(t0));

    Type[] ts3 = TypeStruct.ts(p2,Type.NIL,TypeInt.con(99));
    TypeStruct t3 = TypeStruct.make(flds,ts3,TypeStruct.bs(ts3),alias0);
    TypeMemPtr p3 = TypeMemPtr.make(alias0,t3);
    ds = t3.depth(alias0);
    assertEquals(CUTOFF  ,(int)ds.get(t0));
    assertEquals(CUTOFF-1,(int)ds.get(t1));
    assertEquals(1,(int)ds.get(t2));
    assertEquals(0,(int)ds.get(t3));
    // No single depth is beyond cutoff
    int max = 0;
    for( Type t : ds.keySet() )
      if( t instanceof TypeStruct && ((TypeStruct)t)._news.test(alias0) )
        max = Math.max(max,ds.get(t));
    assertEquals(CUTOFF,max);

    // For all TypeStruct X at depth CUTOFF-1, make a clone of X and X's sub-
    // graph, except every edge to a type at depth CUTOFF is replaced with the
    // X clone.  Track replaced nodes.

    TypeStruct tax = t3.approx(CUTOFF,ds);
    HashMap<Type,Integer> ds2 = tax.depth(alias0);
    max = 0;
    for( Type t : ds2.keySet() )
      if( t instanceof TypeStruct && ((TypeStruct)t)._news.test(alias0) )
        max = Math.max(max,ds2.get(t));
    assertEquals(CUTOFF-1,max);
  }
}
