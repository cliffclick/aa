package com.cliffc.aa;

import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;
import org.junit.Ignore;
import org.junit.Test;

import static org.junit.Assert.*;


public class TestTVar {
  private static final String[] FLD = new String[]{TypeFld.CLZ,"fld"};
  private static final String[] CLZ = new String[]{TypeFld.CLZ};

  // Simply unify leaf and lambda
  private static TV3[] _testUnify() {
    return new TV3[]{
      new TVLeaf(),
      new TVLambda(AA.ARG_IDX,new TVLeaf(),new TVLeaf())
    };
  }
  @Test public void testUnify() {
    // Normal unify, both become lambda
    { TV3[] tvs = _testUnify();
      TV3 v0 = tvs[0], v1 = tvs[1];
      boolean rez = v0.unify( v1, false );
      assertTrue( rez );
      assertSame( v0.find(), v1.find() );
    }
    // Fresh leaf to lambda, no progress
    { TV3[] tvs = _testUnify();
      TV3 v0 = tvs[0], v1 = tvs[1];
      boolean rez = v0.fresh_unify( null, null, v1, false );
      assertFalse( rez );
      assertNotSame( v0.find(), v1.find() );
    }
    // Fresh lambda to leaf; fresh unchanged but leaf is unifiable with lambda
    { TV3[] tvs = _testUnify();
      TV3 v0 = tvs[0], v1 = tvs[1];
      boolean rez = v1.fresh_unify( null, null, v0, false );
      assertTrue( rez );
      assertNotSame( v0.find(), v1.find() );
      assertEquals( 3, v0.find().trial_unify_ok( v1 ) ); // Always a hard yes in a trial
    }
  }


  // Simply unify two open structs
  private static TV3[] _testUnifyOpen() {
    return new TV3[]{
      new TVStruct(new String[]{"fldA","fldB"},new TV3[]{new TVLeaf(),new TVLeaf()},true),
      new TVStruct(new String[]{"fldB","fldC"},new TV3[]{new TVLeaf(),new TVLeaf()},true),
    };
  }
  @Test public void testUnifyOpen() {
    // Normal
    { TV3[] tvs = _testUnifyOpen();
      TV3 v0 = tvs[0], v1 = tvs[1];
      TV3 fldb0 = v0.find().as_struct().arg("fldB");
      TV3 fldb1 = v1.find().as_struct().arg("fldB");
      boolean rez = v0.unify( v1, false );
      assertTrue( rez );
      assertSame( fldb0.find(), fldb1.find() );
      assertEquals(3,v0.as_struct().len() );
    }
    // Fresh
    { TV3[] tvs = _testUnifyOpen();
      TV3 v0 = tvs[0], v1 = tvs[1];
      boolean rez = v0.fresh_unify( null, null, v1, false );
      assertTrue( rez );
      assertEquals(3,v1.as_struct().len() );
    }
  }
  
  // Simply unify two closed structs
  private static TV3[] _testUnifyClose() {
    return new TV3[]{
      new TVStruct(new String[]{TypeFld.CLZ,"fldA","fldB"},new TV3[]{TVPtr.PTRCLZ,new TVLeaf(),new TVLeaf()},false),
      new TVStruct(new String[]{TypeFld.CLZ,"fldB","fldC"},new TV3[]{TVPtr.PTRCLZ,new TVLeaf(),new TVLeaf()},false),
    };
  }
  @Test public void testUnifyClose() {
    // Normal
    { TV3[] tvs = _testUnifyClose();
      TV3 v0 = tvs[0], v1 = tvs[1];
      TV3 fldb0 = v0.find().as_struct().arg("fldB");
      TV3 fldb1 = v1.find().as_struct().arg("fldB");
      boolean rez = v0.unify( v1, false );
      assertTrue( rez );
      assertSame( fldb0.find(), fldb1.find() );
      assertEquals(2,v0.find().as_struct().len() );
    }
    // Fresh
    { TV3[] tvs = _testUnifyClose();
      TV3 v0 = tvs[0], v1 = tvs[1];
      TV3 fldb0 = v0.find().as_struct().arg("fldB");
      TV3 fldb1 = v1.find().as_struct().arg("fldB");
      boolean rez = v0.fresh_unify( null, null, v1, false );
      assertTrue( rez );
      assertEquals(3,v0.as_struct().len() );
      assertEquals(2,v1.as_struct().len() );
    }
  }

  // Simply unify two mixed structs
  private static TV3[] _testUnifyMix() {
    return new TV3[]{
      new TVStruct(new String[]{TypeFld.CLZ,"fldA","fldB"},new TV3[]{TVPtr.PTRCLZ,new TVLeaf(),new TVLeaf()},false),
      new TVStruct(new String[]{            "fldB","fldC"},new TV3[]{             new TVLeaf(),new TVLeaf()},true ),
    };
  }
  @Test public void testUnifyMix() {
    // Normal, close on left
    { TV3[] tvs = _testUnifyMix();
      TV3 v0 = tvs[0], v1 = tvs[1];
      TV3 fldb0 = v0.find().as_struct().arg("fldB");
      TV3 fldb1 = v1.find().as_struct().arg("fldB");
      boolean rez = v0.unify( v1, false );
      assertTrue( rez );
      assertSame( fldb0.find(), fldb1.find() );
      assertEquals(3,v0.find().as_struct().len() );
    }
    // Normal, close on right
    { TV3[] tvs = _testUnifyMix();
      TV3 v0 = tvs[0], v1 = tvs[1];
      TV3 fldb0 = v0.find().as_struct().arg("fldB");
      TV3 fldb1 = v1.find().as_struct().arg("fldB");
      int tmp=v0._uid; v0._uid=v1._uid; v1._uid=tmp;
      boolean rez = v0.unify( v1, false );
      assertTrue( rez );
      assertSame( fldb0.find(), fldb1.find() );
      assertEquals(3,v0.find().as_struct().len() );
    }
    // Fresh, close on left (fresh)
    { TV3[] tvs = _testUnifyMix();
      TV3 v0 = tvs[0], v1 = tvs[1];
      boolean rez = v0.fresh_unify( null, null, v1, false );
      v1 = v1.find();
      assertTrue( rez );
      assertEquals(3,v0.as_struct().len() );
      assertEquals(3,v1.as_struct().len() );
      assertNotNull( v1.as_struct().arg( "fldA" ) );
      assertNull   ( v1.as_struct().arg( "fldC" ) );
    }
    // Fresh, close on right (fresh)
    { TV3[] tvs = _testUnifyMix();
      TV3 v0 = tvs[0], v1 = tvs[1];
      boolean rez = v1.fresh_unify( null, null, v0, false );
      assertFalse( rez );
      assertEquals(3,v0.as_struct().len() );
      assertEquals(2,v1.as_struct().len() );
      assertNotNull( v1.as_struct().arg( "fldC" ) );
      assertNull   ( v1.as_struct().arg( "fldA" ) );
    }
  }

  
  
  // Make a TVStruct with no Clz, and 1 field which should be in the Clz.
  //   @{ fld=V1, ... }
  // Make a TVStruct with a CLz and the fld in the class.
  //   @{ ^=@{ ^=PTRCLZ, fld=V2:{ V3 -> V4 } }
  // During normal unify, both use the same clz, and V1 should unify with V2
  private static TV3[] _testUnifyClz0() {
    TVLambda vlam2 = new TVLambda(AA.ARG_IDX,new TVLeaf(),new TVLeaf());
    TVStruct vclz = new TVStruct(FLD, new TV3[]{TVPtr.PTRCLZ,vlam2});
    int zalias = BitsAlias.new_alias();
    TVPtr vpclz = new TVPtr(BitsAlias.make0(zalias),vclz);
    TVStruct vs3  = new TVStruct(CLZ, new TV3[]{vpclz});
      
    TVLeaf v0 = new TVLeaf();
    TVStruct vs1  = new TVStruct(true);
    vs1.add_fld(FLD[1],v0 ); // Unpinned field
    
    return new TV3[]{ vs1,vs3,v0,vlam2 };
  }
  @Test public void testUnifyClz0() {
    // Normal unify, fld moves up to shared CLZ and unifies
    { TV3[] tvs = _testUnifyClz0();
      TV3 vs1 = tvs[0], vs3 = tvs[1], v0 = tvs[2], vlam2 = tvs[3];      
      boolean rez = vs3.unify(vs1,false);
      assertTrue(rez);
      assertSame(v0.find(),vlam2.find());
    }
    { TV3[] tvs = _testUnifyClz0();
      TV3 vs1 = tvs[0], vs3 = tvs[1], v0 = tvs[2], vlam2 = tvs[3];      
      boolean rez = vs3.fresh_unify(null,null,vs1,false);
      assertTrue(rez);
      assertEquals( 3, v0.find().trial_unify_ok( vlam2 ) ); // Always a hard yes in a trial
    }
    { TV3[] tvs = _testUnifyClz0();
      TV3 vs1 = tvs[0], vs3 = tvs[1], v0 = tvs[2], vlam2 = tvs[3];      
      boolean rez = vs1.fresh_unify(null,null,vs3,false);
      assertFalse(rez);
    }
  }

  // Testing criss-cross Fresh unify.  Getting this wrong gets me infinite
  // blow-up instead of a cycle.
  // FRESH: { V4:@{a=V2} @{b=V4} -> ret }
  // THAT : { V1         V2      -> ret }
  
  // Unification will unify V1 to a fresh of @{a=V2}, unify V2 to a fresh of
  // @{b=V3}, but then the fresh @{a=V2} gets unified with the V2-unify of
  // @{b=V3} and the cycle closes.
  // RESULT: { V1:@{a=V2}  V2:@{b=V1} -> ret }

  private static TV3[] _testCrissCross() {
    TV3 ret = new TVLeaf();
    TVLeaf   dsp1 = new TVLeaf();
    TVLeaf   dyn1 = new TVLeaf();
    // { dsp dyn -> ret }
    TVStruct dsp0 = new TVStruct(new String[]{TypeFld.CLZ,"a"},new TV3[]{TVPtr.PTRCLZ,dyn1});
    TVStruct dyn0 = new TVStruct(new String[]{TypeFld.CLZ,"b"},new TV3[]{TVPtr.PTRCLZ,dsp0});
    TVLambda lam0 = new TVLambda(new TV3[]{ret,null,dsp0,dyn0});
    // { V1  V2 -> ret }
    TVLambda lam1 = new TVLambda(new TV3[]{ret,null,dsp1,dyn1});
    return new TV3[]{ lam0, lam1, dsp0, dsp1, dyn0, dyn1 };
  }
  @Test public void testCrissCross() {
    // Normal unify, fields remain separate
    { TV3[] tvs = _testCrissCross();
      TV3 lam0 = tvs[0], lam1 = tvs[1], dsp0 = tvs[2], dsp1 = tvs[3], dyn0 = tvs[4], dyn1 = tvs[5];
      boolean rez = lam0.unify(lam1,false);
      assertTrue(rez);
      assertSame(lam0.find(),lam1.find());
      assertSame(dsp0.find(),dsp1.find());
      assertSame(dyn0.find(),dyn1.find());
    }
    // Fresh unify, will cross-cross
    { TV3[] tvs = _testCrissCross();
      TV3 lam0 = tvs[0], lam1 = tvs[1], dsp0 = tvs[2], dsp1 = tvs[3], dyn0 = tvs[4], dyn1 = tvs[5];
      boolean rez = lam0.fresh_unify(null,null,lam1,false);
      assertTrue(rez);
      TV3 B = dyn1.find();
      TV3 C = dsp1.find();
      assertSame(dsp0.as_struct().arg("a"),B);
      assertSame(dsp1.find().as_struct().arg("a"),B);
      assertSame(B.as_struct().arg("b"),C);
    }
    // Fresh unify other way
    { TV3[] tvs = _testCrissCross();
      TV3 lam0 = tvs[0], lam1 = tvs[1], dsp0 = tvs[2], dsp1 = tvs[3], dyn0 = tvs[4], dyn1 = tvs[5];
      boolean rez = lam1.fresh_unify(null,null,lam0,false);
      assertFalse(rez);
      assertFalse(dsp0.unified());
      assertFalse(dsp1.unified());
      assertFalse(dyn0.unified());
      assertFalse(dyn1.unified());
    }
  }
  
  // Testing criss-cross Fresh unify.  Getting this wrong gets me infinite
  // blow-up instead of a cycle.
  // FRESH: V2:*[]@{fld=V1}
  // THAT : V1
  // Result:
  // FRESH: V2:*[]@{fld=V3}
  // THAT : V3:*[]@{fld=V3}

  private static TV3[] _testCrissCross2() {
    TVLeaf   v1 = new TVLeaf();
    TVStruct v2 = new TVStruct(new String[]{TypeFld.CLZ,"fld"},new TV3[]{TVPtr.PTRCLZ,v1});
    return new TV3[]{ v1,v2 };
  }
  @Test public void testCrissCross2() {
    // Normal unify, fields remain separate
    { TV3[] tvs = _testCrissCross2();
      TV3 v1 = tvs[0], v2 = tvs[1];
      boolean rez = v1.unify(v2,false);
      assertTrue(rez);
      assertSame(v1.find(),v2.find());
      assertSame(v2.as_struct().arg("fld"),v2);
    }
    // Fresh unify
    { TV3[] tvs = _testCrissCross2();
      TV3 v1 = tvs[0], v2 = tvs[1];
      boolean rez = v1.fresh_unify(null,null,v2,false);
      assertFalse(rez);
    }
    // Fresh unify other way.  This will trigger criss-cross
    { TV3[] tvs = _testCrissCross2();
      TV3 v1 = tvs[0], v2 = tvs[1];
      boolean rez = v2.fresh_unify(null,null,v1,false);
      assertTrue(rez);
      assertSame(v1.find().as_struct().arg("fld"),v1.find());
      assertSame(v2.find().as_struct().arg("fld"),v1.find());
      assertNotSame( v1.find(), v2.find() );
    }
  }

  
  // Build a super-class chain list.
  // tvs[0] is an open TVStruct with no fields.
  // tvs[N] is an open TVStruct with exactly a CLZ TVPtr to tvs[N-1]
  private static TVStruct[] superchain( TVStruct[] tvs ) {
    tvs[0] = new TVStruct(true);
    for( int i=1; i<tvs.length; i++ ) {
      BitsAlias zalias = BitsAlias.make0(BitsAlias.new_alias());
      TVPtr ptr = new TVPtr(zalias,tvs[i-1]);
      tvs[i] = new TVStruct(true);
      tvs[i].add_fld(TypeFld.CLZ,ptr );
    }
    return tvs;
  }

  // CNC - 2/3/2024
  // This test is now no good, as new invariant is that CLZs are never open
  // and that open structs have no CLZ.
  private static TV3[] _testUnifyClz1() {
    // Should get cross-fields from both and unify with the CLZ field in the other.    
    //   @{ ^=@{ fld0={ int -> V2 }, ...}, fld1= { int -> V4} }
    //   @{ ^=@{ fld1={ V3 -> flt }, ...}, fld0= { V5 -> flt} }
    TVStruct[] tvs0 = superchain(new TVStruct[2]);
    TVStruct[] tvs1 = superchain(new TVStruct[2]);
    
    TV3 vint = new TVBase(TypeInt.INT64);
    TV3 vflt = new TVBase(TypeFlt.FLT64);
    TVLambda vlam0 = new TVLambda(AA.ARG_IDX, vint, new TVLeaf());
    TVLambda vlam1 = new TVLambda(AA.ARG_IDX, vint, new TVLeaf());
    TVLambda vlam3 = new TVLambda(AA.ARG_IDX, new TVLeaf(), vflt);
    TVLambda vlam4 = new TVLambda(AA.ARG_IDX, new TVLeaf(), vflt);

    tvs0[0].add_fld("fld0",vlam0 );
    tvs1[0].add_fld("fld1",vlam3 );
    
    TVStruct vs0 = tvs0[1];
    TVStruct vs1 = tvs1[1];
    vs0.add_fld("fld1",vlam1 );
    vs1.add_fld("fld0",vlam4 );

    return new TV3[]{ vs0, vs1, vlam0, vlam1, vlam3, vlam4 };
  }
  @Ignore @Test public void testUnifyClz1() {
    { TV3[] tvs = _testUnifyClz1();
      TV3 vs0 = tvs[0], vs1 = tvs[1], vlam0 = tvs[2], vlam1 = tvs[3], vlam3 = tvs[4], vlam4 = tvs[5];
      boolean rez = vs0.unify(vs1,false);
      assertTrue(rez);
      // Both share the same CLZ
      assertSame(vs0.as_struct().pclz(),vs1.find().as_struct().pclz());
      // Instance fields from either unified with same from CLZ in other
      assertSame(vlam0 .find(),vlam4 .find());
      assertSame(vlam1 .find(),vlam3 .find());
    }
    { TV3[] tvs = _testUnifyClz1();
      TV3 vs0 = tvs[0], vs1 = tvs[1], vlam0 = tvs[2], vlam1 = tvs[3], vlam3 = tvs[4], vlam4 = tvs[5];
      boolean rez = vs0.fresh_unify(null,null,vs1,false);
      assertTrue(rez);
      // Both look alike
      assertEquals( 1, vs0.find().trial_unify_ok( vs1 ) ); // Always a hard yes in a trial
      // Instance fields from either unified with same from CLZ in other
      assertEquals( 1, vlam0.find().trial_unify_ok( vlam4.find() ) );
      assertEquals( 1, vlam1.find().trial_unify_ok( vlam3.find() ) );
      assertTrue( ((TVLambda)vlam3).dsp() instanceof TVBase base && base._t==TypeInt.INT64);
      assertTrue( ((TVLambda)vlam4).dsp() instanceof TVBase base && base._t==TypeInt.INT64);
    }
    { TV3[] tvs = _testUnifyClz1();
      TV3 vs0 = tvs[0], vs1 = tvs[1], vlam0 = tvs[2], vlam1 = tvs[3], vlam3 = tvs[4], vlam4 = tvs[5];
      boolean rez = vs1.fresh_unify(null,null,vs0,false);
      assertTrue(rez);
      // Both look alike
      assertEquals( 1, vs1.find().trial_unify_ok( vs0 ) ); // Always a hard yes in a trial
      // Instance fields from either unified with same from CLZ in other
      assertEquals( 1, vlam0.find().trial_unify_ok( vlam4.find() ) );
      assertEquals( 1, vlam1.find().trial_unify_ok( vlam3.find() ) );
      assertTrue( ((TVLambda)vlam0).ret() instanceof TVBase base && base._t==TypeFlt.FLT64);
      assertTrue( ((TVLambda)vlam1).ret() instanceof TVBase base && base._t==TypeFlt.FLT64);
    }
  }

  // CNC - 2/3/2024
  // This test is now no good, as new invariant is that CLZs are never open
  // and that open structs have no CLZ.
  // 3 CLZs deep.
  // CLZA open, empty        <<== CLZB, closed field1 <<== INST C, has unpinned field0, open
  // CLZA closed, has field0 <<== CLZB, closed field1 <<== INST C, has pinned field 2.
  // Unify:
  // CLZA, closed, unified field0 <<== CLZB closed unified field1 <<== INST C field 2
  private static TV3[] _testUnifyClz2() {
    TVStruct[] tvs0 = superchain(new TVStruct[3]);
    TVStruct[] tvs1 = superchain(new TVStruct[3]);

    // CLZA
    TVStruct vclzA1 = tvs1[0];
    TV3 v0 = new TVLeaf();
    vclzA1.add_fld("fld0",v0 );
    vclzA1.close();

    // CLZB
    TVStruct vclzB0 = tvs0[1];
    TVStruct vclzB1 = tvs1[1];
    TV3 v1_0 = new TVLeaf();
    TV3 v1_1 = new TVLeaf();
    vclzB0.add_fld("fld1",v1_0 );
    vclzB1.add_fld("fld1",v1_1 );
    vclzB0.close();
    vclzB1.close();

    // CLZC
    TVStruct vclzC0 = tvs0[2];
    TVStruct vclzC1 = tvs1[2];
    TV3 v2_0 = new TVLeaf();
    TV3 v2_1 = new TVLeaf();
    vclzC0.add_fld("fld0",v2_0 );
    vclzC1.add_fld("fld2",v2_1 );
    vclzC1.close();
    
    return new TV3[]{ vclzC0, vclzC1, v0, v2_0, v1_0, v1_1 };
  }
  
  @Ignore @Test public void testUnifyClz2() {
    { TV3[] tvs = _testUnifyClz2();
      TVStruct vclzC0 = (TVStruct)tvs[0], vclzC1 = (TVStruct)tvs[1];
      TV3 v0 = tvs[2], v2_0 = tvs[3], v1_0 = tvs[4], v1_1 = tvs[5];
      boolean rez = vclzC0.unify(vclzC1,false);
      assertTrue(rez);
      // Both share the same CLZ
      assertSame(vclzC0.pclz(),vclzC1.find().as_struct().pclz());
      // Instance fields from either unified with same from CLZ in other
      assertSame(v0.find(),v2_0.find());
      assertSame(v1_0.find(),v1_1.find());
      assertTrue(vclzC1.idx("fld2") != -1);
    }
    { TV3[] tvs = _testUnifyClz2();
      TVStruct vclzC0 = (TVStruct)tvs[0], vclzC1 = (TVStruct)tvs[1];
      TV3 v0 = tvs[2], v2_0 = tvs[3], v1_0 = tvs[4], v1_1 = tvs[5];
      boolean rez = vclzC0.fresh_unify(null,null,vclzC1,false);
      assertTrue(rez);
      // Both look alike
      assertEquals( 1, vclzC0.find().trial_unify_ok( vclzC1 ) ); // Always a hard yes in a trial
      assertTrue( vclzC0.pclz().aliases().abit() > 0 );           // Single alias
      assertEquals( -1, vclzC1.pclz().aliases().abit() );         // Unified aliases
    }
    { TV3[] tvs = _testUnifyClz2();
      TVStruct vclzC0 = (TVStruct)tvs[0], vclzC1 = (TVStruct)tvs[1];
      TV3 v0 = tvs[2], v2_0 = tvs[3], v1_0 = tvs[4], v1_1 = tvs[5];
      boolean rez = vclzC1.fresh_unify(null,null,vclzC0,false);
      assertTrue(rez);
      // Both look alike
      assertEquals( 1, vclzC1.find().trial_unify_ok( vclzC0 ) ); // Always a hard yes in a trial
      assertTrue( vclzC1.pclz().aliases().abit() > 0 );           // Single alias
      assertEquals( -1, vclzC0.pclz().aliases().abit() );         // Unified aliases
      assertEquals( -1, vclzC0.idx( "fld0" ) );
      assertTrue(vclzC0.idx("fld2") > 0  );
    }
  }
}
