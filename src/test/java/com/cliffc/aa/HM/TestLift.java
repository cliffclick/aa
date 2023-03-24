package com.cliffc.aa.HM;

import com.cliffc.aa.HM.HM.Apply;
import com.cliffc.aa.HM.HM.T2;
import com.cliffc.aa.HM.HM.Triple;
import com.cliffc.aa.type.*;
import org.junit.Test;

import static com.cliffc.aa.AA.*;
import static com.cliffc.aa.type.TypeFld.Access;
import static org.junit.Assert.assertTrue;

public class TestLift {
  private static final String[] FLDS1 = new String[]{"0"};
  private static final String[] FLDS2 = new String[]{"0","1"};
  private static final String[] FLDS3 = new String[]{"0","1","2"};
  private BitsAlias B3;

  @Test public void testLift() {
    Type dummy = TypeMemPtr.ISUSED0;
    // Setup to call walk_types_out and confirm monotonicity.
    HM.reset();
    Apply apply = null;
    Triple triple = new Triple();
    int alias3 = triple._alias;
    B3 = BitsAlias.make0(alias3);
    T2 fr3 = triple._hmt;
    T2 frl = T2.make_fun(T2.make_leaf(),T2.make_leaf(),T2.make_leaf(),T2.make_leaf());

    // 289: *[3](^=any, _289$, _289$, _289$)
    Type.RECURSIVE_MEET++;
    TypeFld[] flds = TypeFlds.get(4);
    flds[0]=TypeFld.NO_DSP;
    TypeFld fld0 = flds[1] = TypeFld.malloc("0",null,Access.Final);
    TypeFld fld1 = flds[2] = TypeFld.malloc("1",null,Access.Final);
    TypeFld fld2 = flds[3] = TypeFld.malloc("2",null,Access.Final);
    TypeStruct ts = TypeStruct.malloc(false,"",Type.ALL,flds);
    TypeMemPtr ret1 = TypeMemPtr.malloc(false,false,B3,ts);
    fld0.setX(ret1);
    fld1.setX(ret1);
    fld2.setX(ret1);
    Type.RECURSIVE_MEET--;
    ts = Cyclic.install(ts);
    ret1 = TypeMemPtr.make(false,B3,ts);

    // 917: *[3](^=any, _917$, SCALR, SCALR)
    TypeFld[] flds2 = TypeFlds.get(4);
    flds2[0]=TypeFld.NO_DSP;
    TypeFld fld21 = flds2[2] = TypeFld.make_tup(TypeNil.SCALAR,ARG_IDX+1);
    TypeFld fld22 = flds2[3] = TypeFld.make_tup(TypeNil.SCALAR,ARG_IDX+2);
    Type.RECURSIVE_MEET++;
    TypeFld fld20 = flds2[1] = TypeFld.malloc("0",null,Access.Final);
    TypeStruct ts2 = TypeStruct.malloc(false,"",Type.ALL,flds2);
    TypeMemPtr ret2 = TypeMemPtr.make(false,B3,ts2);
    fld20.setX(ret2);
    Type.RECURSIVE_MEET--;
    ts2 = Cyclic.install(ts2);
    ret2 = TypeMemPtr.make(false,B3,ts2);

    // Build rezt2 from HM.apply_lift
    T2 x00 = make3(frl,frl,fr3);
    T2 x01 = make3(frl,fr3,fr3);
    T2 x02 = make3(frl,frl,frl);
    T2 x0_ = make_(x00,x01,x02);

    T2 x10 = make3(frl,frl,fr3);
    T2 x11 = make3(frl,frl,frl);
    T2 x12 = make3(frl,frl,frl);
    T2 x1_ = make_(x10,x11,x12);

    T2 x20 = make3(frl,frl,fr3);
    T2 x21 = make3(frl,frl,frl);
    T2 x22 = make3(frl,frl,frl);
    T2 x2_ = make_(x20,x21,x22);

    T2 x3_ = make_(x0_,x1_,x2_);

    // Call walk_types_out with ret1
    T2.WDUPS.clear(true);
    Type lift1 = x3_.walk_types_out(ret1,apply,true);

    // Call walk_types_out with ret2
    T2.WDUPS.clear(true);
    Type lift2 = x3_.walk_types_out(ret2,apply,true);

    // Check monotonic
    assertTrue(ret1 .isa(ret2 ));
    assertTrue(lift1.isa(lift2));

  };

  // Make a new T2 triple struct
  private T2 make3(T2 t0, T2 t1, T2 t2) {
    return T2.make_struct(FLDS3, new T2[]{t0.fresh(),t1.fresh(),t2.fresh()});
  }
  private T2 make_(T2 t0, T2 t1, T2 t2) {
    return T2.make_struct(FLDS3, new T2[]{t0,t1,t2});
  }

  // An attempt to make a smaller not-monotonic test case.
  // This reduction leads to a simpler test case:
  //  Type ret1 = TMP->anything
  //  Type ret2 = Scalar
  //  T2 t2 = FCN
  //  t2.walk_types_out(ret1) crosses a FCN and a TMP; has to return something higher than a FCN.
  //  t2.walk_types_out(ret2) lifts the Scalar to a FCN.
  // Implies, e.g. walk_types_out goes away, just compute "t2.as_flow()" and join(ret1) or join(ret2).
  //
  @Test public void testLift2() {
    Type dummy = TypeMemPtr.ISUSED0;
    // Setup to call walk_types_out and confirm monotonicity.
    HM.reset();
    Apply apply = null;
    Triple triple = new Triple();
    int alias3 = triple._alias;
    B3 = BitsAlias.make0(alias3);
    T2 fr3 = triple._hmt;
    T2 frl = T2.make_fun(T2.make_leaf(),T2.make_leaf());

    // 289: *[3](^=any, _289$)
    Type.RECURSIVE_MEET++;
    TypeFld fld1 = TypeFld.malloc("0",null,Access.Final);
    TypeStruct ts1 = TypeStruct.malloc_test("",TypeFld.NO_DSP,fld1);
    TypeMemPtr ret1 = TypeMemPtr.make(false,B3,ts1);
    fld1.setX(ret1);
    Type.RECURSIVE_MEET--;
    ts1 = Cyclic.install(ts1);
    ret1 = TypeMemPtr.make(false,B3,ts1);

    // 917: *[3](^=any, 0=SCALR)
    TypeFld fld2 = TypeFld.make_tup(TypeNil.SCALAR,ARG_IDX);
    TypeStruct ts2 = TypeStruct.make_test(TypeFld.NO_DSP,fld2);
    TypeMemPtr ret2 = TypeMemPtr.make(false,B3,ts2);
    
    // Build rezt2 from HM.apply_lift
    T2 x00 = T2.make_struct(FLDS1, new T2[]{frl.fresh()});
    
    // Call walk_types_out with ret1
    T2.WDUPS.clear(true);
    Type lift1 = x00.walk_types_out(ret1,apply,true);
    
    // Call walk_types_out with ret2
    T2.WDUPS.clear(true);
    Type lift2 = x00.walk_types_out(ret2,apply,true);
    
    // Check monotonic
    assertTrue(ret1 .isa(ret2 ));
    assertTrue(lift1.isa(lift2));
  };


}
