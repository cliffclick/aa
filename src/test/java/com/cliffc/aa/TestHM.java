package com.cliffc.aa;

import com.cliffc.aa.type.TypeInt;
import org.junit.Test;
import org.junit.Before;

import static com.cliffc.aa.HM.*;
import static org.junit.Assert.assertEquals;

public class TestHM {
  
  @Before public void reset() { HM.reset(); }

  @Test(expected = RuntimeException.class)
  public void test0() {
    Syntax syn = new Ident("fred");
    HM.HM(syn);
  }

  @Test
  public void test1() {
    Syntax syn = new Con(TypeInt.con(3));
    HMBase t = (HMBase)HM.HM(syn);
    assertEquals(TypeInt.con(3),t.type());
  }

  @Test
  public void test2() {
    Syntax syn = new Apply(new Ident("pair"),new Con(TypeInt.con(3)));
    HMType t = HM.HM(syn);
    String rez = t.str();
    assertEquals("{ v2 -> pair(3,v2) }",rez);
  }



}
