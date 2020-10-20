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

  @Test
  public void test3() {
    // let fact = {n -> (if/else (==0 n) 1 (* n (fact (dec n))))} in (fact 5);
    Syntax syn =
      new Let("fact",
              new Lambda("n",
                         new Apply(new Apply( new Apply(new Ident("if/else"),
                                                        new Apply(new Ident("==0"),new Ident("n"))),
                                              new Con(TypeInt.con(1))),
                                   new Apply(new Apply(new Ident("*"), new Ident("n")),
                                             new Apply(new Ident("fact"),
                                                       new Apply(new Ident("dec"),new Ident("n")))))),
              new Apply(new Ident("fact"), new Con(TypeInt.con(5))));
    HMType t = HM.HM(syn);
    String rez = t.str();
    assertEquals("{ v2 -> pair(3,v2) }",rez);
  }


}
