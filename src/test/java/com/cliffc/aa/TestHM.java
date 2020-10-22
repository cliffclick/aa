package com.cliffc.aa;

import com.cliffc.aa.type.TypeInt;
import com.cliffc.aa.type.TypeStr;
import org.junit.Before;
import org.junit.Test;

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
    HMVar t = (HMVar)HM.HM(syn);
    assertEquals(TypeInt.con(3),t.type());
  }

  @Test
  public void test2() {
    Syntax syn = new Apply(new Ident("pair"),new Con(TypeInt.con(3)));
    HMType t = HM.HM(syn);
    assertEquals("{ v7 -> pair(v6:3,v7) }",t.str());
  }

  @Test
  public void test3() {
    // let fact = {n -> (  if/else (==0 n)  1  ( * n  (fact (dec n))))} in fact;
    // let fact = {n -> (((if/else (==0 n)) 1) ((* n) (fact (dec n))))} in fact;
    Syntax fact =
      new Let("fact",
              new Lambda("n",
                         new Apply(new Apply( new Apply(new Ident("if/else"),
                                                        new Apply(new Ident("==0"),new Ident("n"))),
                                              new Con(TypeInt.con(1))),
                                   new Apply(new Apply(new Ident("*"), new Ident("n")),
                                             new Apply(new Ident("fact"),
                                                       new Apply(new Ident("dec"),new Ident("n")))))),
              new Ident("fact"));
    HMType t1 = HM.HM(fact);
    assertEquals("{ v23:int64 -> v23:int64 }",t1.str());
  }

  @Test
  public void test4() {
    // { x -> (pair (x 3) (x "abc")) }
    Syntax x =
      new Lambda("x",
                 new Apply(new Apply(new Ident("pair"),
                                     new Apply(new Ident("x"), new Con(TypeInt.con(3)))),
                           new Apply(new Ident("x"), new Con(TypeStr.ABC))));
    HMType t1 = HM.HM(x);
    assertEquals("{ {v9:all -> v7} -> pair(v7,v7) }",t1.str());
  }

}
