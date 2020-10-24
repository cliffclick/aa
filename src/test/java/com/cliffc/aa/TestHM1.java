package com.cliffc.aa;

import com.cliffc.aa.type.TypeInt;
import com.cliffc.aa.type.TypeStr;
import org.junit.Before;
import org.junit.Test;

import static com.cliffc.aa.HM1.*;
import static org.junit.Assert.assertEquals;

public class TestHM1 {

  @Before public void reset() { HM1.reset(); }

  @Test(expected = RuntimeException.class)
  public void test0() {
    Syntax syn = new Ident("fred");
    HM1.HM(syn);
  }

  @Test
  public void test1() {
    Syntax syn = new Con(TypeInt.con(3));
    HMVar t = (HMVar)HM1.HM(syn);
    assertEquals(TypeInt.con(3),t.type());
  }

  @Test
  public void test2() {
    Syntax syn = new Apply(new Ident("pair"),new Con(TypeInt.con(3)));
    HMType t = HM1.HM(syn);
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
    HMType t1 = HM1.HM(fact);
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
    HMType t1 = HM1.HM(x);
    assertEquals("{ { v9:all -> v7 } -> pair(v7,v7) }",t1.str());
  }

  @Test
  public void test5() {
    // ({ x -> (pair (x 3) (x "abc")) } {x->x})
    Syntax x =
      new Apply(new Lambda("x",
                           new Apply(new Apply(new Ident("pair"),
                                               new Apply(new Ident("x"), new Con(TypeInt.con(3)))),
                                     new Apply(new Ident("x"), new Con(TypeStr.ABC)))),
                new Lambda("x", new Ident("x")));

    HMType t1 = HM1.HM(x);
    assertEquals("pair(v15:all,v15:all)",t1.str());
  }


  @Test(expected = RuntimeException.class)
  public void test6() {
    // recursive unification
    // fn f => f f (fail)
    Syntax x =
      new Lambda("f", new Apply(new Ident("f"), new Ident("f")));
    HM1.HM(x);
  }

  @Test
  public void test7() {
    // let g = fn f => 5 in g g
    Syntax x =
      new Let("g",
              new Lambda("f", new Con(TypeInt.con(5))),
              new Apply(new Ident("g"), new Ident("g")));
    HMType t1 = HM1.HM(x);
    assertEquals("v10:5",t1.str());
  }

  @Test
  public void test8() {
    // example that demonstrates generic and non-generic variables:
    // fn g => let f = fn x => g in pair (f 3, f true)
    Syntax syn =
      new Lambda("g",
                 new Let("f",
                         new Lambda("x", new Ident("g")),
                         new Apply(
                                   new Apply(new Ident("pair"),
                                             new Apply(new Ident("f"), new Con(TypeInt.con(3)))
                                             ),
                                   new Apply(new Ident("f"), new Con(TypeInt.con(1))))));

    HMType t1 = HM1.HM(syn);
    assertEquals("{ v9 -> pair(v9,v9) }",t1.str());
  }

  @Test
  public void test9() {
    // Function composition
    // fn f (fn g (fn arg (f g arg)))
    Syntax syn =
      new Lambda("f", new Lambda("g", new Lambda("arg", new Apply(new Ident("g"), new Apply(new Ident("f"), new Ident("arg"))))));

    HMType t1 = HM1.HM(syn);
    assertEquals("{ { v8 -> v9 } -> { { v9 -> v10 } -> { v8 -> v10 } } }",t1.str());
  }

}
