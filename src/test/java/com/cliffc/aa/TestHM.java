package com.cliffc.aa;

import com.cliffc.aa.type.*;
import org.junit.Before;
import org.junit.Test;

import static com.cliffc.aa.HM.*;
import static org.junit.Assert.assertEquals;

public class TestHM {

  @Before public void reset() { HM.reset(); }

  @Test(expected = RuntimeException.class)
  public void test00() {
    Syntax syn = new Ident("fred");
    HM.hm(syn);
  }

  @Test
  public void test01() {
    Syntax syn = new Con(TypeInt.con(3));
    HMVar t = (HMVar)HM.hm(syn);
    assertEquals(TypeInt.con(3),t.type());
  }

  @Test
  public void test02() {
    Syntax syn = new Apply(new Ident("pair"),new Con(TypeInt.con(3)));
    HMType t = HM.hm(syn);
    assertEquals("{ v10 -> pair(v8:3,v10$) }",t.str());
  }

  @Test
  public void test03() {
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
    HMType t1 = HM.hm(fact);
    assertEquals("{ v14:int64 -> v14$ }",t1.str());
  }

  @Test
  public void test04() {
    // { x -> (pair (x 3) (x "abc")) }
    Syntax x =
      new Lambda("x",
                 new Apply(new Apply(new Ident("pair"),
                                     new Apply(new Ident("x"), new Con(TypeInt.con(3)))),
                           new Apply(new Ident("x"), new Con(TypeStr.ABC))));
    HMType t1 = HM.hm(x);
    assertEquals("{ { v9:all -> v10 } -> pair(v10$,v10$) }",t1.str());
  }

  @Test
  public void test05() {
    // ({ x -> (pair (x 3) (x "abc")) } {x->x})
    Syntax x =
      new Apply(new Lambda("x",
                           new Apply(new Apply(new Ident("pair"),
                                               new Apply(new Ident("x"), new Con(TypeInt.con(3)))),
                                     new Apply(new Ident("x"), new Con(TypeStr.ABC)))),
                new Lambda("y", new Ident("y")));

    HMType t1 = HM.hm(x);
    assertEquals("pair(v9:all,v9$)",t1.str());
  }


  @Test(expected = RuntimeException.class)
  public void test06() {
    // recursive unification
    // fn f => f f (fail)
    Syntax x =
      new Lambda("f", new Apply(new Ident("f"), new Ident("f")));
    HM.hm(x);
  }

  @Test
  public void test07() {
    // let g = fn f => 5 in g g
    Syntax x =
      new Let("g",
              new Lambda("f", new Con(TypeInt.con(5))),
              new Apply(new Ident("g"), new Ident("g")));
    HMType t1 = HM.hm(x);
    assertEquals("v12:5",t1.str());
  }

  @Test
  public void test08() {
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

    HMType t1 = HM.hm(syn);
    assertEquals("{ v8 -> pair(v8$,v8$) }",t1.str());
  }

  @Test
  public void test09() {
    // Function composition
    // fn f (fn g (fn arg (f g arg)))
    Syntax syn =
      new Lambda("f", new Lambda("g", new Lambda("arg", new Apply(new Ident("g"), new Apply(new Ident("f"), new Ident("arg"))))));

    HMType t1 = HM.hm(syn);
    assertEquals("{ { v10 -> v11 } -> { { v11$ -> v12 } -> { v10$ -> v12$ } } }",t1.str());
  }

  @Test
  public void test10() {
    // Looking at when tvars are duplicated ("fresh" copies made).
    // This is the "map" problem with a scalar instead of a collection.
    // Takes a '{a->b}' and a 'a' for a couple of different prims.
    // let map = { fun -> {x -> (fun x) }} in ((pair ((map str) 5)) ((map factor) 2.3))
    Syntax syn =
      new Let("map",
              new Lambda("fun",
                         new Lambda("x",
                                    new Apply(new Ident("fun"),new Ident("x")))),
              new Apply(new Apply(new Ident("pair"),
                                  new Apply(new Apply(new Ident("map"),
                                                      new Ident("str")), new Con(TypeInt.con(5)))),
                        new Apply(new Apply(new Ident("map"),
                                            // "factor" a float returns a pair (mod,rem).
                                            new Ident("factor")), new Con(TypeFlt.con(2.3)))));
    HMType t1 = HM.hm(syn);
    assertEquals("pair(v18:*str,pair(v11:flt64,v11$))",t1.str());
  }

  @Test(expected = RuntimeException.class)
  public void test11() {
    // Checking behavior when using "if/else" to merge two functions with
    // sufficiently different signatures, then attempting to pass them to a map
    // & calling internally.
    // fcn takes a predicate 'p' and returns one of two fcns.
    //   let fcn = { p -> (((if/else p) {a -> pair[a,a]}) {b -> pair[b,pair[3,b]]}) } in
    // map takes a function and an element (collection?) and applies it (applies to collection?)
    //   let map = { fun -> {x -> (fun x) }} in
    // Should return either { p -> p ? [5,5] : [5,[3,5]] }
    //   { q -> ((map (fcn q)) 5) }

    Syntax syn =
      new Let("fcn",
              new Lambda("p",
                         new Apply(new Apply(new Apply(new Ident("if/else"),new Ident("p")), // p ?
                                             new Lambda("a",
                                                        new Apply(new Apply(new Ident("pair"),new Ident("a")),
                                                                  new Ident("a")))),
                                   new Lambda("b",
                                              new Apply(new Apply(new Ident("pair"),new Ident("b")),
                                                        new Apply(new Apply(new Ident("pair"),new Con(TypeInt.con(3))),
                                                                  new Ident("b")))))),
              new Let("map",
                      new Lambda("fun",
                                 new Lambda("x",
                                            new Apply(new Ident("fun"),new Ident("x")))),
                      new Lambda("q",
                                 new Apply(new Apply(new Ident("map"),
                                                     new Apply(new Ident("fcn"),new Ident("q"))),
                                           new Con(TypeInt.con(5))))));
    HMType t1 = HM.hm(syn);
    assertEquals("TBD",t1.str());
  }

}
