package com.cliffc.aa;

import com.cliffc.aa.type.*;
import org.junit.Before;
import org.junit.Test;

import static com.cliffc.aa.HM3.*;
import static org.junit.Assert.assertEquals;

public class TestHM3 {

  @Before public void reset() { HM3.reset(); }

  @Test(expected = RuntimeException.class)
  public void test00() {
    Syntax syn = new Ident("fred");
    HM3.hm(syn);
  }

  @Test
  public void test01() {
    Syntax syn = new Con(TypeInt.con(3));
    HMVar t = (HMVar)HM3.hm(syn);
    assertEquals(TypeInt.con(3),t.type());
  }

  @Test
  public void test02() {
    Syntax syn = new Apply(new Ident("pair"),new Con(TypeInt.con(3)));
    HMType t = HM3.hm(syn);
    assertEquals("{ v25 -> pair(v21:3,v25$) }",t.str());
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
    HMType t1 = HM3.hm(fact);
    assertEquals("{ v31:int64 -> v31$ }",t1.str());
  }

  @Test
  public void test04() {
    // { x -> (pair (x 3) (x "abc")) }
    Syntax x =
      new Lambda("x",
                 new Apply(new Apply(new Ident("pair"),
                                     new Apply(new Ident("x"), new Con(TypeInt.con(3)))),
                           new Apply(new Ident("x"), new Con(TypeStr.ABC))));
    HMType t1 = HM3.hm(x);
    assertEquals("{ { v22:all -> v23 } -> pair(v23$,v23$) }",t1.str());
  }

  @Test
  public void test05() {
    // ({ x -> (pair (x 3) (x "abc")) } {y->y})
    Syntax x =
      new Apply(new Lambda("x",
                           new Apply(new Apply(new Ident("pair"),
                                               new Apply(new Ident("x"), new Con(TypeInt.con(3)))),
                                     new Apply(new Ident("x"), new Con(TypeStr.ABC)))),
                new Lambda("y", new Ident("y")));

    HMType t1 = HM3.hm(x);
    assertEquals("pair(v22:all,v22$)",t1.str());
  }


  @Test
  public void test05a() {
    // let x = {y->y} in (pair (x 3) (x "abc"))
    Syntax x =
      new Let("x",
              new Lambda("y", new Ident("y")),
              new Apply(new Apply(new Ident("pair"),
                                  new Apply(new Ident("x"), new Con(TypeInt.con(3)))),
                        new Apply(new Ident("x"), new Con(TypeStr.ABC))));

    HMType t1 = HM3.hm(x);
    assertEquals("pair(v27:3,v23:\"abc\")",t1.str());
  }

  @Test
  public void test06() {
    // recursive unification
    // fn f => f f (fail)
    Syntax x =
      new Lambda("f", new Apply(new Ident("f"), new Ident("f")));
    HMType t1 = HM3.hm(x);
    // Not minimal form, but not too bad
    assertEquals("{ { v23$ -> v22 } -> v22$ }",t1.str());
  }

  @Test
  public void test07() {
    // let g = fn f => 5 in g g
    Syntax x =
      new Let("g",
              new Lambda("f", new Con(TypeInt.con(5))),
              new Apply(new Ident("g"), new Ident("g")));
    HMType t1 = HM3.hm(x);
    assertEquals("v25:5",t1.str());
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

    HMType t1 = HM3.hm(syn);
    assertEquals("{ v21 -> pair(v21$,v21$) }",t1.str());
  }

  @Test
  public void test09() {
    // Function composition
    // fn f (fn g (fn arg (f g arg)))
    Syntax syn =
      new Lambda("f", new Lambda("g", new Lambda("arg", new Apply(new Ident("g"), new Apply(new Ident("f"), new Ident("arg"))))));

    HMType t1 = HM3.hm(syn);
    assertEquals("{ { v23 -> v24 } -> { { v24$ -> v27 } -> { v23$ -> v27$ } } }",t1.str());
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
    HMType t1 = HM3.hm(syn);
    assertEquals("pair(v36:*str,pair(v24:flt64,v24$))",t1.str());
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
    HMType t1 = HM3.hm(syn);
    // Cannot unify v29:5 and pair96(v97:3,v96$)
    // Cannot unify 5 and (3,$) - unifying a 5 with a pair.
    assertEquals("TBD",t1.str());
  }

  @Test(expected = RuntimeException.class)
  public void test12() {
    // Want to constant-fold if/else, and drop the dead unification.
    // So compute: (int->bool int) // ==0
    //             (flt->pair 1.2) // factor
    //             (P ? {==0} : {factor}) // Force unification {int/flt} -> {bool/pair}
    // lambda P
    //  (((==0 1),(factor 1.2)),  (((if/else P) ==0) factor))
    Syntax syn =
      new Lambda("p",
                 new Apply(new Apply(new Apply(new Ident("if/else"),new Ident("p")), // (((if/else p) ==0) factor)
                                     new Ident("==0")),
                           new Ident("factor")));
    HMType t1 = HM3.hm(syn);
    assertEquals("Cannot unify v27:int1 and pair24(v23:Real,v23$)",t1.str());
  }
}
