package com.cliffc.aa;

import com.cliffc.aa.type.*;
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
    assertEquals("{ v9 -> pair(v8:3,v9$) }",t.str());
  }

  @Test
  public void test3() {
    // { x -> (pair (x 3) (x "abc")) }
    Syntax x =
      new Lambda("x",
                 new Apply(new Apply(new Ident("pair"),
                                     new Apply(new Ident("x"), new Con(TypeInt.con(3)))),
                           new Apply(new Ident("x"), new Con(TypeStr.ABC))));
    HMType t1 = HM1.HM(x);
    assertEquals("{ { v11:all -> v9 } -> pair(v9$,v9$) }",t1.str());
  }

  @Test
  public void test4() {
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
    assertEquals("{ v25:int64 -> v25$ }",t1.str());
  }

  @Test
  public void test5() {
    // ({ x -> (pair (x 3) (x "abc")) } {y->y})
    Syntax x =
      new Apply(new Lambda("x",
                           new Apply(new Apply(new Ident("pair"),
                                               new Apply(new Ident("x"), new Con(TypeInt.con(3)))),
                                     new Apply(new Ident("x"), new Con(TypeStr.ABC)))),
                new Lambda("y", new Ident("y")));

    HMType t1 = HM1.HM(x);
    assertEquals("pair(v17:all,v17$)",t1.str());
  }

  @Test(expected = RuntimeException.class)
  public void test6() {
    // recursive unification
    // fn f => f f (fail)
    Syntax x =
      new Lambda("f", new Apply(new Ident("f"), new Ident("f")));
    HMType t1 = HM1.HM(x);
    assertEquals("TBD",t1.str());
  }

  @Test
  public void test7() {
    // let g = fn f => 5 in g g
    Syntax x =
      new Let("g",
              new Lambda("f", new Con(TypeInt.con(5))),
              new Apply(new Ident("g"), new Ident("g")));
    HMType t1 = HM1.HM(x);
    assertEquals("v12:5",t1.str());
  }

  @Test
  public void test8() {
    // example that demonstrates generic and non-generic variables:
    // fn g => let f = (fn x => g) in pair (f 3, f true)
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
    assertEquals("{ v11 -> pair(v11$,v11$) }",t1.str());
  }

  @Test
  public void test10() {
    // Function composition
    // fn f (fn g (fn arg (f g arg)))
    Syntax syn =
      new Lambda("f", new Lambda("g", new Lambda("arg", new Apply(new Ident("g"), new Apply(new Ident("f"), new Ident("arg"))))));

    HMType t1 = HM1.HM(syn);
    assertEquals("{ { v10 -> v11 } -> { { v11$ -> v12 } -> { v10$ -> v12$ } } }",t1.str());
  }

  @Test
  public void test13() {
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
    HMType t1 = HM1.HM(syn);
    assertEquals("pair(v12:*str,pair(v26:flt64,v26$))",t1.str());
  }

  @Test(expected = RuntimeException.class)
  public void test17() {
    // Checking behavior when using "if/else" to merge two functions with
    // sufficiently different signatures, then attempting to pass them to a map
    // & calling internally.
    // fcn takes a predicate 'p' and returns one of two fcns.
    //   let fcn = { p -> (((if/else p) {a -> pair[a,a]}) {b -> pair[b,pair[3,b]]}) } in
    // map takes a function and an element (collection?) and applies it (applies to collection?)
    //   let map = { fun -> {x -> (fun x) }} in
    //   { q -> ((map (fcn q)) 5) }
    // Should return either { p -> p ? [5,5] : [5,[3,5]] }
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
    // Ultimately, unifies "a" with "pair[3,a]" which throws recursive unification.
    HMType t1 = HM1.HM(syn);
    assertEquals("TBD",t1.str());
  }

  @Test
  public void test18() {
    // Hand-rolled cons/cdr
    // let cons = { x y -> { cadr -> (cadr x y) } }
    // in         let cdr = { mycons -> (mycons { p q -> q}) }
    //            in (cdr (cons 2 3))
    Syntax syn =
      new Let("cons", new Lambda2("x","y",
                                  new Lambda("cadr",new Apply(new Ident("cadr"),new Ident("x"),new Ident("y")))),
              new Let("cdr", new Lambda("mycons", new Apply(new Ident("mycons"), new Lambda2("p","q", new Ident("q")))),
                      new Apply(new Ident("cdr"),
                                new Apply(new Ident("cons"), new Con(TypeInt.con(2)), new Con(TypeInt.con(3))))));
    HMType t1 = HM1.HM(syn);
    assertEquals("v20:3",t1.str());
  }

  @Test
  public void test20() {
    // let f0 = fn f x => (if/else3 (==0 x) 1 (f (f0 f (dec x)) 2) ) in f0 *2 99
    Syntax syn =
      new Let("f0", new Lambda2("f","x",
                                new Apply(new Ident("if/else3"),
                                          new Apply(new Ident("==0"), new Ident("x")),
                                          new Con(TypeInt.con(1)),
                                          new Apply(new Ident("f"),
                                                    new Apply(new Ident("f0"),
                                                              new Ident("f"),
                                                              new Apply(new Ident("dec"), new Ident("x"))),
                                                    new Con(TypeInt.con(2)))
                                          )
                                ),
              new Apply(new Ident("f0"), new Ident("*2"), new Con(TypeInt.con(99))));
    HMType t1 = HM1.HM(syn);
    assertEquals("v24:int64",t1.str());
  }

  // Toss a function into a pair & pull it back out
  @Test
  public void test23() {
    // { g ->
    //   let fgz =
    //     // Hand-rolled cons/cdr
    //     let cons = { x y -> { cadr -> (cadr x y) } }
    //     in         let cdr = { mycons -> (mycons { p q -> q}) }
    //                in (cdr (cons 2 {z -> g z}))
    //   in ((pair (fgz 3)) (fgz 5))
    // }
    Syntax syn =
      new Lambda("g",
                 new Let("fgz",
                         new Let("cons",
                                 new Lambda2("x","y", new Lambda("cadr",new Apply(new Ident("cadr"),new Ident("x"),new Ident("y")))),
                                 new Let("cdr",
                                         new Lambda("mycons", new Apply(new Ident("mycons"), new Lambda2("p","q", new Ident("q")))),
                                         new Apply(new Ident("cdr"),
                                                   new Apply(new Ident("cons"),
                                                             new Con(TypeInt.con(2)),
                                                             new Lambda("z",new Apply(new Ident("g"),new Ident("z"))))))),
                         new Apply(new Apply(new Ident("pair"),
                                             new Apply(new Ident("fgz"),new Con(TypeInt.con(3)))),
                                   new Apply(new Ident("fgz"),new Con(TypeInt.con(5))))));
    HMType t1 = HM1.HM(syn);
    assertEquals("{ { v27:nint8 -> v31 } -> pair(v31$,v31$) }",t1.str());
  }

}
