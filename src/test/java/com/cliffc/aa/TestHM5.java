package com.cliffc.aa;

import com.cliffc.aa.type.*;
import org.junit.Before;
import org.junit.Test;

import static com.cliffc.aa.HM5.*;
import static org.junit.Assert.assertEquals;

public class TestHM5 {

  @Before public void reset() { HM5.reset(); }

  @Test(expected = RuntimeException.class)
  public void test00() {
    Syntax syn = new Ident("fred");
    HM5.hm(syn);
  }

  @Test
  public void test01() {
    Syntax syn = new Con(TypeInt.con(3));
    T2 t = HM5.hm(syn);
    assertEquals("3",t.p());
  }

  @Test
  public void test02() {
    Syntax syn = new Apply(new Ident("pair1"),new Con(TypeInt.con(3)));
    T2 t = HM5.hm(syn);
    assertEquals("{ V24 -> (pair 3 V24) }",t.p());
  }

  @Test
  public void test03() {
    // { z -> (pair (z 3) (z "abc")) }
    Syntax x =
      new Lambda("z",
                 new Apply(new Ident("pair"),
                           new Apply(new Ident("z"), new Con(TypeInt.con(3))),
                           new Apply(new Ident("z"), new Con(TypeStr.ABC))));
    T2 t = HM5.hm(x);
    assertEquals("{ { all -> V23 } -> (pair V23 V23) }",t.p());
  }

  @Test
  public void test04() {
    // let fact = {n -> (if/else (==0 n)  1  (* n (fact (dec n))))} in fact;
    Syntax fact =
      new Let("fact",
              new Lambda("n",
                         new Apply(new Ident("if/else"),
                                   new Apply(new Ident("==0"),new Ident("n")), // Predicate
                                   new Con(TypeInt.con(1)),                    // True arm
                                   new Apply(new Ident("*"),                  // False arm
                                             new Ident("n"),
                                             new Apply(new Ident("fact"),
                                                       new Apply(new Ident("dec"),new Ident("n")))))),
              new Ident("fact"));
    T2 t = HM5.hm(fact);
    assertEquals("{ int64 -> int64 }",t.p());
  }

  @Test
  public void test05() {
    // ({ x -> (pair (x 3) (x "abc")) } {y->y})
    // Because {y->y} is passed in, all 'y' types must agree.
    // This unifies 3 and "abc" which results in 'all'
    Syntax x =
      new Apply(new Lambda("x",
                           new Apply(new Ident("pair"),
                                     new Apply(new Ident("x"), new Con(TypeInt.con(3))),
                                     new Apply(new Ident("x"), new Con(TypeStr.ABC)))),
                new Lambda("y", new Ident("y")));

    T2 t1 = HM5.hm(x);
    assertEquals("(pair all all)",t1.p());
  }

  @Test//(expected = RuntimeException.class)  No longer throws, but returns a recursive type
  public void test06() {
    // recursive unification
    // fn f => f f (fail)
    Syntax x =
      new Lambda("f", new Apply(new Ident("f"), new Ident("f")));
    T2 t1 = HM5.hm(x);
    assertEquals("{ $25:{ $25 -> V21 } -> V21 }",t1.p());
    // We can argue the pretty-print should print:
    // "$26:{ $26 -> V21 }"
  }

  @Test
  public void test07() {
    // let g = (fn f => 5) in (g g)
    Syntax x =
      new Let("g",
              new Lambda("f", new Con(TypeInt.con(5))),
              new Apply(new Ident("g"), new Ident("g")));
    T2 t1 = HM5.hm(x);
    assertEquals("5",t1.p());
  }

  @Test
  public void test08() {
    // example that demonstrates generic and non-generic variables:
    // fn g => let f = (fn x => g) in pair (f 3, f true)
    Syntax syn =
      new Lambda("g",
                 new Let("f",
                         new Lambda("x", new Ident("g")),
                         new Apply(new Ident("pair"),
                                   new Apply(new Ident("f"), new Con(TypeInt.con(3))),
                                   new Apply(new Ident("f"), new Con(TypeInt.con(1))))));
    T2 t1 = HM5.hm(syn);
    assertEquals("{ V2 -> (pair V2 V2) }",t1.p());
  }

  @Test
  public void test09() {
    // fn f g => (f g)
    Syntax syn =
      new Lambda2("f", "g", new Apply(new Ident("f"), new Ident("g")));
    T2 t1 = HM5.hm(syn);
    assertEquals("{ { V1 -> V22 } V1 -> V22 }",t1.p());
  }

  @Test
  public void test10() {
    // Function composition
    // fn f g => (fn arg => g (f arg))
    Syntax syn =
      new Lambda2("f", "g", new Lambda("arg", new Apply(new Ident("g"), new Apply(new Ident("f"), new Ident("arg")))));
    T2 t1 = HM5.hm(syn);
    assertEquals("{ { V0 -> V26 } { V26 -> V24 } -> { V0 -> V24 } }",t1.p());
  }

  @Test
  public void test11() {
    // Stacked functions ignoring all function arguments
    // let map = (fn fun => (fn x => 2))
    //        in ((map 3) 5)
    Syntax syn =
      new Let("map",
              new Lambda("fun",
                         new Lambda("x",
                                    new Con(TypeInt.con(2)))),
              new Apply(new Apply(new Ident("map"),
                                  new Con(TypeInt.con(3))),
                        new Con(TypeInt.con(5))));
    T2 t1 = HM5.hm(syn);
    assertEquals("2",t1.p());
  }

  @Test
  public void test12() {
    // map takes a function and an element (collection?) and applies it (applies to collection?)
    //   let map = { fun -> {x -> (fun x) }}
    //          in { p -> 5 }
    Syntax syn =
      new Let("map",
              new Lambda("fun",
                         new Lambda("x",
                                    new Apply(new Ident("fun"),new Ident("x")))),
              new Lambda("p",
                         new Con(TypeInt.con(5))));
    T2 t1 = HM5.hm(syn);
    assertEquals("{ V2 -> 5 }",t1.p());
  }

  @Test
  public void test13() {
    // Looking at when tvars are duplicated ("fresh" copies made).
    // This is the "map" problem with a scalar instead of a collection.
    // Takes a '{a->b}' and a 'a' for a couple of different prims.
    // let map = { fun -> {x -> (fun x) }}
    //        in (pair ((map str) 5) ((map factor) 2.3))
    Syntax syn =
      new Let("map",
              new Lambda("fun",
                         new Lambda("x",
                                    new Apply(new Ident("fun"),new Ident("x")))),
              new Apply(new Ident("pair"),
                        new Apply(new Apply(new Ident("map"), new Ident("str")),
                                  new Con(TypeInt.con(5))),
                        new Apply(new Apply(new Ident("map"), new Ident("factor")),
                                  new Con(TypeFlt.con(2.3))))
              );
    T2 t1 = HM5.hm(syn);
    assertEquals("(pair str (divmod flt64 flt64))",t1.p());
  }

  @Test
  public void test14() {
    // map takes a function and an element (collection?) and applies it (applies to collection?)
    //   let map = { fun -> {x -> (fun x) }}
    //          in (map {a -> 3} 5)
    Syntax syn =
      new Let("map",
              new Lambda("fun",
                         new Lambda("x",
                                    new Apply(new Ident("fun"),new Ident("x")))),
              new Apply(new Apply(new Ident("map"),
                                  new Lambda("a",new Con(TypeInt.con(3)))),
                        new Con(TypeInt.con(5))));
    T2 t1 = HM5.hm(syn);
    assertEquals("3",t1.p());
  }

  @Test
  public void test15() {
    // map takes a function and an element (collection?) and applies it (applies to collection?)
    //   let map = { fun -> {x -> (fun x) }}
    //          in (map {a -> [a,a]} 5)
    Syntax syn =
      new Let("map",
              new Lambda("fun",
                         new Lambda("x",
                                    new Apply(new Ident("fun"),new Ident("x")))),
              new Apply(new Apply(new Ident("map"),
                                  new Lambda("a",
                                             new Apply(new Ident("pair"),
                                                       new Ident("a"),
                                                       new Ident("a")))),
                        new Con(TypeInt.con(5))));
    T2 t1 = HM5.hm(syn);
    assertEquals("(pair 5 5)",t1.p());
  }

  @Test
  public void test16() {
    //   let fcn = { p a -> pair[a,a] } in
    // map takes a function and an element (collection?) and applies it (applies to collection?)
    //   let map = { fun x -> (fun x) }
    //          in { q -> (map (fcn q) 5) }
    // Should return  { q -> [5,5] }
    Syntax syn =
      new Let("fcn",
              new Lambda("p",
                         new Lambda("a",
                                    new Apply(new Ident("pair"),
                                              new Ident("a"),
                                              new Ident("a")))),
              new Let("map",
                      new Lambda2("fun", "x", new Apply(new Ident("fun"),new Ident("x"))),
                      new Lambda("q",
                                 new Apply(new Ident("map"),
                                           new Apply(new Ident("fcn"),new Ident("q")),
                                           new Con(TypeInt.con(5))))));
    T2 t1 = HM5.hm(syn);
    assertEquals("{ V4 -> (pair 5 5) }",t1.p());
  }

  @Test(expected = RuntimeException.class)
  public void test17() {
    // Checking behavior when using "if/else" to merge two functions with
    // sufficiently different signatures, then attempting to pass them to a map
    // & calling internally.
    // fcn takes a predicate 'p' and returns one of two fcns.
    //   let fcn = { p -> (if/else p {a -> pair[a,a        ]}
    //                               {b -> pair[b,pair[3,b]]}) } in
    // map takes a function and an element (collection?) and applies it (applies to collection?)
    //   let map = { fun x -> (fun x) }
    //          in { q -> ((map (fcn q)) 5) }
    // Should return { q -> q ? [5,5] : [5,[3,5]] }
    Syntax syn =
      new Let("fcn",
              new Lambda("p",
                         new Apply(new Ident("if/else"),
                                   new Ident("p"), // p ?
                                   new Lambda("a",
                                              new Apply(new Ident("pair"),
                                                        new Ident("a"),
                                                        new Ident("a"))),
                                   new Lambda("b",
                                              new Apply(new Ident("pair"),
                                                        new Ident("b"),
                                                        new Apply(new Ident("pair"),
                                                                  new Con(TypeInt.con(3)),
                                                                  new Ident("b")))))),
              new Let("map",
                      new Lambda2("fun","x",new Apply(new Ident("fun"),new Ident("x"))),
                      new Lambda("q",
                                 new Apply(new Ident("map"),
                                           new Apply(new Ident("fcn"),new Ident("q")),
                                           new Con(TypeInt.con(5))))));
    // Ultimately, unifies "a" with "pair[3,a]" which throws recursive unification.
    T2 t1 = HM5.hm(syn);
    assertEquals("TBD",t1.p());
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
    T2 t1 = HM5.hm(syn);
    assertEquals("3",t1.p());
  }

  // Take 2nd element of pair, and applies a function.
  //    let map = fn parg fun => (fun (cdr parg))
  // Some pairs:
  //    let intz = (pair2 false 3)
  //    let strz = (pair2 false "abc")
  // in pair(map(str,intz),map(isempty,strz))
  // Expects: ("2",false)
  @Test
  public void test19() {
    Syntax syn =
      new Let("cons", new Lambda2("x","y",
                                  new Lambda("cadr",new Apply(new Ident("cadr"),new Ident("x"),new Ident("y")))),
              new Let("cdr", new Lambda("mycons", new Apply(new Ident("mycons"), new Lambda2("p","q", new Ident("q")))),
                      new Let("map",
                              new Lambda2("fun", "parg",
                                          new Apply(new Ident("fun"),
                                                    new Apply(new Ident("cdr"),new Ident("parg"))
                                                    )),
                              // in pair(map(),map())
                              new Apply(new Ident("pair"),
                                        new Apply(new Ident("map"), new Ident("str"    ), (new Apply(new Ident("cons"),new Con(TypeInt.BOOL),new Con(TypeInt.con(5))))),
                                        new Apply(new Ident("map"), new Ident("isempty"), (new Apply(new Ident("cons"),new Con(TypeInt.BOOL),new Con(TypeStr.ABC   ))))
                                        ))));
    T2 t1 = HM5.hm(syn);
    assertEquals("(pair str int1)",t1.p());
  }

  // Obscure factorial-like
  @Test
  public void test20() {
    // let f0 = fn f x => (if/else (==0 x) 1 (f (f0 f (dec x)) 2) ) in f0 * 99
    Syntax x =
      new Let("f0", new Lambda2("f","x",
                                new Apply(new Ident("if/else"),
                                          new Apply(new Ident("==0"), new Ident("x")),
                                          new Con(TypeInt.con(1)),
                                          new Apply(new Ident("f"),
                                                    new Apply(new Ident("f0"),
                                                              new Ident("f"),
                                                              new Apply(new Ident("dec"), new Ident("x"))),
                                                    new Con(TypeInt.con(2)))
                                          )
                                ),
              new Apply(new Ident("f0"), new Ident("*"), new Con(TypeInt.con(99))));
    T2 t1 = HM5.hm(x);
    assertEquals("int64",t1.p());
  }


  // Obscure factorial-like
  @Test
  public void test21() {
    // let f0 = fn f x => (if/else (==0 x) 1 (* (f0 f (dec x)) 2) ) in f0 f0 99
    // let f0 = fn f x => (if/else (==0 x) 1 (f  (f0 f (dec x)) 2) ) in f0 * 99
    Syntax x =
      new Let("f0", new Lambda2("f","x",
                                new Apply(new Ident("if/else"),
                                          new Apply(new Ident("==0"), new Ident("x")),
                                          new Con(TypeInt.con(1)),
                                          new Apply(new Ident("*"),
                                                    new Apply(new Ident("f0"),
                                                              new Ident("f"),
                                                              new Apply(new Ident("dec"), new Ident("x"))),
                                                    new Con(TypeInt.con(2)))
                                          )
                                ),
              new Apply(new Ident("f0"), new Ident("f0"), new Con(TypeInt.con(99))));
    T2 t1 = HM5.hm(x);
    assertEquals("int64",t1.p());
  }

  // Mutual recursion
  @Test
  public void test22() {
    /* let is_even =
           (let is_odd = fn x => (if/else (==0 x) false (is_even (dec x)))
                      in fn x => (if/else (==0 x) true  (is_odd  (dec x))))
                   in (is_even 3)
    */
    Syntax x = new Let("is_even",
                       new Let("is_odd",
                               new Lambda("n",
                                          new Apply(new Ident("if/else"),
                                                    new Apply(new Ident("==0"), new Ident("n")),
                                                    new Con(TypeInt.con(0)),
                                                    new Apply(new Ident("is_even"),
                                                              new Apply(new Ident("dec"), new Ident("n"))))),
                               new Lambda("n",
                                          new Apply(new Ident("if/else"),
                                                    new Apply(new Ident("==0"), new Ident("n")),
                                                    new Con(TypeInt.con(1)),
                                                    new Apply(new Ident("is_odd" ),
                                                              new Apply(new Ident("dec"), new Ident("n")))))
                               ),
                       new Apply(new Ident("is_even"), new Con(TypeInt.con(3))));
    T2 t1 = HM5.hm(x);
    assertEquals("int1",t1.p());
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
    //   in (pair (fgz 3) (fgz 5))
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
                         new Apply(new Ident("pair"),
                                   new Apply(new Ident("fgz"),new Con(TypeInt.con(3))),
                                   new Apply(new Ident("fgz"),new Con(TypeInt.con(5))))));
    T2 t1 = HM5.hm(syn);
    assertEquals("{ { nint8 -> V33 } -> (pair V33 V33) }",t1.p());
  }

}
