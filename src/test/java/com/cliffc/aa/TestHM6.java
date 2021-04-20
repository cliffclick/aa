package com.cliffc.aa;

import com.cliffc.aa.type.*;
import org.junit.Before;
import org.junit.Test;

import static com.cliffc.aa.HM6.*;
import static org.junit.Assert.assertEquals;

public class TestHM6 {

  @Before public void reset() { HM.reset(); }

  @Test(expected = RuntimeException.class)
  public void test00() {
    HM6.hm("fred");
  }

  @Test
  public void test01() {
    Syntax syn = new Con(TypeInt.con(3));
    T2 t = HM6.hm("3");
    assertEquals("3",t.p());
  }

  @Test
  public void test02() {
    T2 t = HM6.hm("(pair1 3)");
    assertEquals("{ V24 -> (pair 3 V24) }",t.p());
  }

  @Test
  public void test03() {
    T2 t = HM6.hm("{ z -> (pair (z 3) (z \"abc\")) }");
    assertEquals("{ { all -> V23 } -> (pair V23 V23) }",t.p());
  }

  @Test
  public void test04() {
    T2 t = HM6.hm("fact = { n -> (if/else (==0 n) 1 (* n (fact (dec n))))}; fact");
    assertEquals("{ int64 -> int64 }",t.p());
  }

  @Test
  public void test05() {
    // Because {y->y} is passed in, all 'y' types must agree.
    // This unifies 3 and "abc" which results in 'all'
    T2 t1 = HM6.hm("({ x -> (pair (x 3) (x \"abc\")) } {y->y})");
    assertEquals("(pair all all)",t1.p());
  }

  @Test//(expected = RuntimeException.class)  No longer throws, but returns a recursive type
  public void test06() {
    // recursive unification
    T2 t1 = HM6.hm("{ f -> (f f) }");
    assertEquals("{ $25:{ $25 -> V21 } -> V21 }",t1.p());
    // We can argue the pretty-print should print:
    // "$26:{ $26 -> V21 }"
  }

  @Test
  public void test07() {
    T2 t1 = HM6.hm("g = {f -> 5}; (g g)");
    assertEquals("5",t1.p());
  }

  @Test
  public void test08() {
    // example that demonstrates generic and non-generic variables:
    T2 t1 = HM6.hm("{ g -> f = { x -> g }; (pair (f 3) (f \"abc\"))}");
    assertEquals("{ V21 -> (pair V21 V21) }",t1.p());
  }

  @Test
  public void test09() {
    T2 t1 = HM6.hm("{ f g -> (f g)}");
    assertEquals("{ { V20 -> V22 } V20 -> V22 }",t1.p());
  }

  @Test
  public void test10() {
    // Function composition
    T2 t1 = HM6.hm("{ f g -> { arg -> (g (f arg))} }");
    assertEquals("{ { V19 -> V26 } { V26 -> V24 } -> { V19 -> V24 } }",t1.p());
  }

  @Test
  public void test11() {
    // Stacked functions ignoring all function arguments
    T2 t1 = HM6.hm("map = { fun -> { x -> 2 } }; ((map 3) 5)");
    assertEquals("2",t1.p());
  }

  @Test
  public void test12() {
    // map takes a function and an element (collection?) and applies it (applies to collection?)
    T2 t1 = HM6.hm("map = { fun -> { x -> (fun x)}}; { p -> 5 }");
    assertEquals("{ V21 -> 5 }",t1.p());
  }

  @Test
  public void test13() {
    // Looking at when tvars are duplicated ("fresh" copies made).
    // This is the "map" problem with a scalar instead of a collection.
    // Takes a '{a->b}' and a 'a' for a couple of different prims.
    T2 t1 = HM6.hm("map = { fun -> { x -> (fun x)}};"+
                  "(pair ((map str) 5) ((map factor) 2.3))");
    assertEquals("(pair str (divmod flt64 flt64))",t1.p());
  }

  @Test
  public void test14() {
    // map takes a function and an element (collection?) and applies it (applies to collection?)
    T2 t1 = HM6.hm("map = { fun x -> (fun x)}; (map {a->3} 5)");
    assertEquals("3",t1.p());
  }

  @Test
  public void test15() {
    // map takes a function and an element (collection?) and applies it (applies to collection?)
    T2 t1 = HM6.hm("map = { fun x -> (fun x)}; (map { a-> (pair a a)} 5)");
    assertEquals("(pair 5 5)",t1.p());
  }

  @Test
  public void test16() {
    T2 t1 = HM6.hm("fcn = { p -> { a -> (pair a a) }};"+
                  "map = { fun x -> (fun x)};"+
                  "{ q -> (map (fcn q) 5)}");
    assertEquals("{ V23 -> (pair 5 5) }",t1.p());
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
    // Ultimately, unifies "a" with "pair[3,a]" which throws recursive unification.
    T2 t1 = HM6.hm("fcn = {p -> (if/else p {a -> (pair a a)} {b -> (pair b (pair 3 b))})};"+
                  "map = { fun x -> (fun x)};"+
                  "{ q -> (map (fcn q) 5)}");
    assertEquals("TBD",t1.p());
  }

  @Test
  public void test18() {
    T2 t1 = HM6.hm("cons ={x y-> {cadr -> (cadr x y)}};"+
                  "cdr ={mycons -> (mycons { p q -> q})};"+
                  "(cdr (cons 2 3))");
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
    T2 t1 = HM6.hm("cons ={x y-> {cadr -> (cadr x y)}};"+
                  "cdr ={mycons -> (mycons { p q -> q})};"+
                  "map ={fun parg -> (fun (cdr parg))};"+
                  "(pair (map str (cons 0 5)) (map isempty (cons 0 \"abc\")))"
                  );
    assertEquals("(pair str int1)",t1.p());
  }

  // Obscure factorial-like
  @Test
  public void test20() {
    T2 t1 = HM6.hm("f0 = { f x -> (if/else (==0 x) 1 (f (f0 f (dec x)) 2))}; (f0 * 99)");
    assertEquals("int64",t1.p());
  }

  // Obscure factorial-like
  @Test
  public void test21() {
    // let f0 = fn f x => (if/else (==0 x) 1 (* (f0 f (dec x)) 2) ) in f0 f0 99
    // let f0 = fn f x => (if/else (==0 x) 1 (f (f0 f (dec x)) 2) ) in f0 *  99
    T2 t1 = HM6.hm("f0 = { f x -> (if/else (==0 x) 1 (* (f0 f (dec x)) 2))}; (f0 f0 99)");
    assertEquals("int64",t1.p());
  }

  // Mutual recursion
  @Test
  public void test22() {
    T2 t1 = HM6.hm("is_even = "+
                  "  is_odd = { n -> (if/else (==0 n) 0 (is_even (dec n)))}; "+
                  "     { n -> (if/else (==0 n) 1 (is_odd (dec n)))};"+
                  "(is_even 3)"
                  );
    assertEquals("int1",t1.p());
  }

  // Toss a function into a pair & pull it back out
  @Test
  public void test23() {
    T2 t1 = HM6.hm("{ g -> fgz = "+
                  "         cons = {x y -> {cadr -> (cadr x y)}};"+
                  "         cdr = {mycons -> (mycons { p q -> q})};"+
                  "         (cdr (cons 2 { z -> (g z) }));"+
                  "      (pair (fgz 3) (fgz 5))"+
                  "}"
                  );
    assertEquals("{ { nint8 -> V44 } -> (pair V44 V44) }",t1.p());
  }

}
