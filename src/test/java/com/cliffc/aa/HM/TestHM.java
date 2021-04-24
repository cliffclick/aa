package com.cliffc.aa.HM;

import org.junit.Before;
import org.junit.Test;

import static com.cliffc.aa.HM.HM.T2;
import static org.junit.Assert.assertEquals;

public class TestHM {

  @Before public void reset() { HM.reset(); }

  @Test(expected = RuntimeException.class)
  public void test00() {
    HM.hm("fred");
  }

  @Test
  public void test01() {
    T2 t = HM.hm("3");
    assertEquals("3",t.p());
  }

  @Test
  public void test02() {
    T2 t = HM.hm("(pair1 3)");
    assertEquals("{ A -> (pair 3 A) }",t.p());
  }

  @Test
  public void test03() {
    T2 t = HM.hm("{ z -> (pair (z 3) (z \"abc\")) }");
    assertEquals("{ { all -> A } -> (pair A A) }",t.p());
  }

  @Test
  public void test04() {
    T2 t = HM.hm("fact = { n -> (if (?0 n) 1 (* n (fact (dec n))))}; fact");
    assertEquals("{ int64 -> int64 }",t.p());
  }

  @Test
  public void test05() {
    // Because {y->y} is passed in, all 'y' types must agree.
    // This unifies 3 and "abc" which results in 'all'
    T2 t1 = HM.hm("({ x -> (pair (x 3) (x \"abc\")) } {y->y})");
    assertEquals("(pair all all)",t1.p());
  }

  @Test//(expected = RuntimeException.class)  No longer throws, but returns a recursive type
  public void test06() {
    // recursive unification
    T2 t1 = HM.hm("{ f -> (f f) }");
    assertEquals("{ A:{ $A -> B } -> B }",t1.p());
    // We can argue the pretty-print should print:
    // "A:{ $A -> B }"
  }

  @Test
  public void test07() {
    T2 t1 = HM.hm("g = {f -> 5}; (g g)");
    assertEquals("5",t1.p());
  }

  @Test
  public void test08() {
    // example that demonstrates generic and non-generic variables:
    T2 t1 = HM.hm("{ g -> f = { x -> g }; (pair (f 3) (f \"abc\"))}");
    assertEquals("{ A -> (pair A A) }",t1.p());
  }

  @Test
  public void test09() {
    T2 t1 = HM.hm("{ f g -> (f g)}");
    assertEquals("{ { A -> B } A -> B }",t1.p());
  }

  @Test
  public void test10() {
    // Function composition
    T2 t1 = HM.hm("{ f g -> { arg -> (g (f arg))} }");
    assertEquals("{ { A -> B } { B -> C } -> { A -> C } }",t1.p());
  }

  @Test
  public void test11() {
    // Stacked functions ignoring all function arguments
    T2 t1 = HM.hm("map = { fun -> { x -> 2 } }; ((map 3) 5)");
    assertEquals("2",t1.p());
  }

  @Test
  public void test12() {
    // map takes a function and an element (collection?) and applies it (applies to collection?)
    T2 t1 = HM.hm("map = { fun -> { x -> (fun x)}}; { p -> 5 }");
    assertEquals("{ A -> 5 }",t1.p());
  }

  @Test
  public void test13() {
    // Looking at when tvars are duplicated ("fresh" copies made).
    // This is the "map" problem with a scalar instead of a collection.
    // Takes a '{a->b}' and a 'a' for a couple of different prims.
    T2 t1 = HM.hm("map = { fun -> { x -> (fun x)}};"+
                  "(pair ((map str) 5) ((map factor) 2.3))");
    assertEquals("(pair str (divmod flt64 flt64))",t1.p());
  }

  @Test
  public void test14() {
    // map takes a function and an element (collection?) and applies it (applies to collection?)
    T2 t1 = HM.hm("map = { fun x -> (fun x)}; (map {a->3} 5)");
    assertEquals("3",t1.p());
  }

  @Test
  public void test15() {
    // map takes a function and an element (collection?) and applies it (applies to collection?)
    T2 t1 = HM.hm("map = { fun x -> (fun x)}; (map { a-> (pair a a)} 5)");
    assertEquals("(pair 5 5)",t1.p());
  }

  @Test
  public void test16() {
    T2 t1 = HM.hm("fcn = { p -> { a -> (pair a a) }};"+
                  "map = { fun x -> (fun x)};"+
                  "{ q -> (map (fcn q) 5)}");
    assertEquals("{ A -> (pair 5 5) }",t1.p());
  }

  @Test(expected = RuntimeException.class)
  public void test17() {
    // Checking behavior when using "if" to merge two functions with
    // sufficiently different signatures, then attempting to pass them to a map
    // & calling internally.
    // fcn takes a predicate 'p' and returns one of two fcns.
    //   let fcn = { p -> (if p {a -> pair[a,a        ]}
    //                               {b -> pair[b,pair[3,b]]}) } in
    // map takes a function and an element (collection?) and applies it (applies to collection?)
    //   let map = { fun x -> (fun x) }
    //          in { q -> ((map (fcn q)) 5) }
    // Should return { q -> q ? [5,5] : [5,[3,5]] }
    // Ultimately, unifies "a" with "pair[3,a]" which throws recursive unification.
    T2 t1 = HM.hm("fcn = {p -> (if p {a -> (pair a a)} {b -> (pair b (pair 3 b))})};"+
                  "map = { fun x -> (fun x)};"+
                  "{ q -> (map (fcn q) 5)}");
    assertEquals("TBD",t1.p());
  }

  @Test
  public void test18() {
    T2 t1 = HM.hm("cons ={x y-> {cadr -> (cadr x y)}};"+
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
    T2 t1 = HM.hm("cons ={x y-> {cadr -> (cadr x y)}};"+
                  "cdr ={mycons -> (mycons { p q -> q})};"+
                  "map ={fun parg -> (fun (cdr parg))};"+
                  "(pair (map str (cons 0 5)) (map isempty (cons 0 \"abc\")))"
                  );
    assertEquals("(pair str int1)",t1.p());
  }

  // Obscure factorial-like
  @Test
  public void test20() {
    T2 t1 = HM.hm("f0 = { f x -> (if (?0 x) 1 (f (f0 f (dec x)) 2))}; (f0 * 99)");
    assertEquals("int64",t1.p());
  }

  // Obscure factorial-like
  @Test
  public void test21() {
    // let f0 = fn f x => (if (?0 x) 1 (* (f0 f (dec x)) 2) ) in f0 f0 99
    // let f0 = fn f x => (if (?0 x) 1 (f (f0 f (dec x)) 2) ) in f0 *  99
    T2 t1 = HM.hm("f0 = { f x -> (if (?0 x) 1 (* (f0 f (dec x)) 2))}; (f0 f0 99)");
    assertEquals("int64",t1.p());
  }

  // Mutual recursion
  @Test
  public void test22() {
    T2 t1 = HM.hm("is_even = "+
                  "  is_odd = { n -> (if (?0 n) 0 (is_even (dec n)))}; "+
                  "     { n -> (if (?0 n) 1 (is_odd (dec n)))};"+
                  "(is_even 3)"
                  );
    assertEquals("int1",t1.p());
  }

  // Toss a function into a pair & pull it back out
  @Test
  public void test23() {
    T2 t1 = HM.hm("{ g -> fgz = "+
                  "         cons = {x y -> {cadr -> (cadr x y)}};"+
                  "         cdr = {mycons -> (mycons { p q -> q})};"+
                  "         (cdr (cons 2 { z -> (g z) }));"+
                  "      (pair (fgz 3) (fgz 5))"+
                  "}"
                  );
    assertEquals("{ { nint8 -> A } -> (pair A A) }",t1.p());
  }

  // Basic structure test
  @Test
  public void test24() {
    T2 t = HM.hm("@{x=2, y=3}");
    assertEquals("@{ x = 2, y = 3}",t.p());
  }

  // Basic field test
  @Test
  public void test25() {
    T2 t = HM.hm(".x @{x =2, y =3}");
    assertEquals("2",t.p());
  }

  @Test
  public void test26() {
    T2 t = HM.hm("{ g -> @{x=g, y=g}}");
    assertEquals("{ A -> @{ x = A, y = A} }",t.p());
  }

  @Test
  public void test27() {
    // Load common field 'x', ignoring mismatched fields y and z
    T2 t = HM.hm("{ pred -> .x (if pred @{x=2,y=3} @{x=3,z= \"abc\"}) }");
    assertEquals("{ A -> nint8 }",t.p());
  }

  @Test
  public void test28() {
    // Load some fields from an unknown struct: area of a square.
    // Since no nil-check, correct types as needing a not-nil input.
    T2 t = HM.hm("{ sq -> (* .x sq .y sq) }");
    assertEquals("{ @{ y = int64, x = int64} -> int64 }",t.p());
  }

  @Test
  public void test29() {
    // Recursive linked-list discovery, with no end clause
    T2 t = HM.hm("map = { fcn lst -> @{ n1 = (map fcn .n0 lst), v1 = (fcn .v0 lst) } }; map");
    assertEquals("{ { A -> B } C:@{ v0 = A, n0 = $C} -> D:@{ n1 = $D, v1 = B} }",t.p());
  }

  @Test
  public void test30() {
    // Recursive linked-list discovery, with nil
    T2 t = HM.hm("map = { fcn lst -> (if lst @{ n1=(map fcn .n0 lst), v1=(fcn .v0 lst) } nil) }; map");
    assertEquals("{ { A -> B } C:@{ v0 = A, n0 = $C}? -> D:@{ n1 = $D, v1 = B}? }",t.p());
  }

  // try the worse-case expo blow-up test case from SO
  @Test
  public void test31() {
    // Recursive linked-list discovery, with nil
    T2 t = HM.hm("p0 = { x y z -> (triple x y z) };"+
                 "p1 = (triple p0 p0 p0);"+
                 "p2 = (triple p1 p1 p1);"+
                 "p3 = (triple p2 p2 p2);"+
                 "p3");
    assertEquals("(triple (triple (triple { A B C -> (triple A B C) } { D E F -> (triple D E F) } { G H I -> (triple G H I) }) (triple { J K L -> (triple J K L) } { M N O -> (triple M N O) } { P Q R -> (triple P Q R) }) (triple { S T U -> (triple S T U) } { V21 V22 V23 -> (triple V21 V22 V23) } { V24 V25 V26 -> (triple V24 V25 V26) })) (triple (triple { V27 V28 V29 -> (triple V27 V28 V29) } { V30 V31 V32 -> (triple V30 V31 V32) } { V33 V34 V35 -> (triple V33 V34 V35) }) (triple { V36 V37 V38 -> (triple V36 V37 V38) } { V39 V40 V41 -> (triple V39 V40 V41) } { V42 V43 V44 -> (triple V42 V43 V44) }) (triple { V45 V46 V47 -> (triple V45 V46 V47) } { V48 V49 V50 -> (triple V48 V49 V50) } { V51 V52 V53 -> (triple V51 V52 V53) })) (triple (triple { V54 V55 V56 -> (triple V54 V55 V56) } { V57 V58 V59 -> (triple V57 V58 V59) } { V60 V61 V62 -> (triple V60 V61 V62) }) (triple { V63 V64 V65 -> (triple V63 V64 V65) } { V66 V67 V68 -> (triple V66 V67 V68) } { V69 V70 V71 -> (triple V69 V70 V71) }) (triple { V72 V73 V74 -> (triple V72 V73 V74) } { V75 V76 V77 -> (triple V75 V76 V77) } { V78 V79 V80 -> (triple V78 V79 V80) })))",t.p());
  }

  // Need to see if a map call, inlined a few times, 'rolls up'.  Sometimes
  // rolls up, sometimes not; depends on worklist visitation order.
  @Test
  public void test32() {
    // Recursive linked-list discovery, with nil.  Unrolled once.
    T2 t = HM.hm("map = { lst -> (if lst @{ n1= arg= .n0 lst; (if arg @{ n1=(map .n0 arg), v1=(str .v0 arg)} nil), v1=(str .v0 lst) } nil) }; map");
    assertEquals("{ A:@{ v0 = int64, n0 = @{ n0 = $A, v0 = int64}?}? -> B:@{ n1 = @{ n1 = $B, v1 = str}?, v1 = str}? }",t.p());
  }
}
