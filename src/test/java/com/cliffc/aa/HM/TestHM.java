package com.cliffc.aa.HM;

import com.cliffc.aa.HM.HM.*;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class TestHM {

  @Before public void reset() { HM.reset(); }

  @Test(expected = RuntimeException.class)
  public void test00() {
    HM.hm("fred");
  }

  @Test
  public void test01() {
    Syntax syn = HM.hm("3");
    assertEquals("3",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  @Test
  public void test02() {
    Syntax syn = HM.hm("(pair1 3)");
    assertEquals("{ A -> (pair 3 A) }",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  @Test
  public void test03() {
    Syntax syn = HM.hm("{ z -> (pair (z 3) (z \"abc\")) }");
    assertEquals("{ { all -> A } -> (pair A A) }",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  @Test
  public void test04() {
    Syntax syn = HM.hm("fact = { n -> (if (?0 n) 1 (* n (fact (dec n))))}; fact");
    assertEquals("{ int64 -> int64 }",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  @Test
  public void test05() {
    // Because {y->y} is passed in, all 'y' types must agree.
    // This unifies 3 and "abc" which results in 'all'
    Syntax syn = HM.hm("({ x -> (pair (x 3) (x \"abc\")) } {y->y})");
    assertEquals("(pair all all)",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  @Test//(expected = RuntimeException.class)  No longer throws, but returns a recursive type
  public void test06() {
    // recursive unification
    Syntax syn = HM.hm("{ f -> (f f) }");
    assertEquals("{ A:{ $A -> B } -> B }",syn._t.p());
    assertEquals("[]",syn._post.p());
    // We can argue the pretty-print should print:
    // "A:{ $A -> B }"
  }

  @Test
  public void test07() {
    Syntax syn = HM.hm("g = {f -> 5}; (g g)");
    assertEquals("5",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  @Test
  public void test08() {
    // example that demonstrates generic and non-generic variables:
    Syntax syn = HM.hm("{ g -> f = { x -> g }; (pair (f 3) (f \"abc\"))}");
    assertEquals("{ A -> (pair A A) }",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  @Test
  public void test09() {
    Syntax syn = HM.hm("{ f g -> (f g)}");
    assertEquals("{ { A -> B } A -> B }",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  @Test
  public void test10() {
    // Function composition
    Syntax syn = HM.hm("{ f g -> { arg -> (g (f arg))} }");
    assertEquals("{ { A -> B } { B -> C } -> { A -> C } }",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  @Test
  public void test11() {
    // Stacked functions ignoring all function arguments
    Syntax syn = HM.hm("map = { fun -> { x -> 2 } }; ((map 3) 5)");
    assertEquals("2",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  @Test
  public void test12() {
    // map takes a function and an element (collection?) and applies it (applies to collection?)
    Syntax syn = HM.hm("map = { fun -> { x -> (fun x)}}; { p -> 5 }");
    assertEquals("{ A -> 5 }",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  @Test
  public void test13() {
    // Looking at when tvars are duplicated ("fresh" copies made).
    // This is the "map" problem with a scalar instead of a collection.
    // Takes a '{a->b}' and a 'a' for a couple of different prims.
    Syntax syn = HM.hm("map = { fun -> { x -> (fun x)}};"+
                  "(pair ((map str) 5) ((map factor) 2.3))");
    assertEquals("(pair str (divmod flt64 flt64))",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  @Test
  public void test14() {
    // map takes a function and an element (collection?) and applies it (applies to collection?)
    Syntax syn = HM.hm("map = { fun x -> (fun x)}; (map {a->3} 5)");
    assertEquals("3",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  @Test
  public void test15() {
    // map takes a function and an element (collection?) and applies it (applies to collection?)
    Syntax syn = HM.hm("map = { fun x -> (fun x)}; (map { a-> (pair a a)} 5)");
    assertEquals("(pair 5 5)",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  @Test
  public void test16() {
    Syntax syn = HM.hm("fcn = { p -> { a -> (pair a a) }};"+
                  "map = { fun x -> (fun x)};"+
                  "{ q -> (map (fcn q) 5)}");
    assertEquals("{ A -> (pair 5 5) }",syn._t.p());
    assertEquals("[]",syn._post.p());
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
    Syntax syn = HM.hm("fcn = {p -> (if p {a -> (pair a a)} {b -> (pair b (pair 3 b))})};"+
                  "map = { fun x -> (fun x)};"+
                  "{ q -> (map (fcn q) 5)}");
    assertEquals("TBD",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  @Test
  public void test18() {
    Syntax syn = HM.hm("cons ={x y-> {cadr -> (cadr x y)}};"+
                  "cdr ={mycons -> (mycons { p q -> q})};"+
                  "(cdr (cons 2 3))");
    assertEquals("3",syn._t.p());
    assertEquals("[]",syn._post.p());
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
    Syntax syn = HM.hm("cons ={x y-> {cadr -> (cadr x y)}};"+
                  "cdr ={mycons -> (mycons { p q -> q})};"+
                  "map ={fun parg -> (fun (cdr parg))};"+
                  "(pair (map str (cons 0 5)) (map isempty (cons 0 \"abc\")))"
                  );
    assertEquals("(pair str int1)",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  // Obscure factorial-like
  @Test
  public void test20() {
    Syntax syn = HM.hm("f0 = { f x -> (if (?0 x) 1 (f (f0 f (dec x)) 2))}; (f0 * 99)");
    assertEquals("int64",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  // Obscure factorial-like
  @Test
  public void test21() {
    // let f0 = fn f x => (if (?0 x) 1 (* (f0 f (dec x)) 2) ) in f0 f0 99
    // let f0 = fn f x => (if (?0 x) 1 (f (f0 f (dec x)) 2) ) in f0 *  99
    Syntax syn = HM.hm("f0 = { f x -> (if (?0 x) 1 (* (f0 f (dec x)) 2))}; (f0 f0 99)");
    assertEquals("int64",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  // Mutual recursion
  @Test
  public void test22() {
    Syntax syn = HM.hm("is_even = "+
                  "  is_odd = { n -> (if (?0 n) 0 (is_even (dec n)))}; "+
                  "     { n -> (if (?0 n) 1 (is_odd (dec n)))};"+
                  "(is_even 3)"
                  );
    assertEquals("int1",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  // Toss a function into a pair & pull it back out
  @Test
  public void test23() {
    Syntax syn = HM.hm("{ g -> fgz = "+
                  "         cons = {x y -> {cadr -> (cadr x y)}};"+
                  "         cdr = {mycons -> (mycons { p q -> q})};"+
                  "         (cdr (cons 2 { z -> (g z) }));"+
                  "      (pair (fgz 3) (fgz 5))"+
                  "}"
                  );
    assertEquals("{ { nint8 -> A } -> (pair A A) }",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  // Basic structure test
  @Test
  public void test24() {
    Syntax syn = HM.hm("@{x=2, y=3}");
    assertEquals("*[7]@{ x = 2, y = 3}",syn._t.p());
    assertEquals("[  7:*[7]@{ x = 2, y = 3}]",syn._post.p());
  }

  // Basic field test
  @Test
  public void test25() {
    Syntax syn = HM.hm(".x @{x =2, y =3}");
    assertEquals("2",syn._t.p());
    assertEquals("[  7:*[7]@{ x = 2, y = 3}]",syn._post.p());
  }

  // Basic field test
  @Test(expected = RuntimeException.class)
  public void test25a() {
    Syntax syn = HM.hm(".x 5");
    assertEquals("TBD",syn._t.p()); // Cannot unify 5 and @{x=A}
  }

  // Basic field test.
  @Test(expected = RuntimeException.class)
  public void test25b() {
    Syntax syn = HM.hm(".x @{ y =3}");
    assertEquals("A",syn._t.p());
    assertEquals("[  7:*[7]@{ x = A, y = 3}]",syn._post.p());
  }

  @Test
  public void test26() {
    Syntax syn = HM.hm("{ g -> @{x=g, y=g}}");
    assertEquals("{ A -> *[7]@{ x = A, y = A} }",syn._t.p());
    assertEquals("[  7:*[7]@{ x = A, y = A}]",syn._post.p());
  }

  @Test
  public void test27() {
    // Load common field 'x', ignoring mismatched fields y and z
    Syntax syn = HM.hm("{ pred -> .x (if pred @{x=2,y=3} @{x=3,z= \"abc\"}) }");
    assertEquals("{ A -> nint8 }",syn._t.p());
    assertEquals("[  7:A:*[7,8]@{ x = nint8, z = all, y = all}, 8:$A]",syn._post.p());
  }

  @Test
  public void test28() {
    // Load some fields from an unknown struct: area of a square.
    // Since no nil-check, correctly types as needing a not-nil input.
    Syntax syn = HM.hm("{ sq -> (* .x sq .y sq) }"); // { sq -> sq.x * sq.y }
    assertEquals("{ *[-2]@{ y = int64, x = int64} -> int64 }",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  @Test
  public void test29() {
    // Recursive linked-list discovery, with no end clause
    Syntax syn = HM.hm("map = { fcn lst -> @{ n1 = (map fcn .n0 lst), v1 = (fcn .v0 lst) } }; map");
    assertEquals("{ { A -> B } C:*[-2]@{ v0 = A, n0 = $C} -> D:*[7]@{ n1 = $D, v1 = B} }",syn._t.p());
    assertEquals("[  7:A:*[7]@{ n1 = $A, v1 = B}]",syn._post.p());
  }

  @Test
  public void test30() {
    // Recursive linked-list discovery, with nil.  Note that the output memory
    // has the output memory alias, but not the input memory alias (which must
    // be made before calling 'map').
    Syntax syn = HM.hm("map = { fcn lst -> (if lst @{ n1=(map fcn .n0 lst), v1=(fcn .v0 lst) } nil) }; map");
    assertEquals("{ { A -> B } C:*[-2]@{ v0 = A, n0 = $C}? -> D:*[7]@{ n1 = $D, v1 = B}? }",syn._t.p());
    assertEquals("[  7:A:*[7]@{ n1 = $A, v1 = B}?]",syn._post.p());
  }

  @Test
  public void test30a() {
    // Recursive linked-list discovery, with no end clause
    Syntax syn = HM.hm("map = { fcn lst -> (if lst @{ n1 = (map fcn .n0 lst), v1 = (fcn .v0 lst) } nil) }; (map dec @{n0 = nil, v0 = 5})");
    assertEquals("A:*[7]@{ n1 = $A, v1 = int64}?",syn._t.p());
    assertEquals("[  7:A:*[7]@{ n1 = $A, v1 = B}?, 8:*[8]@{ n0 = (Nil), v0 = int64}?]",syn._post.p());
  }

  // try the worse-case expo blow-up test case from SO
  @Test
  public void test31() {
    // Recursive linked-list discovery, with nil
    Syntax syn = HM.hm("p0 = { x y z -> (triple x y z) };"+
                 "p1 = (triple p0 p0 p0);"+
                 "p2 = (triple p1 p1 p1);"+
                 "p3 = (triple p2 p2 p2);"+
                 "p3");
    assertEquals("(triple (triple (triple { A B C -> (triple A B C) } { D E F -> (triple D E F) } { G H I -> (triple G H I) }) (triple { J K L -> (triple J K L) } { M N O -> (triple M N O) } { P Q R -> (triple P Q R) }) (triple { S T U -> (triple S T U) } { V21 V22 V23 -> (triple V21 V22 V23) } { V24 V25 V26 -> (triple V24 V25 V26) })) (triple (triple { V27 V28 V29 -> (triple V27 V28 V29) } { V30 V31 V32 -> (triple V30 V31 V32) } { V33 V34 V35 -> (triple V33 V34 V35) }) (triple { V36 V37 V38 -> (triple V36 V37 V38) } { V39 V40 V41 -> (triple V39 V40 V41) } { V42 V43 V44 -> (triple V42 V43 V44) }) (triple { V45 V46 V47 -> (triple V45 V46 V47) } { V48 V49 V50 -> (triple V48 V49 V50) } { V51 V52 V53 -> (triple V51 V52 V53) })) (triple (triple { V54 V55 V56 -> (triple V54 V55 V56) } { V57 V58 V59 -> (triple V57 V58 V59) } { V60 V61 V62 -> (triple V60 V61 V62) }) (triple { V63 V64 V65 -> (triple V63 V64 V65) } { V66 V67 V68 -> (triple V66 V67 V68) } { V69 V70 V71 -> (triple V69 V70 V71) }) (triple { V72 V73 V74 -> (triple V72 V73 V74) } { V75 V76 V77 -> (triple V75 V76 V77) } { V78 V79 V80 -> (triple V78 V79 V80) })))",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  // Need to see if a map call, inlined a few times, 'rolls up'.  Sometimes
  // rolls up, sometimes not; depends on worklist visitation order.
  @Test
  public void test32() {
    // Recursive linked-list discovery, with nil.  Unrolled once.
    Syntax syn = HM.hm("map = { lst -> (if lst @{ n1= arg= .n0 lst; (if arg @{ n1=(map .n0 arg), v1=(str .v0 arg)} nil), v1=(str .v0 lst) } nil) }; map");
    assertEquals("{ A:*[-2]@{ v0 = int64, n0 = *[-2]@{ n0 = $A, v0 = int64}?}? -> B:*[8]@{ n1 = *[7]@{ n1 = $B, v1 = str}?, v1 = str}? }",syn._t.p());
    assertEquals("[  7:A:*[7]@{ n1 = B:*[8]@{ n1 = $A, v1 = str}?, v1 = str}?, 8:$B]",syn._post.p());
  }

  @Test
  public void test33() {
    Syntax syn = HM.hm("x = { y -> (x (y y))}; x");
    assertEquals("{ A:{ $A -> $A } -> B }",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  @Test
  public void test34() {
    try {
      // Example from SimpleSub requiring 'x' to be both a struct with field
      // 'v', and also a function type - specifically disallowed in 'aa'.
      HM.hm("{ x -> y = ( x .v x ); 0}");
    } catch( RuntimeException e ) {
      assertEquals("Cannot unify *[-2]@{ v = V40} and { V40 -> V34 }",e.getMessage());
    }
  }
  
  @Test
  public void test35() {
    Syntax syn = HM.hm("x = { z -> z}; (x { y -> .u y})");
    assertEquals("{ *[-2]@{ u = A} -> A }",syn._t.p());
    assertEquals("[]",syn._post.p());
  }

  @Test
  public void test36() {
    try {
      // Example from SimpleSub requiring 'x' to be both:
      // - a recursive self-call function from "w = (x x)": $V66:{ $V66 -> V67 } AND
      // - a function which takes a struct with field 'u'
      // The first arg to x is two different kinds of functions, so fails unification.
      HM.hm("x = w = (x x); { z -> z}; (x { y -> .u y})");
    } catch( RuntimeException e ) {
      assertEquals("Cannot unify $V66:{ $V66 -> V67 } and *[-2]@{ u = V39}",e.getMessage());
    }
  }

}
