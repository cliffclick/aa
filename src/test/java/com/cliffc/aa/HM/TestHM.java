package com.cliffc.aa.HM;

import com.cliffc.aa.HM.HM.Root;
import com.cliffc.aa.type.Type;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

/*
  Theory: can move the update_root_args back into root._val, and remove pass#2
  Theory: HMT fidxs/aliases carry No Useful Info, other than the "is_fun" bit & nil bit.
 */

public class TestHM {

  private void _run0s( String prog, String rez_hm, String frez_gcp, int rseed ) {
    HM.reset();
    Root syn = HM.hm(prog, rseed, rez_hm!=null, frez_gcp!=null );
    if(  rez_hm !=null )  assertEquals(stripIndent(rez_hm),stripIndent(syn._hmt.p()));
    if( frez_gcp!=null )  assertEquals(Type.valueOf(frez_gcp),syn.flow_type());
  }

  private static final int[] rseeds = new int[]{0,1,2,3};
  private void _run1s( String prog, String rez_hm, String frez_gcp ) {
    for( int rseed : rseeds )
      //for( int rseed=0; rseed<64; rseed++ )
      _run0s(prog,rez_hm,frez_gcp,rseed);
  }

  // Run same program in all 3 combinations, but answers vary across combos
  private void run( String prog, String rez_hm_gcp, String rez_hm_alone, String frez_gcp_hm, String frez_gcp_alone ) {
    _run1s(prog,rez_hm_gcp  ,frez_gcp_hm   );
    _run1s(prog,rez_hm_alone,null          );
    _run1s(prog,null        ,frez_gcp_alone);
  }
  private void run( String prog, String rez_hm, String frez_gcp ) {
    _run1s(prog,rez_hm,frez_gcp);
    _run1s(prog,rez_hm,null    );
    _run1s(prog,null  ,frez_gcp);
  }

  private static String stripIndent(String s){ return s.replace("\n","").replace(" ",""); }


  @Test(expected = RuntimeException.class)
  public void test00() { run( "fred","","all"); }

  @Test public void test01() { run( "3", "3", "3");  }

  @Test public void test02() { run( "{ x -> (pair 3 x) }" ,
                                    "{ A -> ( 3, A) }",
                                    "[18]{any,1 -> *[8](^=any,3,Scalar)}"); }

  @Test public void test03() { run( "{ z -> (pair (z 0) (z \"abc\")) }" ,
                                    "{ { *[0,4]str:(97) -> A } -> ( A, A) }",
                                    "[18]{any,1 ->*[8](^=any, Scalar, Scalar) }");
  }

  @Test public void test04() {
    run( "fact = { n -> (if (eq0 n) 1 (* n (fact (dec n))))}; fact",
         "{ int64 -> int64 }",
         "[21]{any,1 -> int64 }"
         );
  }

  // Because {y->y} is passed in, all 'y' types must agree.
  // This unifies 3 and 5 which results in 'nint8'
  @Test public void test05() {
    run("({ id -> (pair (id 3) (id 5)) } {x->x})",
        "( nint8, nint8)",
        "*[8](^=any, nint8, nint8)");
  }

  @Test public void test06() {
    run("id={x->x}; (pair (id 3) (id \"abc\"))",
        // HM is sharper here than in test05, because id is generalized per each use site
        "( 3, *[4]str:(97))",
        "( 3, *[4]str:(97))",
        // GCP with HM
        "*[8](^=any, 3, *[4]str:(97))",
        // GCP is weaker without HM
        "*[8](^=any, nScalar, nScalar)");
  }

  // recursive unification; normal H-M fails here.
  @Test public void test07() {
    run( "{ f -> (f f) }",
         // We can argue the pretty-print should print:
         // "  A:{ A -> B }"
         "{ A:{ A -> B } -> B }",
         "[17]{any,1 ->Scalar }");
  }

  @Test public void testYcombo() {
    run( "{ f -> ({ x -> (f (x x))} { x -> (f (x x))})}",
         "{{ A -> A } -> A }",
         "{{ A -> A } -> A }",
         "[19]{any,1 -> Scalar }",
         "[19]{any,1 -> Scalar }");
  }

  @Test public void test08() { run( "g = {f -> 5}; (g g)",  "5", "5"); }

  // example that demonstrates generic and non-generic variables:
  @Test public void test09() { run( "{ g -> f = { ignore -> g }; (pair (f 3) (f \"abc\"))}",
                                    "{ A -> ( A, A) }",
                                    "[19]{any,1 ->*[8](^=any, Scalar, Scalar) }"); }

  @Test public void test10() { run( "{ f g -> (f g)}",
                                    "{ { A -> B } A -> B }",
                                    "[17]{any,2 ->Scalar }"); }

  // Function composition
  @Test public void test11() { run( "{ f g -> { arg -> (g (f arg))} }",
                                    "{ { A -> B } { B -> C } -> { A -> C } }",
                                    "[18]{any,2 ->[17]{any,1 ->Scalar } }"); }

  // Stacked functions ignoring all function arguments
  @Test public void test12() { run( "map = { fun -> { x -> 2 } }; ((map 3) 5)", "2", "2"); }

  // map takes a function and an element (collection?) and applies it (applies to collection?)
  @Test public void test13() { run( "map = { fun -> { x -> (fun x)}}; { p -> 5 }",
                                    "{ A -> 5 }",  "[19]{any,1 -> 5 }"); }


  // Looking at when tvars are duplicated ("fresh" copies made).
  // This is the "map" problem with a scalar instead of a collection.
  // Takes a '{a->b}' and a 'a' for a couple of different prims.
  @Test public void test14() {
    run("map = { fun -> { x -> (fun x)}};"+
        "(pair ((map str) 5) ((map factor) 2.3))",
        "( *[4]str:(), flt64)",
        "( *[4]str:(), flt64)",
        "*[8](^=any, *[4]str:(), flt64)",
        "*[8](^=any, Scalar, Scalar)");
  }

  // map takes a function and an element (collection?) and applies it (applies to collection?)
  @Test public void test15() { run("map = { fun x -> (fun x)}; (map {a->3} 5)", "3", "3"); }

  // map takes a function and an element (collection?) and applies it (applies to collection?)
  @Test public void test16() { run("map = { fun x -> (fun x)}; (map { a-> (pair a a)} 5)", "( 5, 5)", "*[8](^=any, 5, 5)"); }

  @Test public void test17() { run("""
fcn = { p -> { a -> (pair a a) }};
map = { fun x -> (fun x)};
{ q -> (map (fcn q) 5)}
""",
                                   "{ A -> ( 5, 5) }", "[21]{any,1 ->*[8](^=any, 5, 5) }"); }

  // Checking behavior when using "if" to merge two functions with sufficiently
  // different signatures, then attempting to pass them to a map & calling internally.
  // fcn takes a predicate 'p' and returns one of two fcns.
  //   let fcn = { p -> (if p {a -> pair[a,a        ]}
  //                          {b -> pair[b,pair[3,b]]}) } in
  // map takes a function and an element (collection?) and applies it (applies to collection?)
  //   let map = { fun x -> (fun x) }
  //          in { q -> ((map (fcn q)) 5) }
  // Should return { q -> q ? [7,5] : [7,[3,5]] }
  // Ultimately, unifies "a" with "pair[3,a]" which throws recursive unification.
  @Test public void test18() {
    run("fcn = {p -> (if p {a -> (pair a a)} {b -> (pair b (pair 3 b))})};"+
        "map = { fun x -> (fun x)};"+
        "{ q -> (map (fcn q) 5)}",
        "{ A? -> ( B:Cannot unify 5 and ( 3, B), B) }",
        "[27]{any,1 -> *[8,9](^=any, 5, nScalar) }");
  }

  @Test public void test19() { run("cons ={x y-> {cadr -> (cadr x y)}};"+
                                   "cdr ={mycons -> (mycons { p q -> q})};"+
                                   "(cdr (cons 2 3))",
                                   "3", "3"); }

  // Take 2nd element of pair, and applies a function.
  //    let map = fn parg fun => (fun (cdr parg))
  // Some pairs:
  //    let intz = (pair2 false 3)
  //    let strz = (pair2 false "abc")
  // in pair(map(str,intz),map(isempty,strz))
  // Expects: ("2",false)
  @Test public void test20() {
    run("""
cons ={x y-> {cadr -> (cadr x y)}};
cdr ={mycons -> (mycons { p q -> q})};
map ={fun parg -> (fun (cdr parg))};
(pair (map str (cons 0 5)) (map isempty (cons 0 "abc")))
""",
        "( *[4]str:(), int1)",
        "( *[4]str:(), int1)",
        "*[8](^=any, *[4]str:(), int64)",
        "*[8](^=any, Scalar, Scalar)");
  }

  // Obscure factorial-like
  @Test public void test21() {
    run("f0 = { f x -> (if (eq0 x) 1 (f (f0 f (dec x)) 2))}; (f0 * 99)",
        "int64","int64",
        "int64","int64");
  }

  // Obscure factorial-like
  // let f0 = fn f x => (if (eq0 x) 1 (* (f0 f (dec x)) 2) ) in f0 f0 99
  // let f0 = fn f x => (if (eq0 x) 1 (f (f0 f (dec x)) 2) ) in f0 *  99
  @Test public void test22() { run("f0 = { f x -> (if (eq0 x) 1 (* (f0 f (dec x)) 2))}; (f0 f0 99)",
                                   "int64", "int64"); }

  // Mutual recursion
  @Test public void test23() {
    run("is_even = "+
        "  is_odd = { n -> (if (eq0 n) 0 (is_even (dec n)))}; "+
        "     { n -> (if (eq0 n) 1 (is_odd (dec n)))};"+
        "(is_even 3)" ,
        "int1", "int1");
  }

  // Toss a function into a pair & pull it back out
  @Test public void test24() {
    run("""
{ g -> fgz =
         cons = {x y -> {cadr -> (cadr x y)}};
         cdr = {mycons -> (mycons { p q -> q})};
         (cdr (cons 2 { z -> (g z) }));
      (pair (fgz 3) (fgz 5))
}
""",
        "{ { nint8 -> A } -> ( A, A) }",
        "[23]{any,1 ->*[8](^=any, Scalar, Scalar) }");
  }

  // Basic structure test
  @Test public void test25() {
    run("@{x=2, y=3}",
        "@{ x = 2; y = 3}",
        "*[8]@{^=any; x=2; y=3}");
  }

  // Basic field test
  @Test public void test26() { run("@{x =2, y =3}.x", "2", "2"); }

  // Basic field test
  @Test public void test27() { run("5.x", "Missing field x in 5", "Scalar"); }

  // Basic field test.
  @Test public void test28() { run("@{ y =3}.x", "Missing field x in @{ y = 3}", "Scalar"); }

  @Test public void test29() { run("{ g -> @{x=g, y=g}}",
                                   "{ A -> @{ x = A; y = A} }",
                                   "[17]{any,1 ->*[8]@{^=any; x=Scalar; y=Scalar} }"); }

  // Load common field 'x', ignoring mismatched fields y and z
  @Test public void test30() {
    run("{ pred -> (if pred @{x=2,y=3} @{x=3,z= \"abc\"}) .x }",
        "{ A? -> nint8 }",
        "[20]{any,1 ->nint8 }"); }

  // Load some fields from an unknown struct: area of a rectangle.
  // Since no nil-check, correctly types as needing a not-nil input.
  @Test public void test31() { run("{ sq -> (* sq.x sq.y) }", // { sq -> sq.x * sq.y }
                                   "{ @{ x = int64; y = int64; ...} -> int64 }",
                                   "[18]{any,1 ->int64 }");
  }

  // Recursive linked-list discovery, with no end clause.  Since this code has
  // no exit (it is an infinite loop, endlessly reading from an infinite input
  // and writing an infinite output), gcp gets a cyclic approximation.
  @Test public void test32() {
    run("map = { fcn lst -> @{ n1 = (map fcn lst.n0), v1 = (fcn lst.v0) } }; map",
        "{ { A -> B } C:@{ n0 = C; v0 = A; ...} -> D:@{ n1 = D; v1 = B} }",
        "[17]{any,2 ->PA:*[8]@{^=any; n1=PA; v1=Scalar} }");
  }

  // Recursive linked-list discovery, with nil.  Note that the output memory
  // has the output memory alias, but not the input memory alias (which must be
  // made before calling 'map').
  @Test public void test33() {
    run("map = { fcn lst -> (if lst @{ n1=(map fcn lst.n0), v1=(fcn lst.v0) } 0) }; map",
        "{ { A -> B } C:@{ n0 = C; v0 = A; ...}? -> D:@{ n1 = D; v1 = B}? }",
        "[20]{any,2 ->PA:*[0,8]@{^=any; n1=PA; v1=Scalar} }");
  }

  // Recursive linked-list discovery, applied
  @Test public void test34() {
    run("map = { fcn lst -> (if lst @{ n1 = (map fcn lst.n0), v1 = (fcn lst.v0) } 0) }; (map dec @{n0 = 0, v0 = 5})",
        "A:@{ n1 = A; v1 = int64}?",
        "PA:*[0,8]@{^=any; n1=PA; v1=4}");
  }

  // try the worse-case expo blow-up test case from SO
  @Test public void test35() {
    String rez_hm = "( ( ( { A B C -> ( A, B, C) }, { D E F -> ( D, E, F) }, { G H I -> ( G, H, I) }), ( { J K L -> ( J, K, L) }, { M N O -> ( M, N, O) }, { P Q R -> ( P, Q, R) }), ( { S T U -> ( S, T, U) }, { V22 V23 V24 -> ( V22, V23, V24) }, { V25 V26 V27 -> ( V25, V26, V27) })), ( ( { V28 V29 V30 -> ( V28, V29, V30) }, { V31 V32 V33 -> ( V31, V32, V33) }, { V34 V35 V36 -> ( V34, V35, V36) }), ( { V37 V38 V39 -> ( V37, V38, V39) }, { V40 V41 V42 -> ( V40, V41, V42) }, { V43 V44 V45 -> ( V43, V44, V45) }), ( { V46 V47 V48 -> ( V46, V47, V48) }, { V49 V50 V51 -> ( V49, V50, V51) }, { V52 V53 V54 -> ( V52, V53, V54) })), ( ( { V55 V56 V57 -> ( V55, V56, V57) }, { V58 V59 V60 -> ( V58, V59, V60) }, { V61 V62 V63 -> ( V61, V62, V63) }), ( { V64 V65 V66 -> ( V64, V65, V66) }, { V67 V68 V69 -> ( V67, V68, V69) }, { V70 V71 V72 -> ( V70, V71, V72) }), ( { V73 V74 V75 -> ( V73, V74, V75) }, { V76 V77 V78 -> ( V76, V77, V78) }, { V79 V80 V81 -> ( V79, V80, V81) })))";
    run("p0 = { x y z -> (triple x y z) };"+
        "p1 = (triple p0 p0 p0);"+
        "p2 = (triple p1 p1 p1);"+
        "p3 = (triple p2 p2 p2);"+
        "p3",

        rez_hm, rez_hm,
        // TODO: Losing in the combo, because need to field-expand during apply-lift
        "*[11](FA:^=any, PB:*[10](FA, PA:*[9](FA, XA:[18]{any,3 ->*[8](FA, Scalar, Scalar, Scalar) }, XA, XA), PA, PA), PB, PB)",
        "*[11](FA:^=any, PB:*[10](FA, PA:*[9](FA, XA:[18]{any,3 ->*[8](FA, Scalar, Scalar, Scalar) }, XA, XA), PA, PA), PB, PB)" );
  }

  // Need to see if a map call, inlined a few times, 'rolls up'.  Sometimes
  // rolls up, sometimes not; depends on worklist visitation order.
  @Test public void test36() {
    run("map = { lst -> (if lst @{ n1= arg= lst.n0; (if arg @{ n1=(map arg.n0), v1=(str arg.v0)} 0), v1=(str lst.v0) } 0) }; map",
        "{ A:@{ n0 = @{ n0 = A; v0 = int64; ...}?; v0 = int64; ...}? -> B:@{ n1 = @{ n1 = B; v1 = *[4]str:()}?; v1 = *[4]str:()}? }",
        "[25]{any,1 ->PA:*[0,9]@{FA:^=any; n1=*[0,8]@{FA; n1=PA; FB:v1=*[4]str:()}; FB} }");
  }

  @Test public void test37() { run("x = { y -> (x (y y))}; x",
                                   "{ A:{ A -> A } -> B }", "[17]{any,1 ->~Scalar }"); }

  // Example from SimpleSub requiring 'x' to be both a struct with field
  // 'v', and also a function type - specifically disallowed in 'aa'.
  @Test public void test38() { run("{ x -> y = ( x x.v ); 0}",
                                   "{ { A:Missing field v in {A->B} -> B } -> C? }",
                                   "[17]{any,1 ->nil }"); }

  // Awful flow-type: function can be called from the REPL with any
  // argument type - and the worse case will be an error.
  @Test public void test39() {
    run("x = { z -> z}; (x { y -> y.u})",
        "{ @{ u = A; ...} -> A }",
        "[18]{any,1 ->Scalar }");
  }

  // Example from SimpleSub requiring 'x' to be both:
  // - a recursive self-call function from "w = (x x)": $V66:{ $V66 -> V67 } AND
  // - a function which takes a struct with field 'u'
  // The first arg to x is two different kinds of functions, so fails unification.
  @Test public void test40() {
    run("x = w = (x x); { z -> z}; (x { y -> y.u})",
        "A:Cannot unify { A -> A } and @{ u = A; ... }",
        "A:Cannot unify { A -> A } and @{ u = A; ... }",
        "[2,17,18]{any,1 ->Scalar }",
        "Scalar");
  }

  // Example from TestParse.test15:
  //   map={lst fcn -> lst ? fcn lst.1};
  //   in_int=(0,2);"+       // List of ints
  //   in_str=(0,"abc");" +  // List of strings
  //   out_str = map(in_int,str:{int->str});"+        // Map over ints with int->str  conversion, returning a list of strings
  //   out_bool= map(in_str,{str -> str==\"abc\"});"+ // Map over strs with str->bool conversion, returning a list of bools
  //   (out_str,out_bool)",
  @Test public void test41() {
    run("""
map={lst fcn -> (fcn lst.y) };
in_int=@{ x=0 y=2};
in_str=@{ x=0 y="abc"};
out_str = (map in_int str);
out_bool= (map in_str { xstr -> (eq xstr "def")});
(pair out_str out_bool)
""",
        "( *[4]str:(), int1)",
        "( *[4]str:(), int1)",
        "*[10](^=any, *[4]str:(), int64)",
        "*[10](^=any, Scalar, Scalar)");
  }

  // CCP Can help HM
  @Test public void test42() {
    run("pred = 0; s1 = @{ x=\"abc\" }; s2 = @{ y=3.4 }; (if pred s1 s2).y",
        "3.4f",
        "Missing field y in ( )",
        "3.4f",
        "3.4f");
  }

  // The z-merge is ignored; the last s2 is a fresh (unmerged) copy.
  @Test public void test43() {
    run("pred = 0; s1 = @{ x=\"abc\" }; s2 = @{ y=3.4 }; z = (if pred s1 s2).x; s2.y",
        "3.4f","3.4f");
  }

  @Test public void test44() {
    run("fun = (if (isempty \"abc\") {x->x} {x->1.2}); (fun @{})",
        "1.2f",
        "Cannot unify 1.2f and ()",
        "1.2f","1.2f");
  }

  // Requires a combo of HM and GCP to get the good answer
  @Test public void test45() {
    run("""
id = {x -> x};
loop = { name cnt ->
  (if cnt
    (loop
       fltfun = (if name id {x->3});
       (fltfun "abc")
       (dec cnt)
     )
     name
   )
};
(loop "def" (id 2))
""",
        "*[0,4]str:(nint8)",  // Both HM and GCP
        "Cannot unify int8 and *[0,4]str:(nint8)", // HM alone cannot do this one
        "*[4]str:(97)",       // Both HM and GCP
        "nScalar");           // GCP alone gets a very weak answer
  }


  // Basic nil test
  @Test public void test46() { run("0.x",
                                   "May be nil when loading field x", "~Scalar"); }

  // Basic nil test
  @Test public void test47() { run("{ pred -> (if pred @{x=3} 0).x}",
                                   "{ A? -> May be nil when loading field x }", "[20]{any,1 ->3 }"); }

  // Basic uplifting after check
  @Test public void test48() { run("{ pred -> tmp=(if pred @{x=3} 0); (if tmp tmp.x 4) }",
                                   "{ A? -> nint8 }", "[23]{any,1 ->nint8 }"); }


  // map is parametric in nil-ness
  @Test public void test49() {
    run("""
{ pred ->
  map = { fun x -> (fun x) };
  (pair (map {str0 ->          str0.x   }          @{x = 3}   )
        (map {str1 -> (if str1 str1.x 4)} (if pred @{x = 5} 0))
  )
}
""",
        "{ A? -> ( 3, nint8) }",
        "{ A? -> ( 3, nint8) }",
        "[27]{any,1 ->*[8](^=any,     3, nint8) }",
        "[27]{any,1 ->*[8](^=any, nint8, nint8) }");
  }

  // map is parametric in nil-ness.  Verify still nil-checking.
  @Test public void test50() {
    run("""
{ pred ->
  map = { fun x -> (fun x) };
  (pair (map {str0 ->          str0.x   }          @{x = 3}   )
        (map {str1 ->          str1.x   } (if pred @{x = 5} 0))
  )
}
""",
        "{ A? -> ( 3, May be nil when loading field x ) }",
        "{ A? -> ( 3, May be nil when loading field x ) }",
        "[24]{any,1 ->*[8](^=any,     3,     5) }",
        "[24]{any,1 ->*[8](^=any, nint8, nint8) }");
  }

  @Test public void test51() {
    run("total_size = { a as ->" +  // Total_size takes an 'a' and a list of 'as'
        "  (if as "+                // If list is not empty then
        "      (+ a.size "+         // Add the size of 'a' to
        "         (total_size as.val as.next))" + // the size of the rest of the list
        "      a.size"+             // Else the list is empty, just take the a.size
        "  )"+                      // End of (if as...)
        "};" +                      // End of total_size={...}
        "total_size",               // What is this type?
        "{ A:@{ size = int64; ...} B:@{ next = B; val = A; ...}? -> int64 }",
        "{ A:@{ size = int64; ...} B:@{ next = B; val = A; ...}? -> int64 }",
        "[21]{any,2 ->int64 }",
        "[21]{any,2 ->Scalar }");
  }

  // Create a boolean-like structure, and unify.
  @Test public void test52() {
    run("void = @{};"+              // Same as '()'; all empty structs are alike
        "true = @{"+                // 'true' is a struct with and,or,then
        "  and= {b -> b}"+
        "  or = {b -> true}"+
        "  then = {then else->(then void) }"+
        "};"+
        "false = @{"+               // 'false' is a struct with and,or,then
        "  and= {b -> false}"+
        "  or = {b -> b}"+
        "  then = {then else->(else void) }"+
        "};"+
        "forceSubtyping ={b ->(if b true false)};"+ // A unified version
        // Trying really hard here to unify 'true' and 'false'
        "bool=@{true=(forceSubtyping 1), false=(forceSubtyping 0), force=forceSubtyping};"+
        // Apply the unified 'false' to two different return contexts
        "testa=(bool.false.then { x-> 3 } { y-> 4 });"+
        "testb=(bool.false.then { z->@{}} { z->@{}});"+
        // Look at the results
        "@{a=testa, b=testb, bool=bool}"+
        "",
        "@{ a = nint8; b = ( ); bool = @{ false = A:@{ and = { A -> A }; or = { A -> A }; then = { { ( ) -> B } { ( ) -> B } -> B }}; force = { C? -> D:@{ and = { D -> D }; or = { D -> D }; then = { { ( ) -> E } { ( ) -> E } -> E }} }; true = F:@{ and = { F -> F }; or = { F -> F }; then = { { ( ) -> G } { ( ) -> G } -> G }}}}",
        "@{ a = nint8; b = ( ); bool = @{ false = A:@{ and = { A -> A }; or = { A -> A }; then = { { ( ) -> B } { ( ) -> B } -> B }}; force = { C? -> D:@{ and = { D -> D }; or = { D -> D }; then = { { ( ) -> E } { ( ) -> E } -> E }} }; true = F:@{ and = { F -> F }; or = { F -> F }; then = { { ( ) -> G } { ( ) -> G } -> G }}}}",
        "*[14]@{FA:^=any; a=int64 ; b=*[ALL](); bool=*[11]@{ FA; true=PA:*[9,10]@{FA; and=[17,20]{any,1 ->Scalar }; or=[18,21]{any,1 ->Scalar }; then=[19,22]{any,2 ->Scalar }}; false=PA; force=[26]{any,1 ->PA }}}",
        "*[14]@{FA:^=any; a=Scalar; b=Scalar  ; bool=*[11]@{ FA; true=PA:*[9,10]@{FA; and=[17,20]{any,1 ->Scalar }; or=[18,21]{any,1 ->Scalar }; then=[19,22]{any,2 ->Scalar }}; false=PA; force=[26]{any,1 ->PA }}}");
  }


  // Simple nil/default test; takes a nilable but does not return one.
  @Test public void test53() { run( "{ x y -> (if x x y) }",
                                    "{ A? A -> A }", "[20]{any,2 ->Scalar }");  }

  // Regression test; double nested.  Failed to unify x and y.
  @Test public void test54() { run( "{ x y -> (if x (if x x y) y) }",
                                    "{ A? A -> A }", "[23]{any,2 ->Scalar }");  }


  // Regression test; was NPE.  Was testMyBoolsNullPException from marco.servetto@gmail.com.
  @Test public void test55() {
    run("""
void = @{};
true = @{
  and      = {b -> b}
  or       = {b -> true}
  not      = {unused ->true}
  then = {then else->(then void) }
};
false = @{
  and      = {b -> false}
  or       = {b -> b}
  not      = {unused ->true}
  then = {then else->(else void) }
};
boolSub ={b ->(if b true false)};
@{true=(boolSub 1) false=(boolSub 0)}
""",
        "@{ false = A:@{ and = { A -> A }; "+
              "not = { B -> A }; "+
              "or = { A -> A }; "+
              "then = { { ( ) -> C } { ( ) -> C } -> C }"+
            "}; "+
            "true = D:@{ and = { D -> D }; "+
              "not = { E -> D }; "+
              "or = { D -> D }; "+
              "then = { { ( ) -> F } { ( ) -> F } -> F }"+
            "}"+
        "}",
        "*[11]@{ FA:^=any; true=PB:*[9,10]@{FA; and=[17,21]{any,1 ->Scalar }; or=[18,22]{any,1 ->Scalar }; not=[19,23]{any,1 -> PA:*[9]@{FA; and=[17]{any,1 ->Scalar }; or=[18]{any,1 ->PA }; not=[19]{any,1 ->PA }; then=[20]{any,2 ->Scalar }} }; then=[20,24]{any,2 ->Scalar } }; false=PB}");
  }

  // Regression test.  Was unexpectedly large type result.  Cut down version of
  // test from marco.servetto@gmail.com.  Looks like it needs some kind of
  // top-level unification with the true->false->true path, and instead the
  // type has an unrolled instance of the 'true' type embedded in the 'false'
  // type.  Bug is actually a core HM algorithm change to handle cycles.
  @Test public void test56() {
    run("left =     "+
        "  rite = @{n1 = left v1 = 7 }; "+
        "  @{ n1 = rite v1 = 7 };"+
        "left"+
        "",
        "A:@{ n1 = @{ n1 = A; v1 = 7}; v1 = 7}",
        "PA:*[9]@{FA:^=any; n1=*[8]@{FA; n1=PA; FB:v1=7}; FB}");
  }

  @Test public void test57() {
    run("""
all =
true = @{
  not = {unused -> all.false},
  then = {then else->(then 7) }
};
false = @{
  not = {unused -> all.true},
  then = {then else->(else 7) }
};
boolSub ={b ->(if b true false)};
@{true=true, false=false, boolSub=boolSub};
all
""",
        "@{ boolSub = { A? -> @{ not = { B -> C:@{ not = { D -> C }; then = { { 7 -> E } { 7 -> E } -> E }} }; then = { { 7 -> F } { 7 -> F } -> F }} }; false = C; true = C}",
        """
*[10]@{
  FA:^=any;
  true=PA:*[8]@{
    FA;
    not=[17]{any,1 ->
      PB:*[9]@{FA; not=[19]{any,1 ->PA }; then=[20]{any,2 ->Scalar }}
    };
    then=[18]{any,2 ->Scalar }
  };
  false=PB;
  boolSub=[24]{any,1 ->
    PC:*[8,9]@{FA; not=[17,19]{any,1 ->PC }; then=[18,20]{any,2 ->Scalar }}
  }
}
""");
  }

  // Full on Peano arithmetic.
  @Test public void test58() {
   run("""
void = @{};
err  = {unused->(err unused)};
// Booleans, support AND, OR, THEN/ELSE.
b=
  true = @{
    and_ = {o -> o}        // true AND anything is that thing
    or__ = {o -> b.true}   // true OR  anything is true
    then = {then else->(then void) }
  };
  false = @{
    and_ = {o -> b.false}  // false AND anything is false
    or__ = {o -> o}        // false OR  anything is that thing
    then = {then else->(else void) }
  };
  @{true=true, false=false};
// Natural numbers are formed from zero (z) and succ (s).
// They are structs which support zero, pred, succ and add.
n=
// Zero, is a struct supporting functions "zero" (always true), "pred"
// (error; no predecessor of zero), "succ" successor, and "add_" which is a no-op.
  z = @{
    zero = {unused ->b.true},
    pred = err
    succ = {unused -> (n.s n.z)},
    add_ = {o-> o}
  };
// Successor, is a function taking a natural number and returning the successor
// (which is just a struct supporting the functions of natural numbers).
  s = { pred ->
    self=@{
      zero = {unused ->b.false},  // zero is always false for anything other than zero
      pred = {unused -> pred },   // careful! 'pred=' is a label, the returned 'pred' was given as the argument 'pred->'
      succ = {unused -> (n.s self)},
      add_ = {m -> ((pred.add_ m).succ void)} // a little odd, but really this counts down (via recursion) on the LHS and applies that many succ on the RHS
    };
    self
  };
  @{s=s, z=z};
// Do some Maths
one = (n.s n.z);      // One is the successor of zero
two = (one.add_ one); // Two is one plus one
three =(n.s two);     // Three is the successor of two
// Return a result, so things are not dead.
@{b=b,n=n, one=one,two=two,three=three}
""",
        "@{" +
        // Booleans, support AND, OR, THEN/ELSE.  Eg. b.false.and is a function which
        // ignores its input and returns false.
        "  b=@{ false=A:@{ and_={B->A}; or__={C->C}; then={D {()->E} ->E} };"+
        "       true =F:@{ and_={G->G}; or__={H->F}; then={{()->I} J ->I} }"+
        "  };"+
        // Natural numbers are formed from zero (z) and succ (s).
        "  n=@{"+
        "    s={"+
        // K is the type var of a natural number: a struct supporting pred,succ,add,zero.
        // So 's' succ is a function which takes a natural number (K) and returns a K.
        "      K:@{ add_={ L:@{ succ={()->L}; ...} ->L };"+
        "           pred={ M -> K};"+
        "           succ={ N -> K};"+
        "           zero={ O -> P:@{ and_={P->P}; or__={P->P}; then={ {()->Q} {()->Q} -> Q }}}"+
        "        } -> K };"+
        "    z=K"+         // Zero is also a natural number
        "  };"+
        // One is formed by taking the successor of zero: "(n.s n.z)".  It has the same
        // shape as any natural number ("self" structural shape above), but its type is
        // not unified with "self".
        "  one=R:@{"+
        "    add_={ S:@{ succ={()->S}; ...} -> S};"+
        "    pred={ T -> R };"+
        "    succ={ U -> R };"+ // Note: succ takes an 'unused'
        "    zero={V22->V23:@{ and_={V23->V23}; or__={V23->V23}; then={ {()->V24} {()->V24} -> V24}}}"+
        "  };"+
        // Has all the fields of a natural number.
        "  three=V25:@{ "+
        "    add_={ V26:@{ succ={()->V26}; ... }->V26  };"+
        "    pred={ V27 -> V25};"+
        "    succ={ ()  -> V25};"+ // Note 'succ' only takes 'void', and not an 'unused'.
        "    zero={ V28 -> V29:@{ and_={V29->V29}; or__={V29->V29}; then={ {()->V30} {()->V30} -> V30}}}"+
        "  };"+
        // Has all the fields of a natural number.
        "  two=V31:@{ "+
        "    add_={ V32:@{succ={()->V32}; ...} ->V32 };"+
        "    pred={ V33 -> V31};"+
        "    succ={ ()  -> V31};"+ // Note 'succ' only takes a 'void', and not an 'unused'.
        "    zero={V34->V35:@{and_={V35->V35};or__={V35->V35};then={{()->V36}{()->V36}->V36}}}"+
        "  }"+
        "}"+
        "",

        "@{" +
        // Booleans, support AND, OR, THEN/ELSE.  Eg. b.false.and is a function which
        // ignores its input and returns false.
        "  b=@{ false=A:@{ and_={B->A}; or__={C->C}; then={D {()->E} ->E} };"+
        "       true =F:@{ and_={G->G}; or__={H->F}; then={{()->I} J ->I} }"+
        "  };"+
        // Natural numbers are formed from zero (z) and succ (s).
        "  n=@{"+
        "    s={"+
        // K is the type var of a natural number: a struct supporting pred,succ,add,zero.
        // So 's' succ is a function which takes a natural number (K) and returns a K.
        "      K:@{ add_={ L:@{ succ={()->L}; ...} ->L };"+
        "           pred={ M -> K};"+
        "           succ={ N -> K};"+
        "           zero={ O -> P:@{ and_={P->P}; or__={P->P}; then={ {()->Q} {()->Q} -> Q }}}"+
        "        } -> K };"+
        "    z=K"+         // Zero is also a natural number
        "  };"+
        // One is formed by taking the successor of zero: "(n.s n.z)".  It has the same
        // shape as any natural number ("self" structural shape above), but its type is
        // not unified with "self".
        "  one=R:@{"+
        "    add_={ S:@{ succ={()->S}; ...} -> S};"+
        "    pred={ T -> R };"+
        "    succ={ U -> R };"+ // Note: succ takes an 'unused'
        "    zero={V22->V23:@{ and_={V23->V23}; or__={V23->V23}; then={ {()->V24} {()->V24} -> V24}}}"+
        "  };"+
        // Has all the fields of a natural number.
        "  three=V25:@{ "+
        "    add_={ V26:@{ succ={()->V26}; ... }->V26  };"+
        "    pred={ V27 -> V25};"+
        "    succ={ ()  -> V25};"+ // Note 'succ' only takes 'void', and not an 'unused'.
        "    zero={ V28 -> V29:@{ and_={V29->V29}; or__={V29->V29}; then={ {()->V30} {()->V30} -> V30}}}"+
        "  };"+
        // Has all the fields of a natural number.
        "  two=V31:@{ "+
        "    add_={ V32:@{succ={()->V32}; ...} ->V32 };"+
        "    pred={ V33 -> V31};"+
        "    succ={ ()  -> V31};"+ // Note 'succ' only takes a 'void', and not an 'unused'.
        "    zero={V34->V35:@{and_={V35->V35};or__={V35->V35};then={{()->V36}{()->V36}->V36}}}"+
        "  }"+
        "}"+
        "",
       """
*[15]@{
  FA:^=any;
  b=*[11]@{
    FA;
    true=PA:*[9]@{FA; and_=[18]{any,1 ->Scalar }; or__=[19]{any,1 ->PA }; then=[20]{any,2 ->Scalar }};
    false=PB:*[10]@{FA; and_=[21]{any,1 ->PB }; or__=[22]{any,1 ->Scalar }; then=[23]{any,2 ->Scalar }}
  };
  n=*[14]@{
    FA;
    s=[31]{any,1 ->
      PC:*[13]@{
        FA;
        zero=[27]{any,1 ->PB };
        pred=[28]{any,1 -> PD:*[ALL]() };
        succ=[29]{any,1 ->PC };
        add_=[30]{any,1 ->Scalar }
      }
    };
    z=*[12]@{FA; zero=[24]{any,1 ->PA }; pred=[17]{any,1 ->~Scalar }; succ=[25]{any,1 ->PC }; add_=[26]{any,1 ->Scalar }}
  };
  one=PC;
  two=PD;
  three=PC
}
""",
       """
*[15]@{
  FA:^=any;
  b=*[11]@{
    FA;
    true=PA:*[9]@{FA; and_=[18]{any,1 ->Scalar }; or__=[19]{any,1 ->PA }; then=[20]{any,2 ->Scalar }};
    false=PB:*[10]@{FA; and_=[21]{any,1 ->PB }; or__=[22]{any,1 ->Scalar }; then=[23]{any,2 ->Scalar }}
  };
  n=*[14]@{
    FA;
    s=[31]{any,1 ->
      PC:*[13]@{FA; zero=[27]{any,1 ->PB }; pred=[28]{any,1 ->Scalar }; succ=[29]{any,1 ->PC }; add_=[30]{any,1 ->Scalar }}
    };
    z=*[12]@{FA; zero=[24]{any,1 ->PA }; pred=[17]{any,1 ->~Scalar }; succ=[25]{any,1 ->PC }; add_=[26]{any,1 ->Scalar }}
  };
  one=PC;
  two=Scalar;
  three=PC
}
""");
  }


  // Checking an AA example
  @Test public void test59() {
    run("prod = { x -> (if x (* (prod x.n) x.v) 1)};"+
        "(prod @{n= @{n=0, v=3}, v=2})"+
        "",
        "int64",
        "int64");
  }

  // Unexpected restriction on extra fields.
  @Test public void test60() {
    run("sx = { ignore -> "+
        "  self0=@{ succ = (sx self0)}; "+
        "  self0 "+
        "};"+
        "self1=@{ succ = self1, nope=7 };"+
        "(sx self1)"+
        "",
        "A:@{ succ=A}",
        "PA:*[8]@{^=any; succ=PA}");
  }

  // Broken from Marco; function 'f' clearly uses 'p2.a' but example 'res1' does not
  // pass in a field 'a'... and still no error.  Fixed.
  @Test public void test61() {
    run("f = { p1 p2 -> (if p2.a p1 p2)}; (f @{a=2} @{b=2.3})",
        "@{ a= Missing field a }",
        "*[8,9](^=any)");
  }

  // Broken from Marco; function 'f' clearly uses 'p2.a' but example 'res1' does not
  // pass in a field 'a'... and still no error.  Fixed.
  @Test public void test62() { run("f = { p1 -> p1.a };"+"(f @{b=2.3})",
                                    "Missing field a",
                                   "Scalar");  }

  @Test public void test63() {
    run("A=@{x=3, y=3.2};"+
        "B=@{x=4, z=\"abc\"};"+
        "rez = { pred -> (if pred A B)};"+
        "rez"+
        "",
        "{ A? -> @{x=nint8} }",
        "[20]{any,1 ->*[8,9]@{^=any; x=nint8} }");
  }

  // Broken from Marco; function 'f' clearly uses 'p2.a' but example 'res1' does not
  // pass in a field 'a'... and still no error.  Fixed.
  @Test public void test64() {
    run("f = { p1 p2 -> (if p2.a p1 p2)};"+
        "res1 = (f @{a=2,      c=\"def\"} @{    b=2.3,d=\"abc\"});"+
        "res2 = (f @{a=2,b=1.2,c=\"def\"} @{a=3,b=2.3,d=\"abc\"});"+
        "@{f=f,res1=res1,res2=res2}",

        "@{ f    =  { A:@{ a=B;... } A -> A };"+
        "   res1 = @{ a = Missing field a };"+
        "   res2 = @{ a=nint8; b=nflt32 }"+
        "}",
        "@{ f    =  { A:@{ a=B;... } A -> A };"+
        "   res1 = @{ a = Missing field a };"+
        "   res2 = @{ a=nint8; b=nflt32 }"+
        "}",
        "*[12]@{^=any; f=[18]{any,2 ->PA:*[2,8,9,10,11]() }; res1=PA; res2=PA}",
        "*[12]@{^=any; f=[18]{any,2 ->Scalar }; res1=Scalar; res2=Scalar}");
  }


  // Regression during the HM/GCP Apply lift.
  @Test public void test65() {
    run("""
all=
  void = @{};
  err  = {unused->(err unused)};
  true = @{
    and  = {b -> b}
    or   = {b -> all.true}
    then = {then else->(then void) }
    };
  false = @{
    and  = {b -> all.false}
    or   = {b -> b}
    then = {then else->(else void) }
    };
  boolSub ={b ->(if b true false)};
  z = @{
    zero = {unused ->all.true}
    pred = err
    succ = {n -> (all.s n)}
    add_ = {n-> n}
    };
  orZero = {n ->(true.then {unused ->n} {unused ->z})};
  s = {pred ->
    self=@{
      zero = {unused ->all.false}
      pred = {unused->pred}
      succ = {unused -> (all.s self)}
      add_ ={m -> (self.succ (pred.add_ m))}
      };
    (orZero self)
    };
  one =(s z);
  @{true=(boolSub 1) false=(boolSub 0) z=z s=s};
all
""",
        """
@{
  false=A:@{
    and={A->A};
    or={A->A};
    then={{()->B}{()->B}->B}
    };
  s={
    C:@{
      add_={C->C};
      pred={D->C};
      succ={C->C};
      zero={E->A}
      }
    ->C
    };
  true=A;
  z=@{
    add_={F->F};
    pred={G->H};
    succ={C->C};
    zero={I->A}
    }
  }
""",
        """
@{
  false=A:@{
    and={A->A};
    or={A->A};
    then={{()->B}{()->B}->B}
    };
  s={
    C:@{
      add_={C->C};
      pred={D->C};
      succ={C->C};
      zero={E->A}
      }
    ->C
    };
  true=A;
  z=@{
    add_={F->F};
    pred={G->H};
    succ={C->C};
    zero={I->A}
    }
  }
""",
        """
*[13]@{
  FA:^=any;
  true=PA:*[9,10]@{FA; and=[18,21]{any,1 ->Scalar }; or=[19,22]{any,1 ->Scalar }; then=[20,23]{any,2 ->Scalar }};
  false=PA;
  z=*[11]@{
    FA;
    zero=[28]{any,1 ->PA };
    pred=[17]{any,1 ->~Scalar };
    succ=[29]{any,1 ->
      PB:*[ALL]()
    };
    add_=[30]{any,1 ->Scalar }
  };
  s=[38]{any,1 ->PB }
}
""",
        """
*[13]@{
  FA:^=any;
  true=PA:*[9,10]@{FA; and=[18,21]{any,1 ->Scalar }; or=[19,22]{any,1 ->Scalar }; then=[20,23]{any,2 ->Scalar }};
  false=PA;
  z=*[11]@{FA; zero=[28]{any,1 ->PA }; pred=[17]{any,1 ->~Scalar }; succ=[29]{any,1 ->Scalar }; add_=[30]{any,1 ->Scalar }};
  s=[38]{any,1 ->Scalar }
}
""");
  }


  // Poster-child collection, larger example
  @Test public void test66() {
    run("""
rand = (factor 1.2);
cage = { ->
  put = { pet ->
    @{ put = put,
       get = pet
     }
  };
  (put 0)
};
cat = @{ name="Pete", purr_vol=1.2 };
dog = @{ name="Spot", wag_rate=2.3 };
cage1 = (cage);
cage2 = (cage);
catcage = (cage1.put cat);
dogcage = (cage2.put dog);
petcage = (if rand catcage dogcage);
maybecat = catcage.get;
maybedog = dogcage.get;
maybepet = petcage.get;
(triple (if maybecat maybecat.purr_vol 9.9)
        (if maybedog maybedog.wag_rate 9.9)
        (if maybepet maybepet.name "no_name")
)
""",
        "(nflt32,nflt32,*[4]str:(nint8))",
        "(nflt32,nflt32,*[4]str:(nint8))",
        "*[11](^=any, nflt32, nflt32, *[4]str:(nint8))",
        "*[11](^=any, Scalar, Scalar, *[4]str:(nint8))");
  }

  @Test public void test67() {
    run("""
all = @{
  is_even = { dsp n -> (if (eq0 n) 0 (dsp.is_odd  dsp (dec n)))},
  is_odd  = { dsp n -> (if (eq0 n) 1 (dsp.is_even dsp (dec n)))}
};
{ x -> (all.is_even all x)}
""",
        "{int64 -> int1}", "[25]{any,1 ->int1 }");
  }

  @Test public void test68() {
    run("dsp = @{  id = { dsp n -> n}}; (pair (dsp.id dsp 3) (dsp.id dsp \"abc\"))",
        "( 3, *[4]str:(97))",
        "( 3, *[4]str:(97))",
        "*[9](^=any, 3 , *[4]str:(97))",
        "*[9](^=any, nScalar, nScalar)");
  }

  // Test incorrect argument count
  @Test public void test69() {
    run("({x y -> (pair x y) } 1 2 3)","Bad argument count","*[8](^=any, 1, 2)");
  }

  // Test incorrect argument count
  @Test public void test70() {
    run("({x y -> (pair x y) } 1 )","Bad argument count","*[8](^=any, 1, ~Scalar)");
  }

  // Test example from AA with expanded ints
  @Test public void test71() {
    run("int = { i -> @{ i=i, add={ x y -> (int (+ x.i y.i))} } }; x=(int 3); y=(int 4); (x.add x y)",
        """
A:@{
  add={
     B:@{ add={ @{i=int64;...} @{i=int64;...} -> B };i=int64}
     C:@{ add={ @{i=int64;...} @{i=int64;...} -> C };i=int64}
     -> A};
  i=int64
}
""",
        "PA:*[8]@{^=any; i=int64; add=[18]{any,2 ->PA }}");
  }

  @Test public void test72() { run( "fun = { ptr -> ptr.x }; fun", "{ @{x=A; ... } -> A }", "[17]{any,1 -> Scalar}");  }
  @Test public void test73() { run(       "{ ptr -> ptr.x }",      "{ @{x=A; ... } -> A }", "[17]{any,1 -> Scalar}");  }
  @Test public void test74() { run("(* 2 3)","int64","6");  }
  @Test public void test75() {
    run("f0 = { f -> (if (rand) 1 (f (f0 f) 2))}; f0",
      "{ { 1 2 -> 1 } -> 1 }","{ { 1 2 -> 1 } -> 1 }",
      "[19]{any,1 ->1 }","[19]{any,1 ->Scalar }");
  }

}

