package com.cliffc.aa.HM;

import com.cliffc.aa.HM.HM.Root;
import com.cliffc.aa.type.*;
import org.junit.BeforeClass;
import org.junit.Ignore;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

/*
  Theory: can move the update_root_args back into root._val, and remove pass#2
 */

public class TestHM {

  // Set to TRUE to run one test once, with fixed arguments.
  // Set to FALSE for each test to all combinations of HMT and GCP, with a bunch of random seeds.
  private static boolean JIG=false, DO_HMT=false, DO_GCP=false;
  private static int RSEED=0;

  @BeforeClass public static void jig_setup() {
    JIG=false;
  }
  @Ignore @Test public void testJig() {
    JIG=true;

    DO_HMT=true;
    DO_GCP=false;
    RSEED=0;
    test78();
  }

  private void _run0s( String prog, String rez_hm, String frez_gcp, int rseed, String esc_ptrs, String esc_funs  ) {
    HM.reset();
    Root syn = HM.hm(prog, rseed, rez_hm!=null, frez_gcp!=null );
    if(  rez_hm !=null )  assertEquals(stripIndent(rez_hm),stripIndent(syn._hmt.p()));
    if( frez_gcp!=null )  assertEquals(Type.valueOf(frez_gcp),syn.flow_type());
    if( rez_hm!=null && frez_gcp!=null ) {
      // Track expected Root escapes
      String esc_ptrs2 = "*"+esc_ptrs+"()";
      String esc_funs2 =     esc_funs+"{any,3->Scalar}";
      BitsAlias aliases = esc_ptrs==null ? BitsAlias.EMPTY : ((TypeMemPtr)Type.valueOf(esc_ptrs2))._aliases;
      BitsFun   fidxs   = esc_funs==null ? BitsFun  .EMPTY : ((TypeFunPtr)Type.valueOf(esc_funs2))._fidxs  ;
      aliases = aliases.meet(TypeMemPtr.STRPTR._aliases); // Always string alias
      assertEquals(aliases,Root.EXT_ALIASES);
      assertEquals(fidxs  ,Root.EXT_FIDXS  );
    }
  }

  private void _run1s( String prog, String rez_hm, String frez_gcp, String esc_ptrs, String esc_funs ) {
    if( JIG )
      _run0s(prog,rez_hm,frez_gcp,RSEED,esc_ptrs,esc_funs);
    else
      for( int rseed=0; rseed<4; rseed++ )
        _run0s(prog,rez_hm,frez_gcp,rseed,esc_ptrs,esc_funs);
  }

  // Run same program in all 3 combinations, but answers vary across combos
  private void run( String prog, String rez_hm_gcp, String rez_hm_alone, String frez_gcp_hm, String frez_gcp_alone ) {
    rune(prog,rez_hm_gcp,rez_hm_alone,frez_gcp_hm,frez_gcp_alone,null,null);
  }
  private void rune( String prog, String rez_hm_gcp, String rez_hm_alone, String frez_gcp_hm, String frez_gcp_alone, String esc_ptrs, String esc_funs ) {
    if( JIG ) {
      _run1s(prog,
             DO_HMT ? (DO_GCP ?  rez_hm_gcp :  rez_hm_alone ) : null,
             DO_GCP ? (DO_HMT ? frez_gcp_hm : frez_gcp_alone) : null, esc_ptrs, esc_funs);
    } else {
      _run1s(prog,null        ,frez_gcp_alone, esc_ptrs, esc_funs);
      _run1s(prog,rez_hm_alone,null          , esc_ptrs, esc_funs);
      _run1s(prog,rez_hm_gcp  ,frez_gcp_hm   , esc_ptrs, esc_funs);
    }
  }
  private void run ( String prog, String rez_hm, String frez_gcp ) { rune(prog,rez_hm,frez_gcp,null,null); }
  private void rune( String prog, String rez_hm, String frez_gcp, String esc_ptrs, String esc_funs ) {
    if( JIG ) {
      _run1s(prog,DO_HMT ? rez_hm : null,DO_GCP ? frez_gcp : null, esc_ptrs, esc_funs);
    } else {
      _run1s(prog,null  ,frez_gcp, esc_ptrs, esc_funs);
      _run1s(prog,rez_hm,null    , esc_ptrs, esc_funs);
      _run1s(prog,rez_hm,frez_gcp, esc_ptrs, esc_funs);
    }
  }

  private static String stripIndent(String s){ return s.replace("\n","").replace(" ",""); }

  @Test(expected = RuntimeException.class)
  public void test00() { run( "fred","","all"); }

  @Test public void test01() { run( "3", "3", "3");  }

  @Test public void test02() { rune( "{ x -> (pair 3 x) }" ,
                                     "{ A -> *( 3, A) }",
                                     "[18]{any,3 -> *[7](^=any,3,Scalar)}",
                                     "[7]", "[18]" ); }

  @Test public void test03() { rune( "{ z -> (pair (z 0) (z \"abc\")) }" ,
                                    "{ { *str:(97)? -> A } -> *( A, A) }",
                                    "[18]{any,3 ->*[7](^=any, Scalar, Scalar) }",
                                    "[7]", "[18,19]" );
  }

  @Test public void test04() {
    rune( "fact = { n -> (if (eq0 n) 1 (* n (fact (dec n))))}; fact",
          "{ int64 -> int64 }",
          "[22]{any,3 -> int64 }",
          null, "[22]" );
  }

  // Because {y->y} is passed in, all 'y' types must agree.
  // This unifies 3 and 5 which results in 'nint8'
  @Test public void test05() {
    rune("({ id -> (pair (id 3) (id 5) ) } {x->x})",
         "*( nint8, nint8)",   // HMT result type, using both GCP + HMT
         "*( nint8, nint8)",   // HMT result type, HMT alone
         "*[7](^=any, 3, 5)",  // GCP result type, using both GCP + HMT
         "*[7](^=any, nint8, nint8)", // GCP result type, GCP alone
          "[7]",null);
  }

  @Test public void test06() {
    rune("id={x->x}; (pair (id 3) (id \"abc\"))",
         // HM is sharper here than in test05, because id is generalized per each use site
         "*( 3, *str:(97))",
         "*( 3, *str:(97))",
         // GCP with HM
         "*[7](^=any, 3, *[4]str:(, 97))",
         // GCP is weaker without HM
         "*[7](^=any, nScalar, nScalar)",
         "[4,7]", null );
  }

  // recursive unification; normal H-M fails here.
  @Test public void test07() {
    rune( "{ f -> (f f) }",
          // We can argue the pretty-print should print:
          // "  A:{ A -> B }"
          "{ A:{ A -> B } -> B }",
          "[17]{any,3 ->Scalar }",
          null, "[17,19]" );
  }

  // After some study, I believe the combined result is correct.  Essentially
  // the 'x' terms take on whatever values are in the induced recursive
  // functions (e.g. 'int' for a 'fact' function).  With no function passed in
  // (just the Y-combinator alone), there is no flow constraint placed on the
  // 'x' terms, and HM "knows" this and "teaches" it to GCP via apply_lift.
  @Test public void testYcombo() {
  rune( "{ f -> ({ x -> (f (x x))} { x -> (f (x x))})}",
         "{{ A -> A } -> A }",
         "{{ A -> A } -> A }",
         "[20]{any,3 -> ~Scalar }",
         "[20]{any,3 ->  Scalar }",
         null, "[19,20]");
  }

  @Test public void test08() { run( "g = {f -> 5}; (g g)",  "5", "5"); }

  // example that demonstrates generic and non-generic variables:
  @Test public void test09() { rune( "{ g -> f = { ignore -> g }; (pair (f 3) (f \"abc\"))}",
                                     "{ A -> *( A, A) }",
                                     "[20]{any,3 ->*[7](^=any, Scalar, Scalar) }",
                                     "[4,7]","[20]"); }

  @Test public void test10() { rune( "{ f g -> (f g)}",
                                     "{ { A -> B } A -> B }",
                                     "[17]{any,4 ->Scalar }",
                                     null,"[17,19]"); }

  // Function composition
  @Test public void test11() { rune( "{ f g -> { arg -> (g (f arg))} }",
                                     "{ { A -> B } { B -> C } -> { A -> C } }",
                                     "[18]{any,4 ->[17]{any,3 ->Scalar } }",
                                     null,"[17,18,19,23]"); }

  // Stacked functions ignoring all function arguments
  @Test public void test12() { run( "map = { fun -> { x -> 2 } }; ((map 3) 5)", "2", "2"); }

  // map takes a function and an element (collection?) and applies it (applies to collection?)
  @Test public void test13() { rune( "map = { fun -> { x -> (fun x)}}; { p -> 5 }",
                                     "{ A -> 5 }",  "[20]{any,3 -> 5 }",
                                     null,"[20]"); }


  // Looking at when tvars are duplicated ("fresh" copies made).
  // This is the "map" problem with a scalar instead of a collection.
  // Takes a '{a->b}' and a 'a' for a couple of different prims.
  @Test public void test14() {
    rune("map = { fun -> { x -> (fun x)}};"+
         "(pair ((map str) 5) ((map factor) 2.3))",
         "*( *str:(int8), flt64)",
         "*( *str:(int8), flt64)",
         "*[7](^=any, *[4]str:(, int8), flt64)",
         "*[7](^=any, Scalar, Scalar)",
         "[4,7]",null);
  }

  // map takes a function and an element (collection?) and applies it (applies to collection?)
  @Test public void test15() { run("map = { fun x -> (fun x)}; (map {a->3} 5)", "3", "3"); }

  // map takes a function and an element (collection?) and applies it (applies to collection?)
  @Test public void test16() { rune("map = { fun x -> (fun x)}; (map { a-> (pair a a)} 5)", "*( 5, 5)", "*[7](^=any, 5, 5)","[4,7]",null); }

  @Test public void test17() { rune("""
fcn = { p -> { a -> (pair a a) }};
map = { fun x -> (fun x)};
{ q -> (map (fcn q) 5)}
""",
                                    "{ A -> *( 5, 5) }", "[22]{any,3 ->*[7](^=any, 5, 5) }",
                                    "[4,7]","[22]"); }

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
    rune("fcn = {p -> (if p {a -> (pair a a)} {b -> (pair b (pair 3 b))})};"+
         "map = { fun x -> (fun x)};"+
         "{ q -> (map (fcn q) 5)}",
         "{ A? -> *( B:Cannot unify 5 and *( 3, B), B) }",
         "[29]{any,3 -> *[7,8](^=any, 5, nScalar) }",
         "[4,7,8,9]","[29]" );
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
    rune("""
cons ={x y-> {cadr -> (cadr x y)}};
cdr ={mycons -> (mycons { p q -> q})};
map ={fun parg -> (fun (cdr parg))};
(pair (map str (cons 0 5)) (map isempty (cons 0 "abc")))
""",
         "*( *str:(int8), int1)",
         "*( *str:(int8), int1)",
         "*[7](^=any, *[4]str:(, int8), int64)",
         "*[7](^=any, Scalar, Scalar)",
         "[4,7]",null );
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
    rune("""
{ g -> fgz =
         cons = {x y -> {cadr -> (cadr x y)}};
         cdr = {mycons -> (mycons { p q -> q})};
         (cdr (cons 2 { z -> (g z) }));
      (pair (fgz 3) (fgz 5))
}
""",
         "{ { nint8 -> A } -> *( A, A) }",
         "[25]{any,3 ->*[7](^=any, Scalar, Scalar) }",
         "[4,7]","[19,25]" );
  }

  // Basic structure test
  @Test public void test25() {
    rune("@{x=2, y=3}",
         "*@{ x = 2; y = 3}",
         "*[7]@{^=any; x=2; y=3}",
         "[4,7]",null);
  }

  // Basic field test
  @Test public void test26() { run("@{x =2, y =3}.x", "2", "2"); }

  // Basic field test
  @Test public void test27() { run("5.x", "Missing field x in 5", "Scalar"); }

  // Basic field test.
  @Test public void test28() { run("@{ y =3}.x", "Missing field x in *@{ y = 3}", "Scalar"); }

  @Test public void test29() { rune("{ g -> @{x=g, y=g}}",
                                    "{ A -> *@{ x = A; y = A} }",
                                    "[17]{any,3 ->*[7]@{^=any; x=Scalar; y=Scalar} }",
                                    "[4,7]","[17]"); }

  // Load common field 'x', ignoring mismatched fields y and z
  @Test public void test30() {
    rune("{ pred -> (if pred @{x=2,y=3} @{x=3,z= \"abc\"}) .x }",
         "{ A? -> nint8 }",
         "[21]{any,3 ->nint8 }",
         null,"[21]"); }

  // Load some fields from an unknown struct: area of a rectangle.
  // Since no nil-check, correctly types as needing a not-nil input.
  @Test public void test31() { rune("{ sq -> (* sq.x sq.y) }", // { sq -> sq.x * sq.y }
                                    "{ *@{ x = int64; y = int64; ...} -> int64 }",
                                    "[18]{any,3 ->int64 }",
                                    "[4,10]","[18]" );
  }

  // Recursive linked-list discovery, with no end clause.  Since this code has
  // no exit (it is an infinite loop, endlessly reading from an infinite input
  // and writing an infinite output), gcp gets a cyclic approximation.
  @Test public void test32() {
    rune("map = { fcn lst -> @{ n1 = (map fcn lst.n0), v1 = (fcn lst.v0) } }; map",
         "{ { A -> B } C:*@{ n0 = C; v0 = A; ...} -> D:*@{ n1 = D; v1 = B} }",
         "[17]{any,4 ->PA:*[7]@{^=any; n1=PA; v1=Scalar} }",
         "[4,7,10]","[17,19]");
  }

  // Recursive linked-list discovery, with nil.  Note that the output memory
  // has the output memory alias, but not the input memory alias (which must be
  // made before calling 'map').
  @Test public void test33() {
    rune("map = { fcn lst -> (if lst @{ n1=(map fcn lst.n0), v1=(fcn lst.v0) } 0) }; map",
         "{ { A -> B } C:*@{ n0 = C; v0 = A; ...}? -> D:*@{ n1 = D; v1 = B}? }",
         "[21]{any,4 ->PA:*[0,7]@{^=any; n1=PA; v1=Scalar} }",
         "[4,7,10]","[19,21]");
  }

  // Recursive linked-list discovery, applied
  @Test public void test34() {
    rune("map = { fcn lst -> (if lst @{ n1 = (map fcn lst.n0), v1 = (fcn lst.v0) } 0) }; (map dec @{n0 = 0, v0 = 5})",
         "A:*@{ n1 = A; v1 = int64}?",
         "PA:*[0,7]@{^=any; n1=PA; v1=4}",
         "[4,7]",null);
  }

  // Need to see if a map call, inlined a few times, 'rolls up'.  Sometimes
  // rolls up, sometimes not; depends on worklist visitation order.
  @Test public void test36() {
    rune("map = { lst -> (if lst @{ n1= arg= lst.n0; (if arg @{ n1=(map arg.n0), v1=(str arg.v0)} 0), v1=(str lst.v0) } 0) }; map",
         "{ A:*@{ n0 = *@{ n0 = A; v0 = int64; ...}?; v0 = int64; ...}? -> B:*@{ n1 = *@{ n1 = B; v1 = *str:(int8)}?; v1 = *str:(int8)}? }",
         "[27]{any,3 ->PA:*[0,8]@{FA:^=any; n1=*[0,7]@{FA; n1=PA; FB:v1=*[4]str:(FA, int8)}; FB} }",
         "[4,7,8,10]","[27]" );
  }

  @Test public void test37() { rune("x = { y -> (x (y y))}; x",
                                    "{ A:{ A -> A } -> B }", "[17]{any,3 ->~Scalar }",
                                    null,"[17,19]");
  }

  // Example from SimpleSub requiring 'x' to be both a struct with field
  // 'v', and also a function type - specifically disallowed in 'aa'.
  @Test public void test38() { rune("{ x -> y = ( x x.v ); 0}",
                                    "{ Cannot unify {A->B} and *@{ v=A; ...} -> C? }",
                                    "[17]{any,3 ->xnil }",
                                    "[4,10]","[17,19]");
  }

  // Awful flow-type: function can be called from the REPL with any
  // argument type - and the worse case will be an error.
  @Test public void test39() {
    rune("x = { z -> z}; (x { y -> y.u})",
         "{ *@{ u = A; ...} -> A }",
         "[18]{any,3 ->Scalar }",
         "[4,10]","[18]");
  }

  // Example from SimpleSub requiring 'x' to be both:
  // - a recursive self-call function from "w = (x x)": $V66:{ $V66 -> V67 } AND
  // - a function which takes a struct with field 'u'
  // The first arg to x is two different kinds of functions, so fails unification.
  @Test public void test40() {
    rune("x = w = (x x); { z -> z}; (x { y -> y.u})",
         "A:Cannot unify { A -> A } and *@{ u = A; ... }",
         "A:Cannot unify { A -> A } and *@{ u = A; ... }",
         "Scalar",
         "Scalar",
         "[4,10]","[17,18,19,23]");
  }

  // Example from TestParse.test15:
  //   map={lst fcn -> lst ? fcn lst.1};
  //   in_int=(0,2);"+       // List of ints
  //   in_str=(0,"abc");" +  // List of strings
  //   out_str = map(in_int,str:{int->str});"+        // Map over ints with int->str  conversion, returning a list of strings
  //   out_bool= map(in_str,{str -> str==\"abc\"});"+ // Map over strs with str->bool conversion, returning a list of bools
  //   (out_str,out_bool)",
  @Test public void test41() {
    rune("""
map={lst fcn -> (fcn lst.y) };
in_int=@{ x=0 y=2};
in_str=@{ x=0 y="abc"};
out_str = (map in_int str);
out_bool= (map in_str { xstr -> (eq xstr "def")});
(pair out_str out_bool)
""",
         "*( *str:(int8), int1)",
         "*( *str:(int8), int1)",
         "*[9](^=any, *[4]str:(, int8), int64)",
         "*[9](^=any, Scalar, Scalar)",
         "[4,9]",null);
  }

  // CCP Can help HM
  @Test public void test42() {
    run("pred = 0; s1 = @{ x=\"abc\" }; s2 = @{ y=3.4 }; (if pred s1 s2).y",
        "3.4f",
        "Missing field y in *()",
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
        "Cannot unify 1.2f and *()",
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
        "*str:(nint8)?",      // Both HM and GCP
        "Cannot unify int8 and *str:(nint8)?", // HM alone cannot do this one
        "*[4]str:(, 100)",    // Both HM and GCP
        "nScalar");           // GCP alone gets a very weak answer
  }


  // Basic nil test
  @Test public void test46() { run("0.x",
                                   "May be nil when loading field x", "~Scalar"); }

  // Basic nil test
  @Test public void test47() { rune("{ pred -> (if pred @{x=3} 0).x}",
                                    "{ A? -> May be nil when loading field x }", "[21]{any,3 ->3 }",
                                    null,"[21]"  );
  }

  // Basic uplifting after check
  @Test public void test48() { rune("{ pred -> tmp=(if pred @{x=3} 0); (if tmp tmp.x 4) }",
                                    "{ A? -> nint8 }", "[25]{any,3 ->nint8 }",null,"[25]"); }


  // map is parametric in nil-ness
  @Test public void test49() {
    rune("""
{ pred ->
  map = { fun x -> (fun x) };
  (pair (map {str0 ->          str0.x   }          @{x = 3}   )
        (map {str1 -> (if str1 str1.x 4)} (if pred @{x = 5} 0))
  )
}
""",
         "{ A? -> *( 3, nint8) }",
         "{ A? -> *( 3, nint8) }",
         "[29]{any,3 ->*[7](^=any, nint8, nint8) }",
         "[29]{any,3 ->*[7](^=any, nint8, nint8) }",
         "[4,7]","[29]");
  }

  // map is parametric in nil-ness.  Verify still nil-checking.
  @Test public void test50() {
    rune("""
{ pred ->
  map = { fun x -> (fun x) };
  (pair (map {str0 ->          str0.x   }          @{x = 3}   )
        (map {str1 ->          str1.x   } (if pred @{x = 5} 0))
  )
}
""",
         "{ A? -> *( 3, May be nil when loading field x ) }",
         "{ A? -> *( 3, May be nil when loading field x ) }",
         "[26]{any,3 ->*[7](^=any, nint8, nint8) }",
         "[26]{any,3 ->*[7](^=any, nint8, nint8) }",
         "[4,7]","[26]");
  }

  @Test public void test51() {
    rune("total_size = { a as ->" +  // Total_size takes an 'a' and a list of 'as'
         "  (if as "+                // If list is not empty then
         "      (+ a.size "+         // Add the size of 'a' to
         "         (total_size as.val as.next))" + // the size of the rest of the list
         "      a.size"+             // Else the list is empty, just take the a.size
         "  )"+                      // End of (if as...)
         "};" +                      // End of total_size={...}
         "total_size",               // What is this type?
         "{ A:*@{ size = int64; ...} B:*@{ next = B; val = A; ...}? -> int64 }",
         "{ A:*@{ size = int64; ...} B:*@{ next = B; val = A; ...}? -> int64 }",
         "[22]{any,4 ->int64 }",
         "[22]{any,4 ->Scalar }",
         "[4,10,11]","[22]");
  }

  // Create a boolean-like structure, and unify.
  @Test public void test52() {
    rune("void = @{};"+              // Same as '()'; all empty structs are alike
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
         "*@{ a = nint8; b = *( ); bool = *@{ false = A:*@{ and = { A -> A }; or = { A -> A }; then = { { *( ) -> B } { *( ) -> B } -> B }}; force = { C? -> D:*@{ and = { D -> D }; or = { D -> D }; then = { { *( ) -> E } { *( ) -> E } -> E }} }; true = F:*@{ and = { F -> F }; or = { F -> F }; then = { { *( ) -> G } { *( ) -> G } -> G }}}}",
         "*@{ a = nint8; b = *( ); bool = *@{ false = A:*@{ and = { A -> A }; or = { A -> A }; then = { { *( ) -> B } { *( ) -> B } -> B }}; force = { C? -> D:*@{ and = { D -> D }; or = { D -> D }; then = { { *( ) -> E } { *( ) -> E } -> E }} }; true = F:*@{ and = { F -> F }; or = { F -> F }; then = { { *( ) -> G } { *( ) -> G } -> G }}}}",
         "*[15]@{FA:^=any; a=int64 ; b=*[13,14](FA); bool=*[12]@{FA; false=PA:*[8,9]@{FA; and=[17,21]{any,3 ->Scalar }; or=[18,22]{any,3 ->Scalar }; then=[20,24]{any,4 ->Scalar }}; force=[28]{any,3 ->PA }; true=PA}}",
         "*[15]@{FA:^=any; a=Scalar; b=Scalar      ; bool=*[12]@{FA; false=PA:*[8,9]@{FA; and=[17,21]{any,3 ->Scalar }; or=[18,22]{any,3 ->Scalar }; then=[20,24]{any,4 ->Scalar }}; force=[28]{any,3 ->PA }; true=PA}}",
         "[4,7,8,9,12,13,14,15]","[17,18,19,20,21,22,23,24,28]");
  }


  // Simple nil/default test; takes a nilable but does not return one.
  @Test public void test53() { rune( "{ x y -> (if x x y) }",
                                     "{ A? A -> A }", "[21]{any,4 ->Scalar }",
                                     null,"[21]");  }

  // Regression test; double nested.  Failed to unify x and y.
  @Test public void test54() { rune( "{ x y -> (if x (if x x y) y) }",
                                     "{ A? A -> A }", "[25]{any,4 ->Scalar }",
                                     null,"[25]");  }


  // Regression test; was NPE.  Was testMyBoolsNullPException from marco.servetto@gmail.com.
  @Test public void test55() {
    rune("""
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
        "*@{ false = A:*@{ and = { A -> A }; "+
              "not = { B -> A }; "+
              "or = { A -> A }; "+
              "then = { { *( ) -> C } { *( ) -> C } -> C }"+
            "}; "+
            "true = D:*@{ and = { D -> D }; "+
              "not = { E -> D }; "+
              "or = { D -> D }; "+
              "then = { { *( ) -> F } { *( ) -> F } -> F }"+
            "}"+
        "}",
         "*[12]@{FA:^=any; false=PB:*[8,9]@{FA; and=[17,22]{any,3 ->Scalar }; not=[20,25]{any,3 ->PA:*[8]@{FA; and=[17]{any,3 ->Scalar }; not=[20]{any,3 ->PA }; or=[18]{any,3 ->PA }; then=[21]{any,4 ->Scalar }} }; or=[18,24]{any,3 ->Scalar }; then=[21,26]{any,4 ->Scalar }}; true=PB}",
           "[4,8,9,12]","[17,18,19,20,21,22,23,24,25,26]");
  }

  // Regression test.  Was unexpectedly large type result.  Cut down version of
  // test from marco.servetto@gmail.com.  Looks like it needs some kind of
  // top-level unification with the true->false->true path, and instead the
  // type has an unrolled instance of the 'true' type embedded in the 'false'
  // type.  Bug is actually a core HM algorithm change to handle cycles.
  @Test public void test56() {
    rune("left =     "+
         "  rite = @{n1 = left v1 = 7 }; "+
         "  @{ n1 = rite v1 = 7 };"+
         "left"+
         "",
         "A:*@{ n1 = *@{ n1 = A; v1 = 7}; v1 = 7}",
         "PA:*[8]@{FA:^=any; n1=*[7]@{FA; n1=PA; FB:v1=7}; FB}",
         "[4,7,8]",null);
  }

  @Test public void test57() {
    rune("""
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
        "*@{ boolSub = { A? -> *@{ not = { B -> C:*@{ not = { D -> C }; then = { { 7 -> E } { 7 -> E } -> E }} }; then = { { 7 -> F } { 7 -> F } -> F }} }; false = C; true = C}",
        """
*[9]@{
  FA:^=any;
  boolSub=[26]{any,3 ->
    PA:*[7,8]@{FA; not=[17,20]{any,3 ->PA }; then=[18,21]{any,4 ->Scalar }}
  };
  false=PB:*[8]@{FA; not=[20]{any,3 ->PC:*[7]@{FA; not=[17]{any,3 ->PB }; then=[18]{any,4 ->Scalar }} }; then=[21]{any,4 ->Scalar }};
  true=PC
}
""",
         "[4,7,8,9]","[17,18,19,20,21,23,26]");
  }

  // Full on Peano arithmetic.
  @Test public void test58() {
   rune("""
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
        "*@{" +
        // Booleans, support AND, OR, THEN/ELSE.  Eg. b.false.and is a function which
        // ignores its input and returns false.
        "  b=*@{ false=A:*@{ and_={B->A}; or__={C->C}; then={D {*()->E} ->E} };"+
        "        true =F:*@{ and_={G->G}; or__={H->F}; then={{*()->I} J ->I} }"+
        "  };"+
        // Natural numbers are formed from zero (z) and succ (s).
        "  n=*@{"+
        "    s={"+
        // K is the type var of a natural number: a struct supporting pred,succ,add,zero.
        // So 's' succ is a function which takes a natural number (K) and returns a K.
        "      K:*@{ add_={ L:*@{ succ={*()->L}; ...} ->L };"+
        "           pred={ M -> K};"+
        "           succ={ N -> K};"+
        "           zero={ O -> P:*@{ and_={P->P}; or__={P->P}; then={ {*()->Q} {*()->Q} -> Q }}}"+
        "        } -> K };"+
        "    z=K"+         // Zero is also a natural number
        "  };"+
        // One is formed by taking the successor of zero: "(n.s n.z)".  It has the same
        // shape as any natural number ("self" structural shape above), but its type is
        // not unified with "self".
        "  one=R:*@{"+
        "    add_={ S:*@{ succ={*()->S}; ...} -> S};"+
        "    pred={ T -> R };"+
        "    succ={ U -> R };"+ // Note: succ takes an 'unused'
        "    zero={V22->V23:*@{ and_={V23->V23}; or__={V23->V23}; then={ {*()->V24} {*()->V24} -> V24}}}"+
        "  };"+
        // Has all the fields of a natural number.
        "  three=V25:*@{ "+
        "    add_={ V26:*@{ succ={*()->V26}; ... }->V26  };"+
        "    pred={ V27 -> V25};"+
        "    succ={ *() -> V25};"+ // Note 'succ' only takes 'void', and not an 'unused'.
        "    zero={ V28 -> V29:*@{ and_={V29->V29}; or__={V29->V29}; then={ {*()->V30} {*()->V30} -> V30}}}"+
        "  };"+
        // Has all the fields of a natural number.
        "  two=V31:*@{ "+
        "    add_={ V32:*@{succ={*()->V32}; ...} ->V32 };"+
        "    pred={ V33 -> V31};"+
        "    succ={ *() -> V31};"+ // Note 'succ' only takes a 'void', and not an 'unused'.
        "    zero={V34->V35:*@{and_={V35->V35};or__={V35->V35};then={{*()->V36}{*()->V36}->V36}}}"+
        "  }"+
        "}"+
        "",

        "*@{" +
        // Booleans, support AND, OR, THEN/ELSE.  Eg. b.false.and is a function which
        // ignores its input and returns false.
        "  b=*@{ false=A:*@{ and_={B->A}; or__={C->C}; then={D {*()->E} ->E} };"+
        "        true =F:*@{ and_={G->G}; or__={H->F}; then={{*()->I} J ->I} }"+
        "  };"+
        // Natural numbers are formed from zero (z) and succ (s).
        "  n=*@{"+
        "    s={"+
        // K is the type var of a natural number: a struct supporting pred,succ,add,zero.
        // So 's' succ is a function which takes a natural number (K) and returns a K.
        "      K:*@{ add_={ L:*@{ succ={*()->L}; ...} ->L };"+
        "           pred={ M -> K};"+
        "           succ={ N -> K};"+
        "           zero={ O -> P:*@{ and_={P->P}; or__={P->P}; then={ {*()->Q} {*()->Q} -> Q }}}"+
        "        } -> K };"+
        "    z=K"+         // Zero is also a natural number
        "  };"+
        // One is formed by taking the successor of zero: "(n.s n.z)".  It has the same
        // shape as any natural number ("self" structural shape above), but its type is
        // not unified with "self".
        "  one=R:*@{"+
        "    add_={ S:*@{ succ={*()->S}; ...} -> S};"+
        "    pred={ T -> R };"+
        "    succ={ U -> R };"+ // Note: succ takes an 'unused'
        "    zero={V22->V23:*@{ and_={V23->V23}; or__={V23->V23}; then={ {*()->V24} {*()->V24} -> V24}}}"+
        "  };"+
        // Has all the fields of a natural number.
        "  three=V25:*@{ "+
        "    add_={ V26:*@{ succ={*()->V26}; ... }->V26  };"+
        "    pred={ V27 -> V25};"+
        "    succ={ *() -> V25};"+ // Note 'succ' only takes 'void', and not an 'unused'.
        "    zero={ V28 -> V29:*@{ and_={V29->V29}; or__={V29->V29}; then={ {*()->V30} {*()->V30} -> V30}}}"+
        "  };"+
        // Has all the fields of a natural number.
        "  two=V31:*@{ "+
        "    add_={ V32:*@{succ={*()->V32}; ...} ->V32 };"+
        "    pred={ V33 -> V31};"+
        "    succ={ *() -> V31};"+ // Note 'succ' only takes a 'void', and not an 'unused'.
        "    zero={V34->V35:*@{and_={V35->V35};or__={V35->V35};then={{*()->V36}{*()->V36}->V36}}}"+
        "  }"+
        "}"+
        "",
       """
*[16]@{
  FA:^=any;
  b=*[12]@{
    FA;
    false=PA:*[9]@{FA; and_=[22]{any,3 ->PA }; or__=[24]{any,3 ->Scalar }; then=[25]{any,4 ->Scalar }};
    true =PB:*[8]@{FA; and_=[18]{any,3 ->Scalar }; or__=[20]{any,3 ->PB }; then=[21]{any,4 ->Scalar }}
  };
  n=*[15]@{
    FA;
    s=[33]{any,3 ->
      PC:*[14]@{
        FA;
        add_=[32]{any,3 ->Scalar };
        pred=[30]{any,3 ->Scalar };
        succ=[31]{any,3 ->PC };
        zero=[29]{any,3 ->PA }
      }
    };
    z=*[13]@{FA; add_=[28]{any,3 ->Scalar }; pred=[17]{any,3 ->~Scalar }; succ=[27]{any,3 ->PC }; zero=[26]{any,3 ->PB }}
  };
  one=PC;
  three=PC;
  two=Scalar
}
""",
       """
*[16]@{
  FA:^=any;
  b=*[12]@{
    FA;
    false=PA:*[9]@{FA; and_=[22]{any,3 ->PA }; or__=[24]{any,3 ->Scalar }; then=[25]{any,4 ->Scalar }};
    true =PB:*[8]@{FA; and_=[18]{any,3 ->Scalar }; or__=[20]{any,3 ->PB }; then=[21]{any,4 ->Scalar }}
  };
  n=*[15]@{
    FA;
    s=[33]{any,3 ->
      PC:*[14]@{FA; add_=[32]{any,3 ->Scalar }; pred=[30]{any,3 ->Scalar }; succ=[31]{any,3 ->PC }; zero=[29]{any,3 ->PA }}
    };
    z=*[13]@{FA; add_=[28]{any,3 ->Scalar }; pred=[17]{any,3 ->~Scalar }; succ=[27]{any,3 ->PC }; zero=[26]{any,3 ->PB }}
  };
  one=PC;
  two=Scalar;
  three=PC
}
""",
        "[4,8,9,10,11,12,13,14,15,16]","[17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]");
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
    rune("sx = { ignore -> "+
         "  self0=@{ succ = (sx self0)}; "+
         "  self0 "+
         "};"+
         "self1=@{ succ = self1, nope=7 };"+
         "(sx self1)"+
         "",
         "A:*@{ succ=A}",
         "PA:*[7]@{^=any; succ=PA}",
         "[4,7]",null);
  }

  // Broken from Marco; function 'f' clearly uses 'p2.a' but example 'res1' does not
  // pass in a field 'a'... and still no error.  Fixed.
  @Test public void test61() {
    rune("f = { p1 p2 -> (if p2.a p1 p2)}; (f @{a=2} @{b=2.3})",
         "*@{ a= Missing field a }",
         "*[7,8](^=any)",
         "[4,7,8]",null);
  }

  // Broken from Marco; function 'f' clearly uses 'p2.a' but example 'res1' does not
  // pass in a field 'a'... and still no error.  Fixed.
  @Test public void test62() { run("f = { p1 -> p1.a };"+"(f @{b=2.3})",
                                    "Missing field a",
                                   "Scalar");  }

  @Test public void test63() {
    rune("A=@{x=3, y=3.2};"+
         "B=@{x=4, z=\"abc\"};"+
         "rez = { pred -> (if pred A B)};"+
         "rez"+
         "",
         "{ A? -> *@{x=nint8} }",
         "[21]{any,3 ->*[7,8]@{^=any; x=nint8} }",
         "[4,7,8]","[21]");
  }

  // Broken from Marco; function 'f' clearly uses 'p2.a' but example 'res1' does not
  // pass in a field 'a'... and still no error.  Fixed.
  @Test public void test64() {
    rune("f = { p1 p2 -> (if p2.a p1 p2)};"+
         "res1 = (f @{a=2,      c=\"def\"} @{    b=2.3,d=\"abc\"});"+
         "res2 = (f @{a=2,b=1.2,c=\"def\"} @{a=3,b=2.3,d=\"abc\"});"+
         "@{f=f,res1=res1,res2=res2}",

         "*@{ f    =  { A:*@{ a=B;... } A -> A };"+
         "    res1 = *@{ a = Missing field a };"+
         "    res2 = *@{ a=nint8; b=nflt32 }"+
         "}",
         "*@{ f    =  { A:*@{ a=B;... } A -> A };"+
         "    res1 = *@{ a = Missing field a };"+
         "    res2 = *@{ a=nint8; b=nflt32 }"+
         "}",
         "*[13]@{FA:^=any; f=[18]{any,4 ->*[7,8,9,10,11,12]SA:(FA) }; res1=*[7,8]SA; res2=*[9,12]@{FA; a=nint8; b=nflt32}}",
         "*[13]@{^=any; f=[18]{any,4 ->Scalar }; res1=Scalar; res2=Scalar}",
         "[4,7,8,9,10,11,12,13]","[18]");
  }


  // Regression during the HM/GCP Apply lift.
  @Test public void test65() {
    rune("""
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
*@{
  false=A:*@{
    and={A->A};
    or={A->A};
    then={{*()->B}{*()->B}->B}
    };
  s={
    C:*@{
      add_={C->C};
      pred={D->C};
      succ={C->C};
      zero={E->A}
      }
    ->C
    };
  true=A;
  z=*@{
    add_={F->F};
    pred={G->H};
    succ={C->C};
    zero={I->A}
    }
  }
""",
         """
*@{
  false=A:*@{
    and={A->A};
    or={A->A};
    then={{*()->B}{*()->B}->B}
    };
  s={
    C:*@{
      add_={C->C};
      pred={D->C};
      succ={C->C};
      zero={E->A}
      }
    ->C
    };
  true=A;
  z=*@{
    add_={F->F};
    pred={G->H};
    succ={C->C};
    zero={I->A}
    }
  }
""",
         """
*[14]@{
  FA:^=any;
  false=PC:*[8,9]@{FA; and=[18,22]{any,3 ->Scalar }; or=[20,24]{any,3 ->Scalar }; then=[21,25]{any,4 ->Scalar }};
  true =PC;
  s=[40]{any,3 ->
    PA:*[13]@{
      FA;
      add_=[39]{any,3 ->PA };
      pred=[37]{any,3 ->PB:*[10,11,12,13,17,18]@{FA; add_=[31,32,38,39,40]{any,3 ->Scalar }; pred=[17,31,37,38,39,40]{any,3 ->PB }; FB:succ=XA:[31,38,39,40]{any,3 ->*[10,11,13,17,18]@{FA; add_=XA; pred=[31,37,38,39,40]{any,3 ->PB }; FB; FC:zero=[20,22,30,36]{any,3 ->PC }} }; FC} };
      succ=[38]{any,3 ->PA };
      zero=[36]{any,3 ->PC }
    }
  };
  z=*[12]@{
    FA;
    add_=[32]{any,3 ->Scalar };
    pred=[17]{any,3 ->~Scalar };
    succ=[31]{any,3 ->PA };
    zero=[30]{any,3 ->PC }
  }
}
""",
         """
*[14]@{
  FA:^=any;
  false=PA:*[8,9]@{FA; and=[18,22]{any,3 ->Scalar }; or=[20,24]{any,3 ->Scalar }; then=[21,25]{any,4 ->Scalar }};
  s=[40]{any,3 ->Scalar };
  true=PA;
  z=*[12]@{FA; add_=[32]{any,3 ->Scalar }; pred=[17]{any,3 ->~Scalar }; succ=[31]{any,3 ->Scalar }; zero=[30]{any,3 ->PA }}
}
""",
         "[4,8,9,10,11,12,13,14,17,18]",
         "[17,18,19,20,21,22,23,24,25,30,31,32,36,37,38,39,40]"
         );
  }


  // Poster-child collection, larger example
  @Test public void test66() {
    rune("""
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
         "*(nflt32,nflt32,*str:(nint8))",
         "*(nflt32,nflt32,*str:(nint8))",
         "*[12](^=any, Scalar, Scalar, *[4]str:(, nint8))",
         "*[12](^=any, Scalar, Scalar, *[4]str:(, nint8))",
         "[4,12]",null);
  }

  @Test public void test67() {
    rune("""
all = @{
  is_even = { dsp n -> (if (eq0 n) 0 (dsp.is_odd  dsp (dec n)))},
  is_odd  = { dsp n -> (if (eq0 n) 1 (dsp.is_even dsp (dec n)))}
};
{ x -> (all.is_even all x)}
""",
         "{int64 -> int1}", "[27]{any,3 ->int1 }",
         null,"[27]");
  }

  @Test public void test68() {
    rune("dsp = @{  id = { dsp n -> n}}; (pair (dsp.id dsp 3) (dsp.id dsp \"abc\"))",
         "*( 3, *str:(97))",
         "*( 3, *str:(97))",
         "*[8](^=any, 3 , *[4]str:(, 97))",
         "*[8](^=any, nScalar, nScalar)",
         "[4,8]",null);
  }

  // Test incorrect argument count
  @Test public void test69() {
    rune("({x y -> (pair x y) } 1 2 3)","Bad argument count","*[7](^=any, 1, 2)","[4,7]",null);
  }

  // Test incorrect argument count
  @Test public void test70() {
    rune("({x y -> (pair x y) } 1 )","Bad argument count","*[7](^=any, 1, ~Scalar)","[4,7]",null);
  }

  // Test example from AA with expanded ints
  @Test public void test71() {
    rune("int = { i -> @{ i=i, add={ x y -> (int (+ x.i y.i))} } }; x=(int 3); y=(int 4); (x.add x y)",
        """
A:*@{
  add={
     B:*@{ add={ *@{i=int64;...} *@{i=int64;...} -> B };i=int64}
     C:*@{ add={ *@{i=int64;...} *@{i=int64;...} -> C };i=int64}
     -> A};
  i=int64
}
""",
         "PA:*[7]@{^=any; i=int64; add=[18]{any,4 ->PA }}",
           "[4,7,10,11]","[18]");
  }

  @Test public void test72() { rune( "fun = { ptr -> ptr.x }; fun", "{ *@{x=A; ... } -> A }", "[17]{any,3 -> Scalar}","[4,10]","[17]");  }
  @Test public void test73() { rune(       "{ ptr -> ptr.x }",      "{ *@{x=A; ... } -> A }", "[17]{any,3 -> Scalar}","[4,10]","[17]");  }
  @Test public void test74() { run("(* 2 3)","int64","6");  }
  @Test public void test75() {
    rune("f0 = { f -> (if (rand 2) 1 (f (f0 f) 2))}; f0",
         "{ { 1 2 -> 1 } -> 1 }","{ { 1 2 -> 1 } -> 1 }",
         "[20]{any,3 ->1 }","[20]{any,3 ->Scalar }",
         null,"[19,20]");
  }
  // Shorter version of 35
  @Test public void test76() {
    String rez_hm = "*({A B C -> *(A,B,C)},{D E F -> *(D,E,F)},{GHI->*(G,H,I)})";
    rune("p0 = { x y z -> (triple x y z) };"+
         "p1 = (triple p0 p0 p0);"+
         "p1",

         rez_hm,
         "*[8](FA:^=any, XA:[18]{any,5 ->*[7](FA, Scalar, Scalar, Scalar) }, XA, XA)",
         "[4,7,8]","[18]"  );
  }

  // try the worse-case expo blow-up test case from SO
  @Test public void test77() {
    String rez_hm = "*( *( *( { A B C -> *( A, B, C) }, { D E F -> *( D, E, F) }, { G H I -> *( G, H, I) }), *( { J K L -> *( J, K, L) }, { M N O -> *( M, N, O) }, { P Q R -> *( P, Q, R) }), *( { S T U -> *( S, T, U) }, { V22 V23 V24 -> *( V22, V23, V24) }, { V25 V26 V27 -> *( V25, V26, V27) })), *( *( { V28 V29 V30 -> *( V28, V29, V30) }, { V31 V32 V33 -> *( V31, V32, V33) }, { V34 V35 V36 -> *( V34, V35, V36) }), *( { V37 V38 V39 -> *( V37, V38, V39) }, { V40 V41 V42 -> *( V40, V41, V42) }, { V43 V44 V45 -> *( V43, V44, V45) }), *( { V46 V47 V48 -> *( V46, V47, V48) }, { V49 V50 V51 -> *( V49, V50, V51) }, { V52 V53 V54 -> *( V52, V53, V54) })), *( *( { V55 V56 V57 -> *( V55, V56, V57) }, { V58 V59 V60 -> *( V58, V59, V60) }, { V61 V62 V63 -> *( V61, V62, V63) }), *( { V64 V65 V66 -> *( V64, V65, V66) }, { V67 V68 V69 -> *( V67, V68, V69) }, { V70 V71 V72 -> *( V70, V71, V72) }), *( { V73 V74 V75 -> *( V73, V74, V75) }, { V76 V77 V78 -> *( V76, V77, V78) }, { V79 V80 V81 -> *( V79, V80, V81) })))";
    rune("p0 = { x y z -> (triple x y z) };"+
         "p1 = (triple p0 p0 p0);"+
         "p2 = (triple p1 p1 p1);"+
         "p3 = (triple p2 p2 p2);"+
         "p3",

         rez_hm,
         "*[12](FA:^=any, PB:*[9](FA, PA:*[8](FA, XA:[18]{any,5 ->*[7](FA, Scalar, Scalar, Scalar) }, XA, XA), PA, PA), PB, PB)",
         "[4,7,8,9,12]","[18]");
  }

// CNC - Probably incorrectly typed from AA; Haskel gets a (slightly) different
// type with no self-recursive infinite type
  @Test public void test78() {
    rune("I = {x->x};"+
         "K = {x->{y->x}};"+
         "W = {x->(x x)};"+
         "term = {z->{y ->((y (z I))(z K))}};"+
         "test = (term W);"+
         "test",
         "{ { A:{A->A} -> {A->B} } -> B }",
         "[22]{any,3 ->Scalar }",
         null,"[19,22]");
  }

  @Test public void test79() {
    rune("I = {x->x};"+
         "K = {x->{y->x}};"+
         "W = {x->(x x)};"+
         "term = {z->{y ->((y (z I))(z K))}};"+
         "test = (term W);"+
         "(test {x -> {y -> (pair (x 3) (((y \"a\") \"b\") \"c\")) } })",
         "*(A:Cannot unify {A->A} and 3 and *str:(nint8), A)",
         "*[7](^=any, Scalar, Scalar)",
         "[4,7]","[]");
  }

  // Test was buggy, since 'rand' is a known non-zero function pointer constant,
  // GCP folds the 'if' to the true arm.  Instead call: '(rand 2)'
  @Test public void test80() {
    run("i = {x -> x}; k = {x -> (i x)}; l = {x -> (k x)}; m = {x -> (l x)}; n = {x -> (m x)}; (if (rand 2) (n 1) (n \"a\"))",
        "Cannot unify 1 and *str:(97)", "nScalar" );
  }

}

