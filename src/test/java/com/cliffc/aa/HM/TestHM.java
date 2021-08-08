package com.cliffc.aa.HM;

import com.cliffc.aa.HM.HM.Root;
import com.cliffc.aa.type.*;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class TestHM {

  @Before public void reset() { HM.reset(); }

  private void run( String prog, String rez_hm, Type rez_gcp ) {
    Root syn = HM.hm(prog);
    if( HM.DO_HM )
      assertEquals(rez_hm,syn._hmt.p());
    if( HM.DO_GCP )
      assertEquals(rez_gcp,syn.flow_type());
  }
  // Simple no-arg signature returning the type
  private static TypeFunSig tfs(Type ret) {
    return TypeFunSig.make(TypeTuple.make_ret(ret),TypeTuple.make_args());
  }

  private static TypeStruct make_tups(Type t0, Type t1         ) { return TypeStruct.tups(t0,t1   ); }
  private static TypeStruct make_tups(Type t0, Type t1, Type t2) { return TypeStruct.tups(t0,t1,t2); }
  private static final TypeMemPtr tuple2  = TypeMemPtr.make(7,make_tups(Type.SCALAR,   Type.SCALAR   ));
  private static final TypeMemPtr tuplen2 = TypeMemPtr.make(7,make_tups(Type.NSCALR,   Type.NSCALR   ));
  private static final TypeMemPtr tuple82 = TypeMemPtr.make(7,make_tups(TypeInt.NINT8, TypeInt.NINT8 ));
  private static final TypeMemPtr tuple55 = TypeMemPtr.make(7,make_tups(TypeInt.con(5),TypeInt.con(5)));
  private static final TypeFunSig ret_tuple2 = tfs(tuple2);
  private static final TypeMemPtr tuple9  = TypeMemPtr.make(9,TypeStruct.args(Type.SCALAR,Type.SCALAR));

  @Test(expected = RuntimeException.class)
  public void test00() { run( "fred",null,null); }

  @Test public void test01() { run( "3" ,
                                    "3", TypeInt.con(3));  }

  @Test public void test02() { run( "(pair1 3)" ,
                                    "{ A -> ( 3, A) }", tfs(TypeMemPtr.make(7,make_tups(TypeInt.con(3),Type.SCALAR)))); }

  @Test public void test03() { run( "{ z -> (pair (z 0) (z \"abc\")) }" ,
                                    "{ { *[0,4]\"abc\"? -> A } -> ( A, A) }", tfs(tuple2)); }

  @Test public void test04() { run( "fact = { n -> (if (eq0 n) 1 (* n (fact (dec n))))}; fact",
                                    "{ int64 -> int64 }", tfs(TypeInt.INT64) ); }

  // Because {y->y} is passed in, all 'y' types must agree.
  // This unifies 3 and "abc" which results in 'all'
  @Test public void test05() {
    Root syn = HM.hm("({ x -> (pair (x 3) (x 5)) } {y->y})");
    if( HM.DO_HM )
      assertEquals("( nint8, nint8)",syn._hmt.p());
    if( HM.DO_GCP )
      if( HM.DO_HM )
        assertEquals(tuple82,syn.flow_type());
      else
        assertEquals(tuple82,syn.flow_type());
  }

  @Test public void test06() {
    Root syn = HM.hm("id={x->x}; (pair (id 3) (id \"abc\"))");
    if( HM.DO_HM ) // HM is sharper here than in test05, because id is generalized per each use site
      assertEquals("( 3, *[4]\"abc\")",syn._hmt.p());
    if( HM.DO_GCP )
      if( HM.DO_HM )
        assertEquals(TypeMemPtr.make(7,make_tups(TypeInt.con(3),TypeMemPtr.make(4,TypeStr.ABC))),syn.flow_type());
      else
        assertEquals(tuplen2,syn.flow_type());
  }

  // recursive unification; normal H-M fails here.
  @Test public void test07() { run( "{ f -> (f f) }",
    // We can argue the pretty-print should print:
    //                              "  A:{ A -> B }"
                                    "{ A:{ A -> B } -> B }", tfs(Type.SCALAR) ); }

  @Test public void test08() { run( "g = {f -> 5}; (g g)",
                                    "5", TypeInt.con(5)); }

  // example that demonstrates generic and non-generic variables:
  @Test public void test09() { run( "{ g -> f = { x -> g }; (pair (f 3) (f \"abc\"))}",
                                    "{ A -> ( A, A) }", ret_tuple2); }

  @Test public void test10() { run( "{ f g -> (f g)}",
                                    "{ { A -> B } A -> B }", tfs(Type.SCALAR) ); }

  // Function composition
  @Test public void test11() { run( "{ f g -> { arg -> (g (f arg))} }",
                                    "{ { A -> B } { B -> C } -> { A -> C } }", tfs(tfs(Type.SCALAR))); }

  // Stacked functions ignoring all function arguments
  @Test public void test12() { run( "map = { fun -> { x -> 2 } }; ((map 3) 5)",
                                    "2", TypeInt.con(2)); }

  // map takes a function and an element (collection?) and applies it (applies to collection?)
  @Test public void test13() { run( "map = { fun -> { x -> (fun x)}}; { p -> 5 }",
                                    "{ A -> 5 }", tfs(TypeInt.con(5))); }

  // Looking at when tvars are duplicated ("fresh" copies made).
  // This is the "map" problem with a scalar instead of a collection.
  // Takes a '{a->b}' and a 'a' for a couple of different prims.
  @Test public void test14() {
    Root syn = HM.hm("map = { fun -> { x -> (fun x)}};"+
                     "(pair ((map str) 5) ((map factor) 2.3))");
    if( HM.DO_HM )
      assertEquals("( *[4]str, flt64)",syn._hmt.p());
    if( HM.DO_GCP )
      if( HM.DO_HM )
        assertEquals(TypeMemPtr.make(7,make_tups(TypeMemPtr.STRPTR,TypeFlt.FLT64)),syn.flow_type());
      else
        assertEquals(tuple2,syn.flow_type());
  }

  // map takes a function and an element (collection?) and applies it (applies to collection?)
  @Test public void test15() { run("map = { fun x -> (fun x)}; (map {a->3} 5)",
                                   "3", TypeInt.con(3)); }

  // map takes a function and an element (collection?) and applies it (applies to collection?)
  @Test public void test16() { run("map = { fun x -> (fun x)}; (map { a-> (pair a a)} 5)",
                                   "( 5, 5)", tuple55); }

  @Test public void test17() { run("fcn = { p -> { a -> (pair a a) }};"+
                                   "map = { fun x -> (fun x)};"+
                                   "{ q -> (map (fcn q) 5)}",
                                   "{ A -> ( 5, 5) }", tfs(tuple55)); }

  // Checking behavior when using "if" to merge two functions with sufficiently
  // different signatures, then attempting to pass them to a map & calling internally.
  // fcn takes a predicate 'p' and returns one of two fcns.
  //   let fcn = { p -> (if p {a -> pair[a,a        ]}
  //                          {b -> pair[b,pair[3,b]]}) } in
  // map takes a function and an element (collection?) and applies it (applies to collection?)
  //   let map = { fun x -> (fun x) }
  //          in { q -> ((map (fcn q)) 5) }
  // Should return { q -> q ? [5,5] : [5,[3,5]] }
  // Ultimately, unifies "a" with "pair[3,a]" which throws recursive unification.
  @Test public void test18() {
    Root syn = HM.hm("fcn = {p -> (if p {a -> (pair a a)} {b -> (pair b (pair 3 b))})};"+
                     "map = { fun x -> (fun x)};"+
                     "{ q -> (map (fcn q) 5)}");
    if( HM.DO_HM )
      assertEquals("{ A? -> ( B:Cannot unify A:( 3, A) and 5, B) }",syn._hmt.p());
    if( HM.DO_GCP )
      if( HM.DO_HM )
        assertEquals(tfs(TypeMemPtr.make(7,make_tups(Type.XNSCALR,TypeMemPtr.make(7,make_tups(TypeInt.con(3),Type.XNSCALR))))),syn.flow_type());
      else
        assertEquals(tfs(TypeMemPtr.make(7,make_tups(TypeInt.con(5),Type.NSCALR))),syn.flow_type());
  }

  @Test public void test19() { run("cons ={x y-> {cadr -> (cadr x y)}};"+
                                   "cdr ={mycons -> (mycons { p q -> q})};"+
                                   "(cdr (cons 2 3))",
                                   "3", TypeInt.con(3)); }

  // Take 2nd element of pair, and applies a function.
  //    let map = fn parg fun => (fun (cdr parg))
  // Some pairs:
  //    let intz = (pair2 false 3)
  //    let strz = (pair2 false "abc")
  // in pair(map(str,intz),map(isempty,strz))
  // Expects: ("2",false)
  @Test public void test20() {
    Root syn = HM.hm("cons ={x y-> {cadr -> (cadr x y)}};"+
                     "cdr ={mycons -> (mycons { p q -> q})};"+
                     "map ={fun parg -> (fun (cdr parg))};"+
                     "(pair (map str (cons 0 5)) (map isempty (cons 0 \"abc\")))");
    if( HM.DO_HM )
      assertEquals("( *[4]str, int1)",syn._hmt.p());
    if( HM.DO_GCP )
      if( HM.DO_HM )
        assertEquals(TypeMemPtr.make(7,make_tups(TypeMemPtr.STRPTR,TypeInt.BOOL)),syn.flow_type());
      else
        assertEquals(tuple2,syn.flow_type());
  }

  // Obscure factorial-like
  @Test public void test21() { run("f0 = { f x -> (if (eq0 x) 1 (f (f0 f (dec x)) 2))}; (f0 * 99)",
                                   "int64", TypeInt.INT64); }

  // Obscure factorial-like
  // let f0 = fn f x => (if (eq0 x) 1 (* (f0 f (dec x)) 2) ) in f0 f0 99
  // let f0 = fn f x => (if (eq0 x) 1 (f (f0 f (dec x)) 2) ) in f0 *  99
  @Test public void test22() { run("f0 = { f x -> (if (eq0 x) 1 (* (f0 f (dec x)) 2))}; (f0 f0 99)",
                                   "int64", TypeInt.INT64); }

  // Mutual recursion
  @Test public void test23() { run("is_even = "+
                                   "  is_odd = { n -> (if (eq0 n) 0 (is_even (dec n)))}; "+
                                   "     { n -> (if (eq0 n) 1 (is_odd (dec n)))};"+
                                   "(is_even 3)" ,
                                   "int1", TypeInt.BOOL); }

  // Toss a function into a pair & pull it back out
  @Test public void test24() { run("{ g -> fgz = "+
                                   "         cons = {x y -> {cadr -> (cadr x y)}};"+
                                   "         cdr = {mycons -> (mycons { p q -> q})};"+
                                   "         (cdr (cons 2 { z -> (g z) }));"+
                                   "      (pair (fgz 3) (fgz 5))"+
                                   "}"
                                   ,
                                   "{ { nint8 -> A } -> ( A, A) }", tfs(tuple2)); }

  // Basic structure test
  @Test public void test25() { run("@{x=2, y=3}",
                                   "@{ x = 2, y = 3}",
                                   TypeMemPtr.make(9,TypeStruct.args(TypeInt.con(2),TypeInt.con(3)))
                                   ); }

  // Basic field test
  @Test public void test26() { run("@{x =2, y =3}.x",
                                   "2", TypeInt.con(2)); }

  // Basic field test
  @Test public void test27() { run("5.x",
                                   "Missing field x in 5", Type.SCALAR); }

  // Basic field test.
  @Test public void test28() { run("@{ y =3}.x",
                                   "Missing field x in @{ y = 3}",
                                   Type.SCALAR); }

  @Test public void test29() { run("{ g -> @{x=g, y=g}}",
                                   "{ A -> @{ x = A, y = A} }", tfs(tuple9)); }

  // Load common field 'x', ignoring mismatched fields y and z
  @Test public void test30() { run("{ pred -> (if pred @{x=2,y=3} @{x=3,z= \"abc\"}) .x }",
                                   "{ A? -> nint8 }", tfs(TypeInt.NINT8)); }

  // Load some fields from an unknown struct: area of a rectangle.
  // Since no nil-check, correctly types as needing a not-nil input.
  @Test public void test31() { run("{ sq -> (* sq.x sq.y) }", // { sq -> sq.x * sq.y }
                                   "{ @{ x = int64, y = int64} -> int64 }", tfs(TypeInt.INT64)); }

  private static TypeMemPtr build_cycle( int alias, boolean nil, Type fld ) {
    // Build a cycle of length 2.
    BitsAlias aliases = BitsAlias.make0(alias);
    if( nil ) aliases = aliases.meet_nil();
    TypeMemPtr cycle_ptr0 = TypeMemPtr.make(aliases,TypeObj.XOBJ);
    TypeStruct cycle_str1 = TypeStruct.make(TypeFld.NO_DISP,TypeFld.make("n1",cycle_ptr0),TypeFld.make("v1",fld));
    TypeMemPtr cycle_ptr1 = TypeMemPtr.make(aliases,cycle_str1);
    TypeStruct cycle_str2 = TypeStruct.make(TypeFld.NO_DISP,TypeFld.make("n1",cycle_ptr1),TypeFld.make("v1",fld));
    TypeStruct cycle_strn = cycle_str2.approx(1,alias);
    TypeMemPtr cycle_ptrn = (TypeMemPtr)cycle_strn.at("n1");
    return cycle_ptrn;
  }
  private static TypeMemPtr build_cycle2( boolean nil, Type fld ) {
    // Unrolled, known to only produce results where either other nested
    // struct is from a different allocation site.
    BitsAlias aliases0 = BitsAlias.make0(10);
    BitsAlias aliases9 = BitsAlias.make0( 9);
    if( nil ) aliases0 = aliases0.meet_nil();
    if( nil ) aliases9 = aliases9.meet_nil();
    TypeMemPtr cycle_ptr0 = TypeMemPtr.make(aliases0,TypeObj.XOBJ);
    TypeStruct cycle_str1 = TypeStruct.make(TypeFld.NO_DISP,TypeFld.make("n1",cycle_ptr0),TypeFld.make("v1",fld));
    TypeMemPtr cycle_ptr1 = TypeMemPtr.make(aliases9,cycle_str1);
    TypeStruct cycle_str2 = TypeStruct.make(TypeFld.NO_DISP,TypeFld.make("n1",cycle_ptr1),TypeFld.make("v1",fld));
    TypeMemPtr cycle_ptr2 = TypeMemPtr.make(aliases0,cycle_str2);
    TypeStruct cycle_str3 = TypeStruct.make(TypeFld.NO_DISP,TypeFld.make("n1",cycle_ptr2),TypeFld.make("v1",fld));
    TypeStruct cycle_strn = cycle_str3.approx(1,9);
    TypeMemPtr cycle_ptrn = (TypeMemPtr)cycle_strn.at("n1");
    return cycle_ptrn;
  }


  // Recursive linked-list discovery, with no end clause.  Since this code has
  // no exit (its an infinite loop, endlessly reading from an infinite input
  // and writing an infinite output), gcp gets a cyclic approximation.
  @Test public void test32() {
    Root syn = HM.hm("map = { fcn lst -> @{ n1 = (map fcn lst.n0), v1 = (fcn lst.v0) } }; map");
    if( HM.DO_HM )
      assertEquals("{ { A -> B } C:@{ n0 = C, v0 = A} -> D:@{ n1 = D, v1 = B} }",syn._hmt.p());
    if( HM.DO_GCP )
      // Build a cycle of length 2, without nil.
      assertEquals(tfs(build_cycle(9,false,Type.SCALAR)),syn.flow_type());
  }

  // Recursive linked-list discovery, with nil.  Note that the output memory
  // has the output memory alias, but not the input memory alias (which must be
  // made before calling 'map').
  @Test public void test33() {
    Root syn = HM.hm("map = { fcn lst -> (if lst @{ n1=(map fcn lst.n0), v1=(fcn lst.v0) } 0) }; map");
    if( HM.DO_HM )
      assertEquals("{ { A -> B } C:@{ n0 = C, v0 = A}? -> D:@{ n1 = D, v1 = B}? }",syn._hmt.p());
    if( HM.DO_GCP )
      // Build a cycle of length 2, with nil.
      assertEquals(tfs(build_cycle(9,true,Type.SCALAR)),syn.flow_type());
  }

  // Recursive linked-list discovery, with no end clause
  @Test public void test34() {
    Root syn = HM.hm("map = { fcn lst -> (if lst @{ n1 = (map fcn lst.n0), v1 = (fcn lst.v0) } 0) }; (map dec @{n0 = 0, v0 = 5})");
    if( HM.DO_HM )
      assertEquals("A:@{ n1 = A, v1 = int64}?",syn._hmt.p());
    if( HM.DO_GCP )
      assertEquals(build_cycle(9,true,TypeInt.con(4)),syn.flow_type());
  }

  // try the worse-case expo blow-up test case from SO
  @Test public void test35() {
    TypeFunPtr tfp  = TypeFunPtr.make(16,3,Type.ANY);
    TypeMemPtr tmp0 = TypeMemPtr.make(8,make_tups(tfp ,tfp ,tfp ));
    TypeMemPtr tmp1 = TypeMemPtr.make(8,make_tups(tmp0,tmp0,tmp0));
    TypeMemPtr tmp2 = TypeMemPtr.make(8,make_tups(tmp1,tmp1,tmp1));

    run("p0 = { x y z -> (triple x y z) };"+
        "p1 = (triple p0 p0 p0);"+
        "p2 = (triple p1 p1 p1);"+
        "p3 = (triple p2 p2 p2);"+
        "p3",
        "( ( ( { A B C -> ( A, B, C) }, { D E F -> ( D, E, F) }, { G H I -> ( G, H, I) }), ( { J K L -> ( J, K, L) }, { M N O -> ( M, N, O) }, { P Q R -> ( P, Q, R) }), ( { S T U -> ( S, T, U) }, { V21 V22 V23 -> ( V21, V22, V23) }, { V24 V25 V26 -> ( V24, V25, V26) })), ( ( { V27 V28 V29 -> ( V27, V28, V29) }, { V30 V31 V32 -> ( V30, V31, V32) }, { V33 V34 V35 -> ( V33, V34, V35) }), ( { V36 V37 V38 -> ( V36, V37, V38) }, { V39 V40 V41 -> ( V39, V40, V41) }, { V42 V43 V44 -> ( V42, V43, V44) }), ( { V45 V46 V47 -> ( V45, V46, V47) }, { V48 V49 V50 -> ( V48, V49, V50) }, { V51 V52 V53 -> ( V51, V52, V53) })), ( ( { V54 V55 V56 -> ( V54, V55, V56) }, { V57 V58 V59 -> ( V57, V58, V59) }, { V60 V61 V62 -> ( V60, V61, V62) }), ( { V63 V64 V65 -> ( V63, V64, V65) }, { V66 V67 V68 -> ( V66, V67, V68) }, { V69 V70 V71 -> ( V69, V70, V71) }), ( { V72 V73 V74 -> ( V72, V73, V74) }, { V75 V76 V77 -> ( V75, V76, V77) }, { V78 V79 V80 -> ( V78, V79, V80) })))",
        tmp2  );
  }

  // Need to see if a map call, inlined a few times, 'rolls up'.  Sometimes
  // rolls up, sometimes not; depends on worklist visitation order.
  @Test public void test36() {
    Root syn = HM.hm("map = { lst -> (if lst @{ n1= arg= lst.n0; (if arg @{ n1=(map arg.n0), v1=(str arg.v0)} 0), v1=(str lst.v0) } 0) }; map");
    if( HM.DO_HM )
      assertEquals("{ A:@{ n0 = @{ n0 = A, v0 = int64}?, v0 = int64}? -> B:@{ n1 = @{ n1 = B, v1 = *[4]str}?, v1 = *[4]str}? }",syn._hmt.p());
    if( HM.DO_GCP )
      assertEquals(tfs(build_cycle2(true,TypeMemPtr.STRPTR)),syn.flow_type());
  }

  @Test public void test37() { run("x = { y -> (x (y y))}; x",
                                   "{ A:{ A -> A } -> B }", tfs(Type.XSCALAR)); }

  // Example from SimpleSub requiring 'x' to be both a struct with field
  // 'v', and also a function type - specifically disallowed in 'aa'.
  @Test public void test38() { run("{ x -> y = ( x x.v ); 0}",
                                   "{ Cannot unify @{ v = A} and { A -> B } -> A? }", tfs(Type.XNIL)); }

  // Really bad flow-type: function can be called from the REPL with any
  // argument type - and the worse case will be an error.
  @Test public void test39() {
    Root syn = HM.hm("x = { z -> z}; (x { y -> y.u})");
    if( HM.DO_HM )
      assertEquals("{ @{ u = A} -> A }",syn._hmt.p());
    if( HM.DO_GCP )
      assertEquals(tfs(Type.SCALAR), syn.flow_type());
  }

  // Example from SimpleSub requiring 'x' to be both:
  // - a recursive self-call function from "w = (x x)": $V66:{ $V66 -> V67 } AND
  // - a function which takes a struct with field 'u'
  // The first arg to x is two different kinds of functions, so fails unification.
  @Test public void test40() {
    Root syn = HM.hm("x = w = (x x); { z -> z}; (x { y -> y.u})");
    if( HM.DO_HM )
      assertEquals("Cannot unify A:{ A -> A } and @{ u = A}",syn._hmt.p());
    if( HM.DO_GCP ) {
      if( HM.DO_HM ) {
        assertEquals(tfs(Type.SCALAR), syn.flow_type());
      } else {
        assertEquals(Type.SCALAR, syn.flow_type());
      }
    }
  }

  // Example from TestParse.test15:
  //   map={lst fcn -> lst ? fcn lst.1};
  //   in_int=(0,2);"+       // List of ints
  //   in_str=(0,"abc");" +  // List of strings
  //   out_str = map(in_int,str:{int->str});"+        // Map over ints with int->str  conversion, returning a list of strings
  //   out_bool= map(in_str,{str -> str==\"abc\"});"+ // Map over strs with str->bool conversion, returning a list of bools
  //   (out_str,out_bool)",
  @Test public void test41() {
    Root syn = HM.hm("map={lst fcn -> (fcn lst.y) }; "+
                     "in_int=@{ x=0 y=2}; " +
                     "in_str=@{ x=0 y=\"abc\"}; " +
                     "out_str = (map in_int str); " +
                     "out_bool= (map in_str { xstr -> (eq xstr \"def\")}); "+
                     "(pair out_str out_bool)");
    if( HM.DO_HM )
      assertEquals("( *[4]str, int1)",syn._hmt.p());
    if( HM.DO_GCP )
      if( HM.DO_HM )
        assertEquals(TypeMemPtr.make(7,make_tups(TypeMemPtr.STRPTR,TypeInt.BOOL)),syn.flow_type());
      else
        assertEquals(tuple2,syn.flow_type());
  }

  // CCP Can help HM
  @Test public void test42() {
    Root syn = HM.hm("pred = 0; s1 = @{ x=\"abc\" }; s2 = @{ y=3.4 }; (if pred s1 s2).y");
    if( HM.DO_HM ) {
      if( HM.DO_GCP )
        assertEquals("3.4000000953674316",syn._hmt.p());
      else
        assertEquals("Missing field y in @{ x = *[4]\"abc\"}",syn._hmt.p());
    }
    if( HM.DO_GCP )
      assertEquals(TypeFlt.con(3.4f), syn.flow_type());
  }

  // The z-merge is ignored; the last s2 is a fresh (unmerged) copy.
  @Test public void test43() {
    Root syn = HM.hm("pred = 0; s1 = @{ x=\"abc\" }; s2 = @{ y=3.4 }; z = (if pred s1 s2); s2.y");
    if( HM.DO_HM )
      assertEquals("3.4000000953674316",syn._hmt.p());
    if( HM.DO_GCP )
      assertEquals(TypeFlt.con(3.4f), syn.flow_type());
  }


  @Test public void test44() {
    Root syn = HM.hm("fun = (if (isempty \"abc\") {x->x} {x->1.2}); (fun @{})");
    if( HM.DO_HM ) {
      if( HM.DO_GCP )
        assertEquals("1.2000000476837158",syn._hmt.p());
      else
        assertEquals("Cannot unify 1.2000000476837158 and ()",syn._hmt.p());
    }
    if( HM.DO_GCP )
      assertEquals(TypeFlt.con(1.2f), syn.flow_type());
  }


  // Requires a combo of HM and GCP to get the good answer
  @Test public void test45() {
    Root syn = HM.hm(
"id = {x -> x};" +
"loop = { name cnt ->" +
"  (if cnt " +
"    (loop" +
"       fltfun = (if name id {x->3});" +
"       (fltfun \"abc\")" +
"       (dec cnt)" +
"     )" +
"     name" +
"   )"+
"};" +
"(loop \"def\" (id 2))");
    if( HM.DO_HM )
      assertEquals(HM.DO_GCP
                   ? "*[0,4]str?"  // Both HM and GCP
                   : "Cannot unify *[4]\"abc\" and 3", // HM alone cannot do this one
                   syn._hmt.p());
    if( HM.DO_GCP )
      assertEquals(HM.DO_HM
                   ? TypeMemPtr.STRPTR // Both HM and GCP
                   : Type.NSCALR,      // GCP alone gets a very weak answer
                   syn.flow_type());
  }


  // Basic nil test
  @Test public void test46() { run("0.x",
                                   "May be nil when loading field x", Type.XSCALAR); }

  // Basic nil test
  @Test public void test47() { run("{ pred -> (if pred @{x=3} 0).x}",
                                   "{ A? -> May be nil when loading field x }", tfs(TypeInt.con(3))); }

  // Basic uplifting after check
  @Test public void test48() { run("{ pred -> tmp=(if pred @{x=3} 0); (if tmp tmp.x 4) }",
                                   "{ A? -> nint8 }", tfs(TypeInt.NINT8)); }


  // map is parametric in nil-ness
  @Test public void test49() {
    Root syn = HM.hm("{ pred -> \n"+
                     "  map = { fun x -> (fun x) };\n" +
                     "  (pair (map {str0 ->          str0.x   }          @{x = 3}   )\n" +
                     "        (map {str1 -> (if str1 str1.x 4)} (if pred @{x = 5} 0))\n" +
                     "  )\n"+
                     "}");
    if( HM.DO_HM )
      assertEquals("{ A? -> ( 3, nint8) }",syn._hmt.p());
    if( HM.DO_GCP )
      if( HM.DO_HM ) assertEquals(tfs(TypeMemPtr.make(7,make_tups(TypeInt.con(3), TypeInt.NINT8 ))),syn.flow_type());
      else           assertEquals(tfs(TypeMemPtr.make(7,make_tups(TypeInt.NINT8 , TypeInt.NINT8 ))),syn.flow_type());
  }

  // map is parametric in nil-ness.  Verify still nil-checking.
  @Test public void test50() {
    Root syn = HM.hm("{ pred -> \n"+
                     "  map = { fun x -> (fun x) };\n" +
                     "  (pair (map {str0 ->          str0.x   }          @{x = 3}   )\n" +
                     "        (map {str1 ->          str1.x   } (if pred @{x = 5} 0))\n" +
                     "  )\n"+
                     "}");
    if( HM.DO_HM )
      assertEquals("{ A? -> May be nil when loading field x }",syn._hmt.p());
    if( HM.DO_GCP )
      if( HM.DO_HM ) assertEquals(tfs(TypeMemPtr.make(7,make_tups(TypeInt.NINT8, TypeInt.NINT8 ))),syn.flow_type());
      else           assertEquals(tfs(TypeMemPtr.make(7,make_tups(TypeInt.NINT8, TypeInt.NINT8 ))),syn.flow_type());
  }

  @Test public void test51() {
    Root syn = HM.hm("total_size = { a as ->" +  // Total_size takes an 'a' and a list of 'as'
                     "  (if as "+                // If list is not empty then
                     "      (+ a.size "+         // Add the size of 'a' to
                     "         (total_size as.val as.next))" + // the size of the rest of the list
                     "      a.size"+             // Else the list is empty, just take the a.size
                     "  )"+                      // End of (if as...)
                     "};" +                      // End of total_size={...}
                     "total_size"                // What is this type?
                     );
    if( HM.DO_HM )
      assertEquals("{ A:@{ size = int64} B:@{ next = B, val = A}? -> int64 }",syn._hmt.p());
    if( HM.DO_GCP )
      if( HM.DO_HM ) assertEquals(tfs(TypeInt.INT64),syn.flow_type());
      else           assertEquals(tfs(Type.SCALAR  ),syn.flow_type());
  }

  // Create a boolean-like structure, and unify.
  @Test public void test52() {
    Root syn = HM.hm("void = @{};"+              // Same as '()'; all empty structs are alike
                     "true = @{"+                // 'true' is a struct with and,or,thenElse
                     "  and= {b -> b}"+
                     "  or = {b -> true}"+
                     "  thenElse = {then else->(then void) }"+
                     "};"+
                     "false = @{"+               // 'false' is a struct with and,or,thenElse
                     "  and= {b -> false}"+
                     "  or = {b -> b}"+
                     "  thenElse = {then else->(else void) }"+
                     "};"+
                     "forceSubtyping ={b ->(if b true false)};"+ // A unified version
                     // Trying really hard here to unify 'true' and 'false'
                     "bool=@{true=(forceSubtyping 1), false=(forceSubtyping 0), force=forceSubtyping};"+
                     // Apply the unified 'false' to two different return contexts
                     "a=(bool.false.thenElse { x-> 3 } { y-> 4 });"+
                     "b=(bool.false.thenElse { z->@{}} { z->@{}});"+
                     // Look at the results
                     "@{a=a,b=b, bool=bool}"+
                     "");
    if( HM.DO_HM ) {
      /*  An indented version of this answer
        @{
          a = nint8,
          b = (),
          bool = @{
            false =        A:@{ and = { A -> A }, or = { A -> A }, thenElse = { { () -> B } { () -> B } -> B } },
            force = { C -> D:@{ and = { D -> D }, or = { D -> D }, thenElse = { { () -> E } { () -> E } -> E } } },
            true =         F:@{ and = { F -> F }, or = { F -> F }, thenElse = { { () -> G } { () -> G } -> G } }
          }
        }
       */
      assertEquals("@{ a = nint8, b = (), bool = @{ false = A:@{ and = { A -> A }, or = { A -> A }, thenElse = { { () -> B } { () -> B } -> B }}, force = { C? -> D:@{ and = { D -> D }, or = { D -> D }, thenElse = { { () -> E } { () -> E } -> E }} }, true = F:@{ and = { F -> F }, or = { F -> F }, thenElse = { { () -> G } { () -> G } -> G }}}}",syn._hmt.p());
    }
    if( HM.DO_GCP ) {
      Type tf   = TypeMemPtr.make(BitsAlias.FULL.make(10,11),
                                  TypeStruct.make(TypeFld.NO_DISP,
                                                  TypeFld.make("and"     ,TypeFunPtr.make(BitsFun.make0(15,18),1,TypeMemPtr.NO_DISP)),
                                                  TypeFld.make("or"      ,TypeFunPtr.make(BitsFun.make0(16,19),1,TypeMemPtr.NO_DISP)),
                                                  TypeFld.make("thenElse",TypeFunPtr.make(BitsFun.make0(17,20),2,TypeMemPtr.NO_DISP))));
      Type xbool= TypeMemPtr.make(12,TypeStruct.make(TypeFld.NO_DISP,
                                                     TypeFld.make("true", tf),
                                                     TypeFld.make("false",tf),
                                                     TypeFld.make("force",TypeFunPtr.make(24,1,TypeMemPtr.NO_DISP))));
      TypeStruct rez = TypeStruct.make(TypeFld.NO_DISP,
                                       TypeFld.make("a",HM.DO_HM ? TypeInt.INT64: Type.NSCALR),
                                       TypeFld.make("b",HM.DO_HM ? Type.SCALAR  : Type.NSCALR),
                                       TypeFld.make("bool",xbool));
      assertEquals(TypeMemPtr.make(15,rez),syn.flow_type());
    }
  }


  // Simple nil/default test; takes a nilable but does not return one.
  @Test public void test53() { run( "{ x y -> (if x x y) }",
                                    "{ A? A -> A }", tfs(Type.SCALAR));  }

  // Double nested.  Currently fails to unify x and y.
  @Test public void test54() { run( "{ x y -> (if x (if x x y) y) }",
                                    "{ A? A -> A }", tfs(Type.SCALAR));  }

  // Regression test; was NPE.  Was testMyBoolsNullPException from marco.servetto@gmail.com.
  @Test public void test55() {
    Root syn = HM.hm("void = @{};                           "+
                     "true = @{                             "+
                     "  and      = {b -> b}                 "+
                     "  or       = {b -> true}              "+
                     "  not      = {unused ->true}          "+
                     "  thenElse = {then else->(then void) }"+
                     "};                                    "+
                     "false = @{                            "+
                     "  and      = {b -> false}             "+
                     "  or       = {b -> b}                 "+
                     "  not      = {unused ->true}          "+
                     "  thenElse = {then else->(else void) }"+
                     "};                                    "+
                     "boolSub ={b ->(if b true false)};     "+
                     "@{true=(boolSub 1) false=(boolSub 0)} "+
                     "");
    if( HM.DO_HM )
      assertEquals("@{ false = A:@{ and = { A -> A }, "+
                         "not = { B -> A }, "+
                         "or = { A -> A }, "+
                         "thenElse = { { () -> C } { () -> C } -> C }"+
                       "}, "+
                       "true = D:@{ and = { D -> D }, "+
                         "not = { E -> D }, "+
                         "or = { D -> D }, "+
                         "thenElse = { { () -> F } { () -> F } -> F }"+
                       "}"+
                    "}",syn._hmt.p());
    if( HM.DO_GCP ) {
      // true/false=*[10,11]@{$; and=[15,19]{any }; or=[16,20]{any }; not=[17,21]{any }; thenElse=[18,22]{any }}
      Type tf   = TypeMemPtr.make(BitsAlias.FULL.make(10,11),
                                  TypeStruct.make(TypeFld.NO_DISP,
                                                  TypeFld.make("and"     ,TypeFunPtr.make(BitsFun.make0(15,19),1,TypeMemPtr.NO_DISP)),
                                                  TypeFld.make("or"      ,TypeFunPtr.make(BitsFun.make0(16,20),1,TypeMemPtr.NO_DISP)),
                                                  TypeFld.make("not"     ,TypeFunPtr.make(BitsFun.make0(17,21),1,TypeMemPtr.NO_DISP)),
                                                  TypeFld.make("thenElse",TypeFunPtr.make(BitsFun.make0(18,22),2,TypeMemPtr.NO_DISP))));
      // *[12]@{^=any; true=$TF; false=$TF}
      TypeStruct rez = TypeStruct.make(TypeFld.NO_DISP,
                                       TypeFld.make("true" ,tf),
                                       TypeFld.make("false",tf) );
      assertEquals(TypeMemPtr.make(12,rez),syn.flow_type());
    }

  }

  // Regression test.  Was unexpectedly large type result.  Cut down version of
  // test from marco.servetto@gmail.com.  Looks like it needs some kind of
  // top-level unification with the true->false->true path, and instead the
  // type has an unrolled instance of the 'true' type embedded in the 'false'
  // type.  Bug is actually a core HM algorithm change to handle cycles.
  @Test public void test56() {
    Root syn = HM.hm("left =     "+
                     "  rite = @{n1 = left v1 = 7 }; "+
                     "  @{ n1 = rite v1 = 7 };"+
                     "left"+
                     "");
    if( HM.DO_HM )
      assertEquals("A:@{ n1 = @{ n1 = A, v1 = 7}, v1 = 7}",syn._hmt.p());
    if( HM.DO_GCP )
      assertEquals(build_cycle2(false,TypeInt.con(7)),syn.flow_type());
  }

  @Test public void test57() {
    Root syn = HM.hm(
"all =                                      "+
"true = @{                                  "+
"  not = {unused -> all.false},             "+
"  thenElse = {then else->(then 7) }        "+
"};                                         "+
"false = @{                                 "+
"  not = {unused -> all.true},              "+
"  thenElse = {then else->(else 7) }        "+
"};                                         "+
"boolSub ={b ->(if b true false)};          "+
"@{true=true, false=false, boolSub=boolSub};"+
"all"+
"");
    if( HM.DO_HM )
        assertEquals("@{ boolSub = { A? -> @{ not = { B -> C:@{ not = { D -> C }, thenElse = { { 7 -> E } { 7 -> E } -> E }} }, thenElse = { { 7 -> F } { 7 -> F } -> F }} }, false = C, true = C}",syn._hmt.p());
    if( HM.DO_GCP ) {

      Type tt = TypeMemPtr.make(BitsAlias.FULL.make(9),
                                TypeStruct.make(TypeFld.NO_DISP,
                                                TypeFld.make("not"     ,TypeFunPtr.make(BitsFun.make0(15),1,TypeMemPtr.NO_DISP)),
                                                TypeFld.make("thenElse",TypeFunPtr.make(BitsFun.make0(16),2,TypeMemPtr.NO_DISP))));
      Type ff = TypeMemPtr.make(BitsAlias.FULL.make(10),
                                TypeStruct.make(TypeFld.NO_DISP,
                                                TypeFld.make("not"     ,TypeFunPtr.make(BitsFun.make0(17),1,TypeMemPtr.NO_DISP)),
                                                TypeFld.make("thenElse",TypeFunPtr.make(BitsFun.make0(18),2,TypeMemPtr.NO_DISP))));
      TypeStruct rez = TypeStruct.make(TypeFld.NO_DISP,
                                       TypeFld.make("true"   ,tt),
                                       TypeFld.make("false"  ,ff),
                                       TypeFld.make("boolSub",TypeFunPtr.make(BitsFun.make0(22),1,TypeMemPtr.NO_DISP)));
      assertEquals(TypeMemPtr.make(11,rez),syn.flow_type());
    }
  }

}
