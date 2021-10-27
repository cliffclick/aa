package com.cliffc.aa.HM;

import com.cliffc.aa.HM.HM.Root;
import com.cliffc.aa.type.*;
import org.junit.Test;

import java.util.function.Supplier;

import static org.junit.Assert.assertEquals;

public class TestHM {

  private void _run0( String prog, String rez_hm, Supplier<Type> frez_gcp, int rseed ) {
    HM.reset();
    Root syn = HM.hm(prog, rseed, rez_hm!=null, frez_gcp!=null );
    if(  rez_hm !=null )  assertEquals(stripIndent(rez_hm),stripIndent(syn._hmt.p()));
    if( frez_gcp!=null )  assertEquals(frez_gcp.get(),syn.flow_type());
  }

  private static final int[] rseeds = new int[]{0,1,2,3};
  private void _run1( String prog, String rez_hm, Supplier<Type> frez_gcp ) {
    for( int rseed : rseeds )
      _run0(prog,rez_hm,frez_gcp,rseed);
  }

  // Run same program in all 3 combinations
  private void run( String prog, String rez_hm, Supplier<Type> frez_gcp ) {
    _run1(prog,rez_hm,frez_gcp);
    _run1(prog,rez_hm,null    );
    _run1(prog,null  ,frez_gcp);
  }
  private void run( String prog, String rez_hm, Type rez_gcp ) {
    run(prog,rez_hm,()->rez_gcp);
  }

  // Run same program in all 3 combinations, but answers vary across combos
  private void run( String prog, String rez_hm_gcp, String rez_hm_alone, Supplier<Type> frez_gcp_hm, Supplier<Type> frez_gcp_alone ) {
    _run1(prog,rez_hm_gcp  ,frez_gcp_hm   );
    _run1(prog,rez_hm_alone,null          );
    _run1(prog,null        ,frez_gcp_alone);
  }
  private void run( String prog, String rez_hm_gcp, String rez_hm_alone, Type rez_gcp_hm, Type rez_gcp_alone ) {
    run(prog, rez_hm_gcp, rez_hm_alone, ()->rez_gcp_hm, ()-> rez_gcp_alone );
  }

  // Simple no-arg signature returning the type
  private static TypeFunSig tfs(Type ret) { return TypeFunSig.make(TypeStruct.EMPTY,ret); }

  private static String stripIndent(String s){ return s.replace("\n","").replace(" ",""); }

  private static TypeStruct make_tups(Type t0, Type t1         ) { return TypeStruct.maket(t0,t1   ); }
  private static TypeStruct make_tups(Type t0, Type t1, Type t2) { return TypeStruct.maket(t0,t1,t2); }
  private static final TypeMemPtr tuple2  = TypeMemPtr.make(7,make_tups(Type.SCALAR,   Type.SCALAR   ));
  private static final TypeMemPtr tuplen2 = TypeMemPtr.make(7,make_tups(Type.NSCALR,   Type.NSCALR   ));
  private static final TypeMemPtr tuple82 = TypeMemPtr.make(7,make_tups(TypeInt.NINT8, TypeInt.NINT8 ));
  private static final TypeMemPtr tuple55 = TypeMemPtr.make(7,make_tups(TypeInt.con(5),TypeInt.con(5)));
  private static final TypeFunSig ret_tuple2 = tfs(tuple2);
  private static final TypeMemPtr tuple9  = TypeMemPtr.make(9,TypeStruct.make(TypeFld.NO_DISP,
                                                                              TypeFld.make("x",Type.SCALAR),
                                                                              TypeFld.make("y",Type.SCALAR)));

  @Test(expected = RuntimeException.class)
  public void test00() { run( "fred","",Type.ALL); }

  @Test public void test01() { run( "3" ,
                                    "3", TypeInt.con(3));  }

  @Test public void test02() { run( "{ x -> (pair 3 x) }" ,
                                    "{ A -> ( 3, A) }", tfs(TypeMemPtr.make(7,make_tups(TypeInt.con(3),Type.SCALAR)))); }

  @Test public void test03() { run( "{ z -> (pair (z 0) (z \"abc\")) }" ,
                                    "{ { *[0,4]str? -> A } -> ( A, A) }", tfs(tuple2)); }

  @Test public void test04() { run( "fact = { n -> (if (eq0 n) 1 (* n (fact (dec n))))}; fact",
                                    "{ int64 -> int64 }", tfs(TypeInt.INT64) ); }

  // Because {y->y} is passed in, all 'y' types must agree.
  // This unifies 3 and 5 which results in 'nint8'
  @Test public void test05() {
    run("({ id -> (pair (id 3) (id 5)) } {x->x})", "( nint8, nint8)",tuple82);
  }

  @Test public void test06() {
    run("id={x->x}; (pair (id 3) (id \"abc\"))",
        // HM is sharper here than in test05, because id is generalized per each use site
        "( 3, *[4]\"abc\")",
        "( 3, *[4]\"abc\")",
        // GCP with HM
        // With lift ON
        //TypeMemPtr.make(7,make_tups(TypeInt.NINT64,TypeMemPtr.make(4,TypeStr.STR))),
        // With lift OFF
        TypeMemPtr.make(7,make_tups(Type.NSCALR,Type.NSCALR)),
        // GCP is weaker without HM
        tuplen2);
  }

  // recursive unification; normal H-M fails here.
  @Test public void test07() {
    run( "{ f -> (f f) }",
         // We can argue the pretty-print should print:
         // "  A:{ A -> B }"
         "{ A:{ A -> B } -> B }", tfs(Type.SCALAR) ); }

  @Test public void test08() { run( "g = {f -> 5}; (g g)",
                                    "5", TypeInt.con(5)); }

  // example that demonstrates generic and non-generic variables:
  @Test public void test09() { run( "{ g -> f = { ignore -> g }; (pair (f 3) (f \"abc\"))}",
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
    run("map = { fun -> { x -> (fun x)}};"+
        "(pair ((map str) 5) ((map factor) 2.3))",
        "( *[4]str, flt64)",
        "( *[4]str, flt64)",
        // With lift ON
        //TypeMemPtr.make(7,make_tups(TypeMemPtr.STRPTR,TypeFlt.FLT64)),
        // With lift OFF
        TypeMemPtr.make(7,make_tups(Type.SCALAR,Type.SCALAR)),
        tuple2);
  }

  // map takes a function and an element (collection?) and applies it (applies to collection?)
  @Test public void test15() { run("map = { fun x -> (fun x)}; (map {a->3} 5)",
                                   "3", TypeInt.con(3)); }

  // map takes a function and an element (collection?) and applies it (applies to collection?)
  @Test public void test16() { run("map = { fun x -> (fun x)}; (map { a-> (pair a a)} 5)",
                                   "( 5, 5)", tuple55); }

  @Test public void test17() { run("""
fcn = { p -> { a -> (pair a a) }};
map = { fun x -> (fun x)};
{ q -> (map (fcn q) 5)}
""",
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
    run("fcn = {p -> (if p {a -> (pair a a)} {b -> (pair b (pair 3 b))})};"+
        "map = { fun x -> (fun x)};"+
        "{ q -> (map (fcn q) 5)}",
        "{ A? -> ( B:Cannot unify 5 and ( 3, B), B) }",
        "{ A? -> ( B:Cannot unify 5 and ( 3, B), B) }",
        // tfs(*[7](^=any, ~nScalar, *[7]($, 3, ~nScalar)))
        // With Lift ON
        //tfs(TypeMemPtr.make(7,make_tups(Type.XNSCALR,TypeMemPtr.make(7,make_tups(TypeInt.con(3),Type.XNSCALR))))),
        // With Lift OFF
        tfs(TypeMemPtr.make(7,make_tups(TypeInt.con(5),Type.NSCALR))),
        // tfs(*[7](^=any, 5, nScalar))
        tfs(TypeMemPtr.make(7,make_tups(TypeInt.con(5),Type.NSCALR))));
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
    run("""
cons ={x y-> {cadr -> (cadr x y)}};
cdr ={mycons -> (mycons { p q -> q})};
map ={fun parg -> (fun (cdr parg))};
(pair (map str (cons 0 5)) (map isempty (cons 0 "abc")))
""",
        "( *[4]str, int1)",
        "( *[4]str, int1)",
        // With Lift ON
        //TypeMemPtr.make(7,make_tups(TypeMemPtr.STRPTR,TypeInt.BOOL)),
        // With Lift OFF
        tuple2,
        tuple2);
  }

  // Obscure factorial-like
  @Test public void test21() {
    run("f0 = { f x -> (if (eq0 x) 1 (f (f0 f (dec x)) 2))}; (f0 * 99)",
        "int64",TypeInt.INT64);
  }

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

  @Test public void test23x() {
    run("""
all = @{
  is_even = { dsp n -> (if (eq0 n) 0 (dsp.is_odd  dsp (dec n)))},
  is_odd  = { dsp n -> (if (eq0 n) 1 (dsp.is_even dsp (dec n)))}
};
{ x -> (all.is_even all x)}
""",
        "{int64 -> int1}", tfs(TypeInt.BOOL));
  }

  @Test public void test23y() {
    run("dsp = @{  id = { dsp n -> n}}; (pair (dsp.id dsp 3) (dsp.id dsp \"abc\"))",
        "( 3, *[4]\"abc\")",
        "( 3, *[4]\"abc\")",
        // With lift On
        //TypeMemPtr.make(7,make_tups(TypeInt.NINT64,TypeMemPtr.STRPTR)),
        // With lift Off
        TypeMemPtr.make(7,make_tups(Type.NSCALR,Type.NSCALR)),
        tuplen2);
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
        "{ { int64 -> A } -> ( A, A) }", tfs(tuple2));
  }

  // Basic structure test
  @Test public void test25() {
    run("@{x=2, y=3}",
        "@{ x = 2; y = 3}",
        TypeMemPtr.make(9,TypeStruct.make(TypeFld.NO_DISP,
                                          TypeFld.make("x",TypeInt.con(2)),
                                          TypeFld.make("y",TypeInt.con(3)))));
  }

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
                                   "{ A -> @{ x = A; y = A} }", tfs(tuple9)); }

  // Load common field 'x', ignoring mismatched fields y and z
  @Test public void test30() {
    run("{ pred -> (if pred @{x=2,y=3} @{x=3,z= \"abc\"}) .x }",
        "{ A? -> nint8 }",
        tfs(TypeInt.NINT8));
  }

  // Load some fields from an unknown struct: area of a rectangle.
  // Since no nil-check, correctly types as needing a not-nil input.
  @Test public void test31() { run("{ sq -> (* sq.x sq.y) }", // { sq -> sq.x * sq.y }
                                   "{ @{ x = int64; y = int64; ...} -> int64 }", tfs(TypeInt.INT64));
  }

  private static TypeMemPtr build_cycle( int alias, boolean nil, Type fld ) {
    // Build a cycle of length 2.
    BitsAlias aliases = BitsAlias.make0(alias);
    if( nil ) aliases = aliases.meet_nil();
    TypeMemPtr cycle_ptr0 = TypeMemPtr.make(aliases,TypeObj.XOBJ);
    TypeStruct cycle_str1 = TypeStruct.make("",false,false,TypeFld.NO_DISP,TypeFld.make("n1",cycle_ptr0),TypeFld.make("v1",fld));
    TypeMemPtr cycle_ptr1 = TypeMemPtr.make(aliases,cycle_str1);
    TypeStruct cycle_str2 = TypeStruct.make("",false,false,TypeFld.NO_DISP,TypeFld.make("n1",cycle_ptr1),TypeFld.make("v1",fld));
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
    TypeStruct cycle_str1 = TypeStruct.make("",false,false,TypeFld.NO_DISP,TypeFld.make("n1",cycle_ptr0),TypeFld.make("v1",fld));
    TypeMemPtr cycle_ptr1 = TypeMemPtr.make(aliases9,cycle_str1);
    TypeStruct cycle_str2 = TypeStruct.make("",false,false,TypeFld.NO_DISP,TypeFld.make("n1",cycle_ptr1),TypeFld.make("v1",fld));
    TypeMemPtr cycle_ptr2 = TypeMemPtr.make(aliases0,cycle_str2);
    TypeStruct cycle_str3 = TypeStruct.make("",false,false,TypeFld.NO_DISP,TypeFld.make("n1",cycle_ptr2),TypeFld.make("v1",fld));
    TypeStruct cycle_strn = cycle_str3.approx(1,9);
    TypeMemPtr cycle_ptrn = (TypeMemPtr)cycle_strn.at("n1");
    return cycle_ptrn;
  }


  // Recursive linked-list discovery, with no end clause.  Since this code has
  // no exit (its an infinite loop, endlessly reading from an infinite input
  // and writing an infinite output), gcp gets a cyclic approximation.
  @Test public void test32() {
    run("map = { fcn lst -> @{ n1 = (map fcn lst.n0), v1 = (fcn lst.v0) } }; map",
        "{ { A -> B } C:@{ n0 = C; v0 = A; ...} -> D:@{ n1 = D; v1 = B} }",
        // Build a cycle of length 2, without nil.
        tfs(build_cycle(9,false,Type.SCALAR)));
  }

  // Recursive linked-list discovery, with nil.  Note that the output memory
  // has the output memory alias, but not the input memory alias (which must be
  // made before calling 'map').
  @Test public void test33() {
    run("map = { fcn lst -> (if lst @{ n1=(map fcn lst.n0), v1=(fcn lst.v0) } 0) }; map",
        "{ { A -> B } C:@{ n0 = C; v0 = A; ...}? -> D:@{ n1 = D; v1 = B}? }",
        // Build a cycle of length 2, with nil.
        () -> tfs(build_cycle(9,true,Type.SCALAR)));
  }

  // Recursive linked-list discovery, with no end clause
  @Test public void test34() {
    run("map = { fcn lst -> (if lst @{ n1 = (map fcn lst.n0), v1 = (fcn lst.v0) } 0) }; (map dec @{n0 = 0, v0 = 5})",
        "A:@{ n1 = A; v1 = int64}?",
        ()->build_cycle(9,true,TypeInt.con(4)));
  }

  // try the worse-case expo blow-up test case from SO
  @Test public void test35() {
    TypeFunPtr tfp  = TypeFunPtr.make(15,3,Type.ANY,Type.SCALAR);
    TypeMemPtr tmp0 = TypeMemPtr.make(8,make_tups(tfp ,tfp ,tfp ));
    TypeMemPtr tmp1 = TypeMemPtr.make(8,make_tups(tmp0,tmp0,tmp0));
    TypeMemPtr tmp2 = TypeMemPtr.make(8,make_tups(tmp1,tmp1,tmp1));

    run("p0 = { x y z -> (triple x y z) };"+
        "p1 = (triple p0 p0 p0);"+
        "p2 = (triple p1 p1 p1);"+
        "p3 = (triple p2 p2 p2);"+
        "p3",
        "( ( ( { A B C -> ( A, B, C) }, { D E F -> ( D, E, F) }, { G H I -> ( G, H, I) }), ( { J K L -> ( J, K, L) }, { M N O -> ( M, N, O) }, { P Q R -> ( P, Q, R) }), ( { S T U -> ( S, T, U) }, { V22 V23 V24 -> ( V22, V23, V24) }, { V25 V26 V27 -> ( V25, V26, V27) })), ( ( { V28 V29 V30 -> ( V28, V29, V30) }, { V31 V32 V33 -> ( V31, V32, V33) }, { V34 V35 V36 -> ( V34, V35, V36) }), ( { V37 V38 V39 -> ( V37, V38, V39) }, { V40 V41 V42 -> ( V40, V41, V42) }, { V43 V44 V45 -> ( V43, V44, V45) }), ( { V46 V47 V48 -> ( V46, V47, V48) }, { V49 V50 V51 -> ( V49, V50, V51) }, { V52 V53 V54 -> ( V52, V53, V54) })), ( ( { V55 V56 V57 -> ( V55, V56, V57) }, { V58 V59 V60 -> ( V58, V59, V60) }, { V61 V62 V63 -> ( V61, V62, V63) }), ( { V64 V65 V66 -> ( V64, V65, V66) }, { V67 V68 V69 -> ( V67, V68, V69) }, { V70 V71 V72 -> ( V70, V71, V72) }), ( { V73 V74 V75 -> ( V73, V74, V75) }, { V76 V77 V78 -> ( V76, V77, V78) }, { V79 V80 V81 -> ( V79, V80, V81) })))",
        tmp2  );
  }

  // Need to see if a map call, inlined a few times, 'rolls up'.  Sometimes
  // rolls up, sometimes not; depends on worklist visitation order.
  @Test public void test36() {
    run("map = { lst -> (if lst @{ n1= arg= lst.n0; (if arg @{ n1=(map arg.n0), v1=(str arg.v0)} 0), v1=(str lst.v0) } 0) }; map",
        "{ A:@{ n0 = @{ n0 = A; v0 = int64; ...}?; v0 = int64; ...}? -> B:@{ n1 = @{ n1 = B; v1 = *[4]str}?; v1 = *[4]str}? }",
        ()-> tfs(build_cycle2(true,TypeMemPtr.STRPTR)));
  }

  @Test public void test37() { run("x = { y -> (x (y y))}; x",
                                   "{ A:{ A -> A } -> B }", tfs(Type.XSCALAR)); }

  // Example from SimpleSub requiring 'x' to be both a struct with field
  // 'v', and also a function type - specifically disallowed in 'aa'.
  @Test public void test38() { run("{ x -> y = ( x x.v ); 0}",
                                   "{ { A:Missing field v in {A->B} -> B } -> C? }",
                                   tfs(Type.XNIL)); }

  // Really bad flow-type: function can be called from the REPL with any
  // argument type - and the worse case will be an error.
  @Test public void test39() {
    run("x = { z -> z}; (x { y -> y.u})",
        "{ @{ u = A; ...} -> A }",
        tfs(Type.SCALAR));
  }

  // Example from SimpleSub requiring 'x' to be both:
  // - a recursive self-call function from "w = (x x)": $V66:{ $V66 -> V67 } AND
  // - a function which takes a struct with field 'u'
  // The first arg to x is two different kinds of functions, so fails unification.
  @Test public void test40() {
    run("x = w = (x x); { z -> z}; (x { y -> y.u})",
        "A:Cannot unify { A -> A } and @{ u = A; ... }",
        "A:Cannot unify { A -> A } and @{ u = A; ... }",
        tfs(Type.SCALAR),
        Type.SCALAR);
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
        "( *[4]str, int1)",
        "( *[4]str, int1)",
        // With lift ON
        //TypeMemPtr.make(7,make_tups(TypeMemPtr.STRPTR,TypeInt.BOOL)),
        // With lift OFF
        tuple2,
        tuple2);
  }

  // CCP Can help HM
  @Test public void test42() {
    run("pred = 0; s1 = @{ x=\"abc\" }; s2 = @{ y=3.4 }; (if pred s1 s2).y",
        "3.4000000953674316",
        "Missing field y in ( )",
        TypeFlt.con(3.4f),
        TypeFlt.con(3.4f));
  }

  // The z-merge is ignored; the last s2 is a fresh (unmerged) copy.
  @Test public void test43() {
    run("pred = 0; s1 = @{ x=\"abc\" }; s2 = @{ y=3.4 }; z = (if pred s1 s2).x; s2.y",
        "3.4000000953674316",TypeFlt.con(3.4f));
  }

  @Test public void test44() {
    run("fun = (if (isempty \"abc\") {x->x} {x->1.2}); (fun @{})",
        "1.2000000476837158",
        "Cannot unify 1.2000000476837158 and ()",
        TypeFlt.con(1.2f),
        TypeFlt.con(1.2f));
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
        "*[0,4]str?",  // Both HM and GCP
        "Cannot unify int8 and *[0,4]str?", // HM alone cannot do this one
        // With lift ON
        //TypeMemPtr.make(4,TypeStr.STR), // Both HM and GCP
        // With lift OFF
        Type.NSCALR,
        Type.NSCALR);                   // GCP alone gets a very weak answer
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
    run("""
{ pred ->
  map = { fun x -> (fun x) };
  (pair (map {str0 ->          str0.x   }          @{x = 3}   )
        (map {str1 -> (if str1 str1.x 4)} (if pred @{x = 5} 0))
  )
}
""",
        "{ A? -> ( int64, int64) }",
        tfs(TypeMemPtr.make(7,make_tups(TypeInt.NINT8, TypeInt.NINT8 ))));
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
        "{ A? -> May be nil when loading field x }",
        "{ A? -> May be nil when loading field x }",
        tfs(TypeMemPtr.make(7,make_tups(TypeInt.NINT8, TypeInt.NINT8 ))),
        tfs(TypeMemPtr.make(7,make_tups(TypeInt.NINT8, TypeInt.NINT8 ))));
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
        tfs(TypeInt.INT64),
        tfs(Type.SCALAR  ));
  }

  // Create a boolean-like structure, and unify.
  @Test public void test52() {
    run("void = @{};"+              // Same as '()'; all empty structs are alike
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
        "",
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
        "@{ a = nint8; b = ( ); bool = @{ false = A:@{ and = { A -> A }; or = { A -> A }; thenElse = { { ( ) -> B } { ( ) -> B } -> B }}; force = { C? -> D:@{ and = { D -> D }; or = { D -> D }; thenElse = { { ( ) -> E } { ( ) -> E } -> E }} }; true = F:@{ and = { F -> F }; or = { F -> F }; thenElse = { { ( ) -> G } { ( ) -> G } -> G }}}}",
        () -> {
          Type tf   = TypeMemPtr.make(BitsAlias.FULL.make(10,11),
                                      TypeStruct.make(TypeFld.NO_DISP,
                                                      TypeFld.make("and"     ,TypeFunPtr.make(BitsFun.make0(14,17),1)),
                                                      TypeFld.make("or"      ,TypeFunPtr.make(BitsFun.make0(15,18),1)),
                                                      TypeFld.make("thenElse",TypeFunPtr.make(BitsFun.make0(16,19),2))));
          Type xbool= TypeMemPtr.make(12,TypeStruct.make(TypeFld.NO_DISP,
                                                         TypeFld.make("true", tf),
                                                         TypeFld.make("false",tf),
                                                         TypeFld.make("force",TypeFunPtr.make(BitsFun.make0(23),1))));
          TypeStruct rez = TypeStruct.make(TypeFld.NO_DISP,
                                           // With lift ON
                                           //TypeFld.make("a", HM.DO_HM ? TypeInt.NINT8 : Type.SCALAR),
                                           //TypeFld.make("b", HM.DO_HM ? TypeMemPtr.make(BitsAlias.FULL.make(13,14),TypeStruct.maket()) : Type.SCALAR),
                                           // With lift OFF
                                           TypeFld.make("a", Type.SCALAR),
                                           TypeFld.make("b", Type.SCALAR),
                                           TypeFld.make("bool",xbool));
          return TypeMemPtr.make(15,rez);
        }
        );
  }


  // Simple nil/default test; takes a nilable but does not return one.
  @Test public void test53() { run( "{ x y -> (if x x y) }",
                                    "{ A? A -> A }", tfs(Type.SCALAR));  }

  // Double nested.  Currently fails to unify x and y.
  @Test public void test54() { run( "{ x y -> (if x (if x x y) y) }",
                                    "{ A? A -> A }", tfs(Type.SCALAR));  }

  // Regression test; was NPE.  Was testMyBoolsNullPException from marco.servetto@gmail.com.
  @Test public void test55() {
    run("""
void = @{};
true = @{
  and      = {b -> b}
  or       = {b -> true}
  not      = {unused ->true}
  thenElse = {then else->(then void) }
};
false = @{
  and      = {b -> false}
  or       = {b -> b}
  not      = {unused ->true}
  thenElse = {then else->(else void) }
};
boolSub ={b ->(if b true false)};
@{true=(boolSub 1) false=(boolSub 0)}
""",
        "@{ false = A:@{ and = { A -> A }; "+
              "not = { B -> A }; "+
              "or = { A -> A }; "+
              "thenElse = { { ( ) -> C } { ( ) -> C } -> C }"+
            "}; "+
            "true = D:@{ and = { D -> D }; "+
              "not = { E -> D }; "+
              "or = { D -> D }; "+
              "thenElse = { { ( ) -> F } { ( ) -> F } -> F }"+
            "}"+
        "}",
        () -> {
          // true/false=*[10,11]@{$; and=[15,19]{any }; or=[16,20]{any }; not=[17,21]{any }; thenElse=[18,22]{any }}
          Type tf   = TypeMemPtr.make(BitsAlias.FULL.make(10,11),
                                      TypeStruct.make(TypeFld.NO_DISP,
                                                      TypeFld.make("and"     ,TypeFunPtr.make(BitsFun.make0(14,18),1)),
                                                      TypeFld.make("or"      ,TypeFunPtr.make(BitsFun.make0(15,19),1)),
                                                      TypeFld.make("not"     ,TypeFunPtr.make(BitsFun.make0(16,20),1)),
                                                      TypeFld.make("thenElse",TypeFunPtr.make(BitsFun.make0(17,21),2))));
          // *[12]@{^=any; true=$TF; false=$TF}
          TypeStruct rez = TypeStruct.make("",false,false,TypeFld.NO_DISP,TypeFld.make("true",tf),TypeFld.make("false",tf));
          return TypeMemPtr.make(12,rez);
        } );
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
        build_cycle2(false,TypeInt.con(7)));
  }

  @Test public void test57() {
    run("""
all =
true = @{
  not = {unused -> all.false},
  thenElse = {then else->(then 7) }
};
false = @{
  not = {unused -> all.true},
  thenElse = {then else->(else 7) }
};
boolSub ={b ->(if b true false)};
@{true=true, false=false, boolSub=boolSub};
all
""",
        "@{ boolSub = { A? -> @{ not = { B -> C:@{ not = { D -> C }; thenElse = { { int64 -> E } { int64 -> E } -> E }} }; thenElse = { { int64 -> F } { int64 -> F } -> F }} }; false = C; true = C}",
        () -> {
          Type tt = TypeMemPtr.make(BitsAlias.FULL.make(9),
                                    TypeStruct.make("",false,false,TypeFld.NO_DISP,
                                                    TypeFld.make("not"     ,TypeFunPtr.make(BitsFun.make0(14),1)),
                                                    TypeFld.make("thenElse",TypeFunPtr.make(BitsFun.make0(15),2))));
          Type ff = TypeMemPtr.make(BitsAlias.FULL.make(10),
                                    TypeStruct.make("",false,false,TypeFld.NO_DISP,
                                                    TypeFld.make("not"     ,TypeFunPtr.make(BitsFun.make0(16),1)),
                                                    TypeFld.make("thenElse",TypeFunPtr.make(BitsFun.make0(17),2))));
          TypeStruct rez = TypeStruct.make(TypeFld.NO_DISP,
                                           TypeFld.make("true"   ,tt),
                                           TypeFld.make("false"  ,ff),
                                           TypeFld.make("boolSub",TypeFunPtr.make(BitsFun.make0(21),1)));

          return TypeMemPtr.make(11,rez);
        });
  }

  // Full on Peano arithmetic.
  @Test public void test58() {
    run(
        "void = @{};                                   "+
        "err  = {unused->(err unused)};                "+
        // Booleans, support AND, OR, THENELSE.  Eg. b.false.and is a function which
        // ignores its input and returns false.
        "b=                                            "+
        "  true = @{                                   "+
        "    and      = {o -> o}                       "+ // true  AND anything is that thing
        "    or       = {o -> b.true}                  "+ // true  OR  anything is true
        "    thenElse = {then else->(then void) }      "+
        "  };                                          "+
        "  false = @{                                  "+
        "    and      = {o -> b.false}                 "+ // false AND anything is false
        "    or       = {o -> o}                       "+ // false OR  anything is that thing
        "    thenElse = {then else->(else void) }      "+
        "  };                                          "+
        "  @{true=true, false=false};                  "+
        // Natural numbers are formed from zero (z) and succ (s).
        // They are structs which support isZero, pred, succ and add.
        "n=                                            "+
        // Zero, is a struct supporting functions "isZero" (always true), "pred"
        // (error; no predecessor of zero), "succ" successor, and "add" which is a no-op.
        "  z = @{                                      "+
        "    isZero = {unused ->b.true},               "+
        "    pred   = err                              "+
        "    succ   = {unused -> (n.s n.z)},           "+
        "    add    = {o-> o}                          "+
        "  };                                          "+
        // Successor, is a function taking a natural number and returning the successor
        // (which is just a struct supporting the functions of natural numbers).
        "  s = {pred ->                                "+
        "    self=@{                                   "+
        "      isZero = {unused ->b.false},            "+ // isZero is always false for anything other than zero
        "      pred   = {unused->pred},                "+ // careful! 'pred=' is a label, the returned 'pred' was given as the argument
        "      succ   = {unused -> (n.s self)},        "+
        "      add    = {m -> ((pred.add m).succ void)}"+ // a little odd, but really this counts down (via recursion) on the LHS and applies that many succ on the RHS
        "    };                                        "+
        "    self                                      "+
        "  };                                          "+
        "  @{s=s, z=z};                                "+
        // Do some Maths
        "one = (n.s n.z);                              "+ // One is the successor of zero
        "two = (one.add one);                          "+ // Two is one plus one
        "three =(n.s two);                             "+ // Three is the successor of two
        // Return a result, so things are not dead.
        "@{b=b,n=n, one=one,two=two,three=three}"+
        "",
        "@{" +
        // Booleans, support AND, OR, THENELSE.  Eg. b.false.and is a function which
        // ignores its input and returns false.
        "  b=@{ false=A:@{ and={B->A}; or={C->C}; thenElse={D {()->E} ->E} };"+
        "       true =F:@{ and={G->G}; or={H->F}; thenElse={{()->I} J ->I} }"+
        "  };"+
        // Natural numbers are formed from zero (z) and succ (s).
        "  n=@{"+
        "    s={"+
        // K is the type var of a natural number: a struct supporting pred,succ,add,isZero.
        // So 's' succ is a function which takes a natural number (K) and returns a K.
        "      K:@{ add   ={ L:@{ succ={()->L}; ...} ->L };"+
        "           isZero={ M -> N:@{ and={N->N}; or={N->N}; thenElse={ {()->O} {()->O} -> O }}};"+
        "           pred  ={ P -> K};"+
        "           succ  ={ Q -> K}"+
        "        } -> K };"+
        "    z=K"+         // Zero is also a natural number
        "  };"+
        // One is formed by taking the successor of zero: "(n.s n.z)".  It has the same
        // shape as any natural number ("self" structural shape above), but its type is
        // not unified with "self".
        "  one=R:@{"+
        "    add   ={ S:@{ succ={()->S}; ...} -> S};"+
        "    isZero={  T  -> U:@{ and={U->U}; or={U->U}; thenElse={ {()->V22} {()->V22}->V22}}};"+
        "    pred=  { V23 -> R };"+
        "    succ=  { V24 -> R }"+      // Note: succ takes an 'unused'
        "  };"+
        // Has all the fields of a natural number.
        "  three=V25:@{ "+
        "    add   ={ V26:@{ succ={()->V26}; ... }->V26  };"+
        "    isZero={ V27 -> V28:@{ and={V28->V28}; or={V28->V28}; thenElse={ {()->V29} {()->V29} ->V29 }}};"+
        "    pred  ={ V30 -> V25 };"+
        "    succ  ={ ()  -> V25 }"+ // Note 'succ' only takes 'void', and not an 'unused'.
        "  };"+
        // Has all the fields of a natural number.
        "  two=V31:@{ "+
        "    add   ={ V32:@{succ={()->V32}; ...} ->V32 };"+
        "    isZero={ V33 -> V34:@{ and={V34->V34}; or={V34->V34}; thenElse={ {()->V35} {()->V35} ->V35 }}};"+
        "    pred  ={ V36 -> V31};"+
        "    succ  ={ ()  -> V31}"+ // Note 'succ' only takes a 'void', and not an 'unused'.
        "  }"+
        "}"+
        "",
        () -> {
          // *[16]@{^ = any;
          //        b = *[12]@{$;
          //          true =*[10]@{$; and=[16]{any }; or=[17]{any }; thenElse=[18]{any }};
          //          false=*[11]@{$; and=[19]{any }; or=[20]{any }; thenElse=[21]{any }}
          //        };
          //        n = *[15]@{$;
          //                   s = [29]{any };
          //                   z =*[13]@{$; isZero=[22]{any }; pred=[15]{any }; succ=[23]{any }; add=[24]{any }}
          //        };
          //        one = *[14]@{$; isZero=[25]{any }; pred=[26]{any }; succ=[27]{any }; add=[28]{any }};
          //        two = $;
          //        three=$
          // }
          TypeFld bt = bfun("true" ,10,15,16,17);
          TypeFld bf = bfun("false",11,18,19,20);
          TypeFld b  = mptr("b",12,TypeStruct.make(TypeFld.NO_DISP,bt,bf)); // Booleans

          TypeFld s  = mfun("s",28);
          TypeFld z  = nfun("z",13,21,14,22,23);
          TypeFld n  = mptr("n",15,TypeStruct.make(TypeFld.NO_DISP,s,z));

          TypeFld n1 = nfun("one"  ,14,24,25,26,27);
          // With lift ON
          //TypeFld n2 = HM.DO_HM ? nfun("two"  ,14,24,25,26,27) : TypeFld.make("two",Type.SCALAR);
          // With lift OFF
          TypeFld n2 = TypeFld.make("two",Type.SCALAR);
          TypeFld n3 = nfun("three",14,24,25,26,27);

          Type rez = TypeMemPtr.make(16,TypeStruct.make(TypeFld.NO_DISP,b,n,n1,n2,n3));
          return rez;
        });
  }

  // Make field holding a pointer to a struct
  private static TypeFld mptr( String fld, int alias, TypeStruct ts ) {
    return TypeFld.make(fld,TypeMemPtr.make(alias,ts));
  }
  // Make a field holding a function pointer
  private static TypeFld mfun( String fld, int fidx ) { return mfun(fld,fidx,1); }
  private static TypeFld mfun( String fld, int fidx, int nargs ) {
    return TypeFld.make(fld,TypeFunPtr.make(BitsFun.make0(fidx),nargs));
  }

  // Make a boolean field, with struct fields and,or,thenElse
  private static TypeFld bfun( String fld, int alias, int afidx, int ofidx, int tfidx ) {
    return mptr(fld,alias,TypeStruct.make(TypeFld.NO_DISP,mfun("and",afidx),mfun("or",ofidx),mfun("thenElse",tfidx,2) ) );
  }

  // Make a natural numbers field, with struct fields isZero,pred,succ,add
  private static TypeFld nfun( String fld, int alias, int zfidx, int pfidx, int sfidx, int afidx) {
    return mptr(fld,alias,TypeStruct.make(TypeFld.NO_DISP,mfun("isZero",zfidx),mfun("pred",pfidx),mfun("succ",sfidx), mfun("add",afidx) ));
  }


  // Checking an AA example
  @Test public void test59() {
    run("prod = { x -> (if x (* (prod x.n) x.v) 1)};"+
        "(prod @{n= @{n=0, v=3}, v=2})"+
        "",
        "int64",
        TypeInt.INT64);
  }

  // Unexpected restriction on extra fields.
  @Test public void test60() {
    // Build a cycle of length 1.
    Type.RECURSIVE_MEET++;
    TypeFld f = TypeFld.malloc("succ",null,TypeFld.Access.Final,TypeFld.oBot);
    TypeStruct ts = TypeStruct.malloc("",false,false,TypeFld.NO_DISP,f).set_hash();
    TypeMemPtr p = TypeMemPtr.make(9,ts);
    f.setX(p);
    Type.RECURSIVE_MEET--;
    ts.install();

    run("sx = { ignore -> "+
        "  self0=@{ succ = (sx self0)}; "+
        "  self0 "+
        "};"+
        "self1=@{ succ = self1, nope=7 };"+
        "(sx self1)"+
        "",
        "A:@{ succ=A}",p);
  }

  // Broken from Marco; function 'f' clearly uses 'p2.a' but example 'res1' does not
  // pass in a field 'a'... and still no error.  Fixed.
  @Test public void test61() {
    run("f = { p1 p2 -> (if p2.a p1 p2)};"+"(f @{a=2}   @{b=2.3})",
        "@{ a= Missing field a in ()}",
        "@{ a= Missing field a in ()}",
        () -> TypeMemPtr.make(BitsAlias.FULL.make(9,10),
                              TypeStruct.make(TypeFld.NO_DISP,TypeFld.make("a",Type.SCALAR))),
        () -> TypeMemPtr.make(BitsAlias.FULL.make(9,10),
                              TypeStruct.make(TypeFld.NO_DISP)));
  }

  // Broken from Marco; function 'f' clearly uses 'p2.a' but example 'res1' does not
  // pass in a field 'a'... and still no error.  Fixed.
  @Test public void test62() { run("f = { p1 -> p1.a };"+"(f @{b=2.3})",
                                    "Missing field a in @{b=flt64}",
                                   Type.SCALAR);  }

  @Test public void test63() {
    run("A=@{x=3, y=3.2};"+
        "B=@{x=4, z=\"abc\"};"+
        "rez = { pred -> (if pred A B)};"+
        "rez"+
        "",
        "{ A? -> @{x=nint8} }",
        () -> tfs(TypeMemPtr.make(BitsAlias.FULL.make(9,10),TypeStruct.make(TypeFld.NO_DISP,TypeFld.make("x",TypeInt.NINT8)))));
  }

  // Broken from Marco; function 'f' clearly uses 'p2.a' but example 'res1' does not
  // pass in a field 'a'... and still no error.  Fixed.
  @Test public void test64() {
    run("f = { p1 p2 -> (if p2.a p1 p2)};"+
        "res1 = (f @{a=2,      c=\"def\"} @{    b=2.3,d=\"abc\"});"+
        "res2 = (f @{a=2,b=1.2,c=\"def\"} @{a=3,b=2.3,d=\"abc\"});"+
        "@{f=f,res1=res1,res2=res2}",

        "@{ f    =  { A:@{ a=B;... } A -> A };"+
        "   res1 = @{ a = Missing field a in () };"+
        "   res2 = @{ a=int64; b=flt64 }"+
        "}",
        "@{ f    =  { A:@{ a=B;... } A -> A };"+
        "   res1 = @{ a = Missing field a in () };"+
        "   res2 = @{ a=int64; b=flt64 }"+
        "}",
        () -> {
          Type tmp9hm = TypeMemPtr.make(BitsAlias.FULL.make(9,10,11,12),
                                        TypeStruct.make(TypeFld.NO_DISP
                                                        // With Lift ON
                                                        //, TypeFld.make("a",Type.SCALAR)
                                                        ));
          Type tmp9hmab = TypeMemPtr.make(BitsAlias.FULL.make(9,10,11,12),
                                          TypeStruct.make(  TypeFld.NO_DISP
                                                          // With Lift ON
                                                          //, TypeFld.make("a",TypeInt.INT64)
                                                          //, TypeFld.make("b",TypeFlt.FLT64)
                                                            )
                                          );
          //*[13]@{^=any; f=[15]{any }; res1=*[9,10,11,12]($); res2=$}
          Type rezhm = TypeMemPtr.make(BitsAlias.make0(13),
                                       TypeStruct.make(TypeFld.NO_DISP,
                                                       TypeFld.make("f",TypeFunPtr.make(BitsFun.make0(15),2)),
                                                       TypeFld.make("res1",tmp9hm),
                                                       TypeFld.make("res2",tmp9hmab)));
          return rezhm;
        },
        () -> {
          return TypeMemPtr.make(BitsAlias.make0(13),
                                 TypeStruct.make(TypeFld.NO_DISP,
                                                 TypeFld.make("f",TypeFunPtr.make(BitsFun.make0(15),2)),
                                                 TypeFld.make("res1",Type.SCALAR),
                                                 TypeFld.make("res2",Type.SCALAR)));
        });
  }


  // Regression during the HM/GCP Apply lift.
  @Test public void test65() {
    run("""
all=
  void = @{};
  err  = {unused->(err unused)};
  true = @{
    and      = {b -> b}
    or       = {b -> all.true}
    thenElse = {then else->(then void) }
    };
  false = @{
    and      = {b -> all.false}
    or       = {b -> b}
    thenElse = {then else->(else void) }
    };
  boolSub ={b ->(if b true false)};
  z = @{
    isZero = {unused ->all.true}
    pred = err
    succ = {n -> (all.s n)}
    add = {n-> n}
    };
  orZero = {n ->(true.thenElse {unused ->n} {unused ->z})};
  s = {pred ->
    self=@{
      isZero = {unused ->all.false}
      pred = {unused->pred}
      succ = {unused -> (all.s self)}
      add ={m -> (self.succ (pred.add m))}
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
    thenElse={{()->B}{()->B}->B}
    };
  s={
    C:@{
      add={C->C};
      isZero={D->A};
      pred={E->C};
      succ={C->C}
      }
    ->C
    };
  true=A;
  z=@{
    add={F->F};
    isZero={G->A};
    pred={H->I};
    succ={C->C}
    }
  }
""",
        /*
         *[14]@{^    =any;
                false=*[10,11]@{$; and=[15,18]{any ->Scalar }; or=[16,19]{any ->Scalar }; thenElse=[17,20]{any ->Scalar }};
                true = $;
                s    = [  35 ]{any ->Scalar };
                z=*[12]@{$; add=[27]{any ->Scalar }; isZero=[25]{any ->Scalar }; pred=[14]{any ->Scalar }; succ=[26]{any ->Scalar }}
          }
        */
        () -> {
          TypeFld and = bfun2("and" ,15,18,1);
          TypeFld or  = bfun2("or"  ,16,19,1);
          TypeFld thn = bfun2("thenElse",17,20,2);
          TypeMemPtr tf = TypeMemPtr.make(BitsAlias.make0(10).or(11),TypeStruct.make(TypeFld.NO_DISP,and,or,thn));
          TypeFld f = TypeFld.make("false",tf);
          TypeFld t = TypeFld.make("true",tf);

          TypeFld s = mfun("s",35);

          TypeFld pred  = mfun("pred"  ,14);
          TypeFld isZero= mfun("isZero",25);
          TypeFld add   = mfun("add"   ,27);
          TypeFld succ  = mfun("succ"  ,26);
          TypeFld z = TypeFld.make("z",TypeMemPtr.make(BitsAlias.make0(12),TypeStruct.make(TypeFld.NO_DISP,pred,isZero,add,succ)));
          return TypeMemPtr.make(BitsAlias.make0(14),TypeStruct.make(TypeFld.NO_DISP,f,t,s,z));
        });
  }
private static TypeFld bfun2(String fld, int a0, int a1, int nargs ) {
    return TypeFld.make(fld,TypeFunPtr.make(BitsFun.make0(a0,a1),nargs));
  }


  // Poster-child collection, larger example
  @Test public void test66() {
    run("""
rand = (factor 1.2).0;
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
        "(flt64,flt64,*[4]str)",
        "(flt64,flt64,*[4]str)",
        // With lift ON
        //TypeMemPtr.make(8, make_tups(TypeFlt.FLT64, TypeFlt.FLT64, TypeMemPtr.STRPTR)),
        // With lift OFF
        TypeMemPtr.make(8, make_tups(Type.SCALAR  , Type.SCALAR  , TypeMemPtr.STRPTR)),
        TypeMemPtr.make(8, make_tups(Type.SCALAR  , Type.SCALAR  , TypeMemPtr.STRPTR)) );
  }

}

