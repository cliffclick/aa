package com.cliffc.aa.HM;

import com.cliffc.aa.HM.HM9.Root;
import com.cliffc.aa.type.*;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class TestHM9 {

  @Before public void reset() { HM.reset(); }

  private void run( String prog, String rez_hm, Type rez_gcp ) {
    Root syn = HM9.hm(prog);
    if( HM.DO_HM )
      assertEquals(rez_hm,syn._hmt.p());
    if( HM.DO_GCP )
      assertEquals(rez_gcp,syn.flow_type());
  }
  // Simple no-arg signature returning the type
  private static TypeFunSig tfs(Type ret) {
    return TypeFunSig.make(TypeTuple.make_ret(ret),TypeTuple.make_args());
  }

  private static final TypeMemPtr tuple2  = TypeMemPtr.make(7,TypeStruct.maket(Type.SCALAR,   Type.SCALAR   ));
  private static final TypeMemPtr tuplen2 = TypeMemPtr.make(7,TypeStruct.maket(Type.NSCALR,   Type.NSCALR   ));
  private static final TypeMemPtr tuple82 = TypeMemPtr.make(7,TypeStruct.maket(TypeInt.NINT8, TypeInt.NINT8 ));
  private static final TypeMemPtr tuple55 = TypeMemPtr.make(7,TypeStruct.maket(TypeInt.con(5),TypeInt.con(5)));
  private static final TypeFunSig ret_tuple2 = tfs(tuple2);
  private static final String[] XY = new String[]{"^","x","y"};
  private static final String[] N1V1 = new String[]{"^","n1","v1"};
  private static final TypeMemPtr tuple9  = TypeMemPtr.make(9,TypeStruct.maket(Type.SCALAR,Type.SCALAR));

  @Test(expected = RuntimeException.class)
  public void test00() { run( "fred",null,null); }

  @Test public void test01() { run( "3" ,
                                    "3", TypeInt.con(3));  }

  @Test public void test02() { run( "(pair1 3)" ,
                                    "{ A -> ( 3, $A)[7] }", tfs(TypeMemPtr.make(7,TypeStruct.maket(TypeInt.con(3),Type.SCALAR)))); }

  @Test public void test03() { run( "{ z -> (pair (z 0) (z \"abc\")) }" ,
                                    "{ { *[0,4]\"abc\"? -> A } -> ( $A, $A)[7] }", tfs(tuple2)); }

  @Test public void test04() { run( "fact = { n -> (if (?0 n) 1 (* n (fact (dec n))))}; fact",
                                    "{ int64 -> int64 }", tfs(TypeInt.INT64) ); }

  // Because {y->y} is passed in, all 'y' types must agree.
  // This unifies 3 and "abc" which results in 'all'
  @Test public void test05() {
    Root syn = HM9.hm("({ x -> (pair (x 3) (x 5)) } {y->y})");
    if( HM.DO_HM )
      assertEquals("( nint8, nint8)[7]",syn._hmt.p());
    if( HM.DO_GCP )
      if( HM.DO_HM )
        assertEquals(tuple82,syn.flow_type());
      else
        assertEquals(tuple82,syn.flow_type());
  }

  @Test public void test06() {
    Root syn = HM9.hm("id={x->x}; (pair (id 3) (id \"abc\"))");
    if( HM.DO_HM ) // HM is sharper here than in test05, because id is generalized per each use site
      assertEquals("( 3, *[4]\"abc\")[7]",syn._hmt.p());
    if( HM.DO_GCP )
      if( HM.DO_HM )
        assertEquals(TypeMemPtr.make(7,TypeStruct.maket(TypeInt.con(3),TypeMemPtr.make(4,TypeStr.ABC))),syn.flow_type());
      else
        assertEquals(tuplen2,syn.flow_type());
  }

  // recursive unification; normal H-M fails here.
  @Test public void test07() { run( "{ f -> (f f) }",
    // We can argue the pretty-print should print:
    //                              "  A:{ $A -> B }"
                                    "{ A:{ $A -> B } -> $B }", tfs(Type.SCALAR) ); }

  @Test public void test08() { run( "g = {f -> 5}; (g g)",
                                    "5", TypeInt.con(5)); }

  // example that demonstrates generic and non-generic variables:
  @Test public void test09() { run( "{ g -> f = { x -> g }; (pair (f 3) (f \"abc\"))}",
                                    "{ A -> ( $A, $A)[7] }", ret_tuple2); }

  @Test public void test10() { run( "{ f g -> (f g)}",
                                    "{ { A -> B } $A -> $B }", tfs(Type.SCALAR) ); }

  // Function composition
  @Test public void test11() { run( "{ f g -> { arg -> (g (f arg))} }",
                                    "{ { A -> B } { $B -> C } -> { $A -> $C } }", tfs(tfs(Type.SCALAR))); }

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
    Root syn = HM9.hm("map = { fun -> { x -> (fun x)}};"+
                     "(pair ((map str) 5) ((map factor) 2.3))");
    if( HM.DO_HM )
      assertEquals("( *[4]str, flt64)[7]",syn._hmt.p());
    if( HM.DO_GCP )
      if( HM.DO_HM )
        assertEquals(TypeMemPtr.make(7,TypeStruct.maket(TypeMemPtr.STRPTR,TypeFlt.FLT64)),syn.flow_type());
      else
        assertEquals(tuple2,syn.flow_type());
  }

  // map takes a function and an element (collection?) and applies it (applies to collection?)
  @Test public void test15() { run("map = { fun x -> (fun x)}; (map {a->3} 5)",
                                   "3", TypeInt.con(3)); }

  // map takes a function and an element (collection?) and applies it (applies to collection?)
  @Test public void test16() { run("map = { fun x -> (fun x)}; (map { a-> (pair a a)} 5)",
                                   "( 5, 5)[7]", tuple55); }

  @Test public void test17() { run("fcn = { p -> { a -> (pair a a) }};"+
                                   "map = { fun x -> (fun x)};"+
                                   "{ q -> (map (fcn q) 5)}",
                                   "{ A -> ( 5, 5)[7] }", tfs(tuple55)); }

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
    Root syn = HM9.hm("fcn = {p -> (if p {a -> (pair a a)} {b -> (pair b (pair 3 b))})};"+
                     "map = { fun x -> (fun x)};"+
                     "{ q -> (map (fcn q) 5)}");
    if( HM.DO_HM )
      assertEquals("{ A -> ( B:Cannot unify A:( 3, $A)[7] and 5, $B)[7] }",syn._hmt.p());
    if( HM.DO_GCP )
      if( HM.DO_HM )
        assertEquals(tfs(TypeMemPtr.make(7,TypeStruct.maket(Type.XNSCALR,TypeMemPtr.make(7,TypeStruct.maket(TypeInt.con(3),Type.XNSCALR))))),syn.flow_type());
      else
        assertEquals(tfs(TypeMemPtr.make(7,TypeStruct.maket(TypeInt.con(5),Type.NSCALR))),syn.flow_type());
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
    Root syn = HM9.hm("cons ={x y-> {cadr -> (cadr x y)}};"+
                     "cdr ={mycons -> (mycons { p q -> q})};"+
                     "map ={fun parg -> (fun (cdr parg))};"+
                     "(pair (map str (cons 0 5)) (map isempty (cons 0 \"abc\")))");
    if( HM.DO_HM )
      assertEquals("( *[4]str, int1)[7]",syn._hmt.p());
    if( HM.DO_GCP )
      if( HM.DO_HM )
        assertEquals(TypeMemPtr.make(7,TypeStruct.maket(TypeMemPtr.STRPTR,TypeInt.BOOL)),syn.flow_type());
      else
        assertEquals(tuple2,syn.flow_type());
  }

  // Obscure factorial-like
  @Test public void test21() { run("f0 = { f x -> (if (?0 x) 1 (f (f0 f (dec x)) 2))}; (f0 * 99)",
                                   "int64", TypeInt.INT64); }

  // Obscure factorial-like
  // let f0 = fn f x => (if (?0 x) 1 (* (f0 f (dec x)) 2) ) in f0 f0 99
  // let f0 = fn f x => (if (?0 x) 1 (f (f0 f (dec x)) 2) ) in f0 *  99
  @Test public void test22() { run("f0 = { f x -> (if (?0 x) 1 (* (f0 f (dec x)) 2))}; (f0 f0 99)",
                                   "int64", TypeInt.INT64); }

  // Mutual recursion
  @Test public void test23() { run("is_even = "+
                                   "  is_odd = { n -> (if (?0 n) 0 (is_even (dec n)))}; "+
                                   "     { n -> (if (?0 n) 1 (is_odd (dec n)))};"+
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
                                   "{ { nint8 -> A } -> ( $A, $A)[7] }", tfs(tuple2)); }

  // Basic structure test
  @Test public void test25() { run("@{x=2, y=3}",
                                   "@{ x = 2, y = 3}[9]",
                                   TypeMemPtr.make(9,TypeStruct.maket(TypeInt.con(2),TypeInt.con(3)))
                                   ); }

  // Basic field test
  @Test public void test26() { run(".x @{x =2, y =3}",
                                   "2", TypeInt.con(2)); }

  // Basic field test
  @Test public void test27() { run(".x 5",
                                   "Missing field x in 5", Type.SCALAR); }

  // Basic field test.
  @Test public void test28() { run(".x @{ y =3}",
                                   "Missing field x in @{ y = 3}[9]",
                                   Type.SCALAR); }

  @Test public void test29() { run("{ g -> @{x=g, y=g}}",
                                   "{ A -> @{ x = $A, y = $A}[9] }", tfs(tuple9)); }

  // Load common field 'x', ignoring mismatched fields y and z
  @Test public void test30() { run("{ pred -> .x (if pred @{x=2,y=3} @{x=3,z= \"abc\"}) }",
                                   "{ A -> nint8 }", tfs(TypeInt.NINT8)); }

  // Load some fields from an unknown struct: area of a rectangle.
  // Since no nil-check, correctly types as needing a not-nil input.
  @Test public void test31() { run("{ sq -> (* .x sq .y sq) }", // { sq -> sq.x * sq.y }
                                   "{ @{ x = int64, y = int64}[] -> int64 }", tfs(TypeInt.INT64)); }

  private static TypeMemPtr build_cycle( int alias, boolean nil, Type fld ) {
    // Build a cycle of length 2.
    BitsAlias aliases = BitsAlias.make0(alias);
    if( nil ) aliases = aliases.meet_nil();
    TypeMemPtr cycle_ptr0 = TypeMemPtr.make(aliases,TypeObj.XOBJ);
    TypeStruct cycle_str1 = TypeStruct.make2flds("n1",cycle_ptr0,"v1",fld);
    TypeMemPtr cycle_ptr1 = TypeMemPtr.make(aliases,cycle_str1);
    TypeStruct cycle_str2 = TypeStruct.make2flds("n1",cycle_ptr1,"v1",fld);
    TypeStruct cycle_strn = cycle_str2.approx(1,alias);
    TypeMemPtr cycle_ptrn = (TypeMemPtr)cycle_strn.at("n1");
    return cycle_ptrn;
  }


  // Recursive linked-list discovery, with no end clause.  Since this code has
  // no exit (its an infinite loop, endlessly reading from an infinite input
  // and writing an infinite output), gcp gets a cyclic approximation.
  @Test public void test32() {
    Root syn = HM9.hm("map = { fcn lst -> @{ n1 = (map fcn .n0 lst), v1 = (fcn .v0 lst) } }; map");
    if( HM.DO_HM )
      assertEquals("{ { A -> B } C:@{ n0 = $C, v0 = $A}[] -> D:@{ n1 = $D, v1 = $B}[9] }",syn._hmt.p());
    if( HM.DO_GCP )
      // Build a cycle of length 2, without nil.
      assertEquals(tfs(build_cycle(9,false,Type.SCALAR)),syn.flow_type());
  }

  // Recursive linked-list discovery, with nil.  Note that the output memory
  // has the output memory alias, but not the input memory alias (which must be
  // made before calling 'map').
  @Test public void test33() {
    Root syn = HM9.hm("map = { fcn lst -> (if lst @{ n1=(map fcn .n0 lst), v1=(fcn .v0 lst) } 0) }; map");
    if( HM.DO_HM )
      assertEquals("{ { A -> B } C:@{ n0 = $C, v0 = $A}[0] -> D:@{ n1 = $D, v1 = $B}[0,9] }",syn._hmt.p());
    if( HM.DO_GCP )
      // Build a cycle of length 2, with nil.
      assertEquals(tfs(build_cycle(9,true,Type.SCALAR)),syn.flow_type());
  }

  // Recursive linked-list discovery, with no end clause
  @Test public void test34() {
    Root syn = HM9.hm("map = { fcn lst -> (if lst @{ n1 = (map fcn .n0 lst), v1 = (fcn .v0 lst) } 0) }; (map dec @{n0 = 0, v0 = 5})");
    if( HM.DO_HM )
      assertEquals("A:@{ n1 = $A, v1 = int64}[0,9]",syn._hmt.p());
    if( HM.DO_GCP )
      assertEquals(build_cycle(9,true,TypeInt.con(4)),syn.flow_type());
  }

  // try the worse-case expo blow-up test case from SO
  @Test public void test35() {
    TypeFunPtr tfp = TypeFunPtr.make(15,3,Type.ANY,null);
    TypeMemPtr tmp0 = TypeMemPtr.make(8,TypeStruct.maket(tfp ,tfp ,tfp ));
    TypeMemPtr tmp1 = TypeMemPtr.make(8,TypeStruct.maket(tmp0,tmp0,tmp0));
    TypeMemPtr tmp2 = TypeMemPtr.make(8,TypeStruct.maket(tmp1,tmp1,tmp1));

    run("p0 = { x y z -> (triple x y z) };"+
        "p1 = (triple p0 p0 p0);"+
        "p2 = (triple p1 p1 p1);"+
        "p3 = (triple p2 p2 p2);"+
        "p3",
        "( ( ( { A B C -> ( $A, $B, $C)[8] }, { D E F -> ( $D, $E, $F)[8] }, { G H I -> ( $G, $H, $I)[8] })[8], ( { J K L -> ( $J, $K, $L)[8] }, { M N O -> ( $M, $N, $O)[8] }, { P Q R -> ( $P, $Q, $R)[8] })[8], ( { S T U -> ( $S, $T, $U)[8] }, { V21 V22 V23 -> ( $V21, $V22, $V23)[8] }, { V24 V25 V26 -> ( $V24, $V25, $V26)[8] })[8])[8], ( ( { V27 V28 V29 -> ( $V27, $V28, $V29)[8] }, { V30 V31 V32 -> ( $V30, $V31, $V32)[8] }, { V33 V34 V35 -> ( $V33, $V34, $V35)[8] })[8], ( { V36 V37 V38 -> ( $V36, $V37, $V38)[8] }, { V39 V40 V41 -> ( $V39, $V40, $V41)[8] }, { V42 V43 V44 -> ( $V42, $V43, $V44)[8] })[8], ( { V45 V46 V47 -> ( $V45, $V46, $V47)[8] }, { V48 V49 V50 -> ( $V48, $V49, $V50)[8] }, { V51 V52 V53 -> ( $V51, $V52, $V53)[8] })[8])[8], ( ( { V54 V55 V56 -> ( $V54, $V55, $V56)[8] }, { V57 V58 V59 -> ( $V57, $V58, $V59)[8] }, { V60 V61 V62 -> ( $V60, $V61, $V62)[8] })[8], ( { V63 V64 V65 -> ( $V63, $V64, $V65)[8] }, { V66 V67 V68 -> ( $V66, $V67, $V68)[8] }, { V69 V70 V71 -> ( $V69, $V70, $V71)[8] })[8], ( { V72 V73 V74 -> ( $V72, $V73, $V74)[8] }, { V75 V76 V77 -> ( $V75, $V76, $V77)[8] }, { V78 V79 V80 -> ( $V78, $V79, $V80)[8] })[8])[8])[8]",
        tmp2  );
  }

  // Need to see if a map call, inlined a few times, 'rolls up'.  Sometimes
  // rolls up, sometimes not; depends on worklist visitation order.
  @Test public void test36() {
    Root syn = HM9.hm("map = { lst -> (if lst @{ n1= arg= .n0 lst; (if arg @{ n1=(map .n0 arg), v1=(str .v0 arg)} 0), v1=(str .v0 lst) } 0) }; map");
    if( HM.DO_HM )
      assertEquals("{ A:@{ n0 = @{ n0 = $A, v0 = int64}[0], v0 = int64}[0] -> B:@{ n1 = @{ n1 = $B, v1 = *[4]str}[0,9], v1 = *[4]str}[0,10] }",syn._hmt.p());
    if( HM.DO_GCP ) {
      TypeStruct cycle_strX;
      if( true ) {
        // Unrolled, known to only produce results where either other nested
        // struct is from a different allocation site.
        TypeMemPtr cycle_ptr0 = TypeMemPtr.make(BitsAlias.FULL.make(0,10),TypeObj.XOBJ);
        TypeStruct cycle_str1 = TypeStruct.make2flds("n1",cycle_ptr0,"v1",TypeMemPtr.STRPTR);
        TypeMemPtr cycle_ptr1 = TypeMemPtr.make(BitsAlias.FULL.make(0, 9),cycle_str1);
        TypeStruct cycle_str2 = TypeStruct.make2flds("n1",cycle_ptr1,"v1",TypeMemPtr.STRPTR);
        TypeMemPtr cycle_ptr2 = TypeMemPtr.make(BitsAlias.FULL.make(0,10),cycle_str2);
        TypeStruct cycle_str3 = TypeStruct.make2flds("n1",cycle_ptr2,"v1",TypeMemPtr.STRPTR);
        cycle_strX = cycle_str3;
      } else {
        // Not unrolled, both structs are folded
        TypeMemPtr cycle_ptr0 = TypeMemPtr.make(BitsAlias.FULL.make(0,7, 8),TypeObj.XOBJ);
        TypeStruct cycle_str1 = TypeStruct.make2flds("n1",cycle_ptr0,"v1",TypeMemPtr.STRPTR);
        TypeMemPtr cycle_ptr1 = TypeMemPtr.make(BitsAlias.FULL.make(0,7, 8),cycle_str1);
        TypeStruct cycle_str2 = TypeStruct.make2flds("n1",cycle_ptr1,"v1",TypeMemPtr.STRPTR);
        cycle_strX = cycle_str2;
      }
      TypeStruct cycle_strn = cycle_strX.approx(1,9);
      TypeMemPtr cycle_ptrn = (TypeMemPtr)cycle_strn.at("n1");
      assertEquals(tfs(cycle_ptrn),syn.flow_type());
    }
  }

  @Test public void test37() { run("x = { y -> (x (y y))}; x",
                                   "{ A:{ $A -> $A } -> B }", tfs(Type.XSCALAR)); }

  // Example from SimpleSub requiring 'x' to be both a struct with field
  // 'v', and also a function type - specifically disallowed in 'aa'.
  @Test public void test38() { run("{ x -> y = ( x .v x ); 0}",
                                   "{ Cannot unify @{ v = A}[] and { A -> B } -> 0 }", tfs(Type.XNIL)); }

  // Really bad flow-type: function can be called from the REPL with any
  // argument type - and the worse case will be an error.
  @Test public void test39() {
    Root syn = HM9.hm("x = { z -> z}; (x { y -> .u y})");
    if( HM.DO_HM )
      assertEquals("{ @{ u = A}[] -> $A }",syn._hmt.p());
    if( HM.DO_GCP )
      assertEquals(tfs(Type.SCALAR), syn.flow_type());
  }

  // Example from SimpleSub requiring 'x' to be both:
  // - a recursive self-call function from "w = (x x)": $V66:{ $V66 -> V67 } AND
  // - a function which takes a struct with field 'u'
  // The first arg to x is two different kinds of functions, so fails unification.
  @Test public void test40() {
    Root syn = HM9.hm("x = w = (x x); { z -> z}; (x { y -> .u y})");
    if( HM.DO_HM )
      assertEquals("Cannot unify A:{ $A -> $A } and @{ u = A}[]",syn._hmt.p());
    if( HM.DO_GCP ) {
      if( HM.DO_HM ) {
        assertEquals(tfs(Type.SCALAR), syn.flow_type());
      } else {
        assertEquals(Type.SCALAR, syn.flow_type());
      }
    }
  }

  // Example from test15:
  //   map={lst fcn -> lst ? fcn lst.1};
  //   in_int=(0,2);"+       // List of ints
  //   in_str=(0,"abc");" +  // List of strings
  //   out_str = map(in_int,str:{int->str});"+        // Map over ints with int->str  conversion, returning a list of strings
  //   out_bool= map(in_str,{str -> str==\"abc\"});"+ // Map over strs with str->bool conversion, returning a list of bools
  //   (out_str,out_bool)",
  @Test public void test41() {
    Root syn = HM9.hm("map={lst fcn -> (fcn .y lst) }; "+
                     "in_int=@{ x=0 y=2}; " +
                     "in_str=@{ x=0 y=\"abc\"}; " +
                     "out_str = (map in_int str); " +
                     "out_bool= (map in_str { xstr -> (eq xstr \"def\")}); "+
                     "(pair out_str out_bool)");
    if( HM.DO_HM )
      assertEquals("( *[4]str, int1)[7]",syn._hmt.p());
    if( HM.DO_GCP )
      if( HM.DO_HM )
        assertEquals(TypeMemPtr.make(7,TypeStruct.maket(TypeMemPtr.STRPTR,TypeInt.BOOL)),syn.flow_type());
      else
        assertEquals(tuple2,syn.flow_type());
  }

  // CCP Can help HM
  @Test public void test42() {
    Root syn = HM9.hm("pred = 0; s1 = @{ x=\"abc\" }; s2 = @{ y=3.4 }; .y (if pred s1 s2)");
    if( HM.DO_HM ) {
      if( HM.DO_GCP )
        assertEquals("3.4000000953674316",syn._hmt.p());
      else
        assertEquals("Missing field y in @{ x = *[4]\"abc\"}[9]",syn._hmt.p());
    }
    if( HM.DO_GCP )
      assertEquals(TypeFlt.con(3.4f), syn.flow_type());
  }

  // The z-merge is ignored; the last s2 is a fresh (unmerged) copy.
  @Test public void test43() {
    Root syn = HM9.hm("pred = 0; s1 = @{ x=\"abc\" }; s2 = @{ y=3.4 }; z = (if pred s1 s2); .y s2");
    if( HM.DO_HM )
      assertEquals("3.4000000953674316",syn._hmt.p());
    if( HM.DO_GCP )
      assertEquals(TypeFlt.con(3.4f), syn.flow_type());
  }


  @Test public void test44() {
    Root syn = HM9.hm("fun = (if (isempty \"abc\") {x->x} {x->1.2}); (fun @{})");
    if( HM.DO_HM ) {
      if( HM.DO_GCP )
        assertEquals("1.2000000476837158",syn._hmt.p());
      else
        assertEquals("Cannot unify 1.2000000476837158 and )[9]",syn._hmt.p());
    }
    if( HM.DO_GCP )
      assertEquals(TypeFlt.con(1.2f), syn.flow_type());
  }


  // Requires a combo of HM and GCP to get the good answer
  @Test public void test45() {
    Root syn = HM9.hm(
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
                   ? "*[4]str"  // Both HM and GCP
                   : "Cannot unify *[4]\"abc\" and 3", // HM alone cannot do this one
                   syn._hmt.p());
    if( HM.DO_GCP )
      assertEquals(HM.DO_HM
                   ? TypeMemPtr.STRPTR // Both HM and GCP
                   : Type.NSCALR,      // GCP alone gets a very weak answer
                   syn.flow_type());
  }


  // Basic nil test
  @Test public void test46() { run(".x 0",
                                   "May be nil when loading field x", Type.XSCALAR); }

  // Basic nil test
  @Test public void test47() { run("{ pred -> .x (if pred @{x=3} 0)}",
                                   "{ A -> May be nil when loading field x }", tfs(TypeInt.con(3))); }

  // Basic uplifting after check
  @Test public void test48() { run("{ pred -> tmp=(if pred @{x=3} 0); (if tmp .x tmp 4) }",
                                   "{ A -> nint8 }", tfs(TypeInt.NINT8)); }


  // map is parametric in nil-ness
  @Test public void test49() {
    Root syn = HM9.hm("{ pred -> \n"+
                     "  map = { fun x -> (fun x) };\n" +
                     "  (pair (map {str0 ->          .x str0   }          @{x = 3}   )\n" +
                     "        (map {str1 -> (if str1 .x str1 4)} (if pred @{x = 5} 0))\n" +
                     "  )\n"+
                     "}");
    if( HM.DO_HM )
      assertEquals("{ A -> ( 3, nint8)[7] }",syn._hmt.p());
    if( HM.DO_GCP )
      if( HM.DO_HM ) tfs(TypeMemPtr.make(7,TypeStruct.maket(TypeInt.con(3), TypeInt.NINT8 )));
      else           tfs(TypeMemPtr.make(7,TypeStruct.maket(TypeInt.NINT8 , TypeInt.NINT8 )));
  }

  // map is parametric in nil-ness.  Verify still nil-checking.
  @Test public void test50() {
    Root syn = HM9.hm("{ pred -> \n"+
                     "  map = { fun x -> (fun x) };\n" +
                     "  (pair (map {str0 ->          .x str0   }          @{x = 3}   )\n" +
                     "        (map {str1 ->          .x str1   } (if pred @{x = 5} 0))\n" +
                     "  )\n"+
                     "}");
    if( HM.DO_HM )
      assertEquals("{ A -> May be nil when loading field x }",syn._hmt.p());
    if( HM.DO_GCP )
      if( HM.DO_HM ) tfs(TypeMemPtr.make(7,TypeStruct.maket(TypeInt.con(3), TypeInt.NINT8 )));
      else           tfs(TypeMemPtr.make(7,TypeStruct.maket(TypeInt.NINT8 , TypeInt.NINT8 )));
  }

}
