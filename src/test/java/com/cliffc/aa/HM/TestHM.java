package com.cliffc.aa.HM;

import com.cliffc.aa.HM.HM.*;
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

  private static final TypeMemPtr tuple2  = TypeMemPtr.make(7,TypeStruct.make_tuple(Type.ANY,Type.SCALAR,   Type.SCALAR   ));
  private static final TypeMemPtr tuplen2 = TypeMemPtr.make(7,TypeStruct.make_tuple(Type.ANY,Type.NSCALR,   Type.NSCALR   ));
  private static final TypeMemPtr tuple55 = TypeMemPtr.make(7,TypeStruct.make_tuple(Type.ANY,TypeInt.con(5),TypeInt.con(5)));
  private static final TypeFunSig ret_tuple2 = tfs(tuple2);
  private static final String[] XY = new String[]{"^","x","y"};
  private static final String[] N1V1 = new String[]{"^","n1","v1"};
  private static final TypeMemPtr tuple9  = TypeMemPtr.make(7,TypeStruct.make(XY,Types.ts(Type.ANY,Type.SCALAR,Type.SCALAR)));

  @Test(expected = RuntimeException.class)
  public void test00() { run( "fred",null,null); }

  @Test public void test01() { run( "3" ,
                                    "3", TypeInt.con(3));  }

  @Test public void test02() { run( "(pair1 3)" ,
                                    "{ A -> ( 3, $A)[7] }", tfs(TypeMemPtr.make(7,TypeStruct.make_tuple(Type.ANY,TypeInt.con(3),Type.SCALAR)))); }

  @Test public void test03() { run( "{ z -> (pair (z 3) (z \"abc\")) }" ,
                                    "{ { nScalar -> A } -> ( $A, $A)[7] }", tfs(tuple2)); }

  @Test public void test04() { run( "fact = { n -> (if (?0 n) 1 (* n (fact (dec n))))}; fact",
                                    "{ int64 -> int64 }", tfs(TypeInt.INT64) ); }

  // Because {y->y} is passed in, all 'y' types must agree.
  // This unifies 3 and "abc" which results in 'all'
  @Test public void test05() {
    Root syn = HM.hm("({ x -> (pair (x 3) (x \"abc\")) } {y->y})");
    if( HM.DO_HM )
      assertEquals("( nScalar, nScalar)[7]",syn._hmt.p());
    if( HM.DO_GCP )
      if( HM.DO_HM )
        assertEquals(tuplen2,syn.flow_type());
      else
        assertEquals(tuplen2,syn.flow_type());
  }

  @Test public void test06() {
    Root syn = HM.hm("id={x->x}; (pair (id 3) (id \"abc\"))");
    if( HM.DO_HM ) // HM is sharper here than in test05, because id is generalized per each use site
      assertEquals("( 3, *[4]\"abc\")[7]",syn._hmt.p());
    if( HM.DO_GCP )
      if( HM.DO_HM )
        assertEquals(TypeMemPtr.make(7,TypeStruct.make_tuple(Type.ANY,TypeInt.NINT64,TypeMemPtr.STRPTR)),syn.flow_type());
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
  @Test public void test14() { run("map = { fun -> { x -> (fun x)}};"+
                                   "(pair ((map str) 5) ((map factor) 2.3))",
                                   "( *[4]str, flt64)[7]", tuple2); }

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
  @Test public void test18() { run("fcn = {p -> (if p {a -> (pair a a)} {b -> (pair b (pair 3 b))})};"+
                                   "map = { fun x -> (fun x)};"+
                                   "{ q -> (map (fcn q) 5)}",
                                   "{ A -> ( B:Cannot unify A:( 3, $A)[7] and 5, $B)[7] }",
                                   tfs(TypeMemPtr.make(7,TypeStruct.make_tuple(Type.ANY,TypeInt.con(5),Type.NSCALR)))
                                   ); }

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
  @Test public void test20() { run("cons ={x y-> {cadr -> (cadr x y)}};"+
                                   "cdr ={mycons -> (mycons { p q -> q})};"+
                                   "map ={fun parg -> (fun (cdr parg))};"+
                                   "(pair (map str (cons 0 5)) (map isempty (cons 0 \"abc\")))",
                                   "( *[4]str, int1)[7]", tuple2); }

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
                                   "@{ x = 2, y = 3}[7]",
                                   TypeMemPtr.make(7,TypeStruct.make(XY,Types.ts(Type.ANY,TypeInt.con(2),TypeInt.con(3))))
                                   ); }

  // Basic field test
  @Test public void test26() { run(".x @{x =2, y =3}",
                                   "2", TypeInt.con(2)); }

  // Basic field test
  @Test public void test27() { run(".x 5",
                                   "Missing field x in 5", TypeMemPtr.make(BitsAlias.STRBITS0,TypeStr.con("Missing field x"))); }

  // Basic field test.
  @Test public void test28() { run(".x @{ y =3}",
                                   "Missing field x",
                                   TypeMemPtr.make(BitsAlias.STRBITS0,TypeStr.con("Missing field x"))); }

  @Test public void test29() { run("{ g -> @{x=g, y=g}}",
                                   "{ A -> @{ x = $A, y = $A}[7] }", tfs(tuple9)); }

  // Load common field 'x', ignoring mismatched fields y and z
  @Test public void test30() { run("{ pred -> .x (if pred @{x=2,y=3} @{x=3,z= \"abc\"}) }",
                                   "{ A -> nint8 }", tfs(TypeInt.NINT8)); }

  // Load some fields from an unknown struct: area of a rectangle.
  // Since no nil-check, correctly types as needing a not-nil input.
  @Test public void test31() { run("{ sq -> (* .x sq .y sq) }", // { sq -> sq.x * sq.y }
                                   "{ @{ y = int64, x = int64}[] -> int64 }", tfs(TypeInt.INT64)); }

  private static TypeMemPtr build_cycle( int alias, boolean nil, Type fld ) {
    // Build a cycle of length 2.
    BitsAlias aliases = BitsAlias.make0(alias);
    if( nil ) aliases = aliases.meet_nil();
    TypeMemPtr cycle_ptr0 = TypeMemPtr.make(aliases,TypeObj.XOBJ);
    TypeStruct cycle_str1 = TypeStruct.make(N1V1,Types.ts(Type.ANY,cycle_ptr0,fld));
    TypeMemPtr cycle_ptr1 = TypeMemPtr.make(aliases,cycle_str1);
    TypeStruct cycle_str2 = TypeStruct.make(N1V1,Types.ts(Type.ANY,cycle_ptr1,fld));
    TypeStruct cycle_strn = cycle_str2.approx(1,alias);
    TypeMemPtr cycle_ptrn = (TypeMemPtr)cycle_strn._ts[1];
    return cycle_ptrn;
  }


  // Recursive linked-list discovery, with no end clause.  Since this code has
  // no exit (its an infinite loop, endlessly reading from an infinite input
  // and writing an infinite output), gcp gets a cyclic approximation.
  @Test public void test32() {
    Root syn = HM.hm("map = { fcn lst -> @{ n1 = (map fcn .n0 lst), v1 = (fcn .v0 lst) } }; map");
    if( HM.DO_HM )
      assertEquals("{ { A -> B } C:@{ v0 = $A, n0 = $C}[] -> D:@{ n1 = $D, v1 = $B}[7] }",syn._hmt.p());
    if( HM.DO_GCP )
      // Build a cycle of length 2, without nil.
      assertEquals(tfs(build_cycle(7,false,Type.SCALAR)),syn.flow_type());
  }

  // Recursive linked-list discovery, with nil.  Note that the output memory
  // has the output memory alias, but not the input memory alias (which must be
  // made before calling 'map').
  @Test public void test33() {
    Root syn = HM.hm("map = { fcn lst -> (if lst @{ n1=(map fcn .n0 lst), v1=(fcn .v0 lst) } 0) }; map");
    if( HM.DO_HM )
      assertEquals("{ { A -> B } C:@{ v0 = $A, n0 = $C}[0] -> D:@{ n1 = $D, v1 = $B}[0,7] }",syn._hmt.p());
    if( HM.DO_GCP )
      // Build a cycle of length 2, with nil.
      assertEquals(tfs(build_cycle(7,true,Type.SCALAR)),syn.flow_type());
  }

  // Recursive linked-list discovery, with no end clause
  @Test public void test34() {
    Root syn = HM.hm("map = { fcn lst -> (if lst @{ n1 = (map fcn .n0 lst), v1 = (fcn .v0 lst) } 0) }; (map dec @{n0 = 0, v0 = 5})");
    if( HM.DO_HM )
      assertEquals("A:@{ n1 = $A, v1 = int64}[0,7]",syn._hmt.p());
    if( HM.DO_GCP )
      assertEquals(build_cycle(7,true,TypeInt.con(4)),syn.flow_type());
  }

  // try the worse-case expo blow-up test case from SO
  @Test public void test35() {
    TypeFunPtr tfp = TypeFunPtr.make(3,3,Type.ANY);
    TypeMemPtr tmp0 = TypeMemPtr.make(7,TypeStruct.make_tuple(Type.ANY,tfp ,tfp ,tfp ));
    TypeMemPtr tmp1 = TypeMemPtr.make(7,TypeStruct.make_tuple(Type.ANY,tmp0,tmp0,tmp0));
    TypeMemPtr tmp2 = TypeMemPtr.make(7,TypeStruct.make_tuple(Type.ANY,tmp1,tmp1,tmp1));

    run("p0 = { x y z -> (triple x y z) };"+
        "p1 = (triple p0 p0 p0);"+
        "p2 = (triple p1 p1 p1);"+
        "p3 = (triple p2 p2 p2);"+
        "p3",
        "( A:( B:( C:{ D E F -> ( $D, $E, $F)[7] }, $G, $H)[7], $I, $J)[7], $K, $L)[7]",
        tmp2  );
  }

  // Need to see if a map call, inlined a few times, 'rolls up'.  Sometimes
  // rolls up, sometimes not; depends on worklist visitation order.
  @Test public void test36() {
    Root syn = HM.hm("map = { lst -> (if lst @{ n1= arg= .n0 lst; (if arg @{ n1=(map .n0 arg), v1=(str .v0 arg)} 0), v1=(str .v0 lst) } 0) }; map");
    if( HM.DO_HM )
      assertEquals("{ A:@{ v0 = int64, n0 = @{ v0 = int64, n0 = $A}[0]}[0] -> B:@{ n1 = @{ n1 = $B, v1 = *[4]str}[0,7], v1 = *[4]str}[0,8] }",syn._hmt.p());
    if( HM.DO_GCP ) {
      TypeStruct cycle_strX;
      if( true ) {
        // Unrolled, known to only produce results where either other nested
        // struct is from a different allocation site.
        TypeMemPtr cycle_ptr0 = TypeMemPtr.make(BitsAlias.FULL.make(0, 8),TypeObj.XOBJ);
        TypeStruct cycle_str1 = TypeStruct.make(N1V1,Types.ts(Type.ANY,cycle_ptr0,TypeMemPtr.STRPTR));
        TypeMemPtr cycle_ptr1 = TypeMemPtr.make(BitsAlias.FULL.make(0, 7),cycle_str1);
        TypeStruct cycle_str2 = TypeStruct.make(N1V1,Types.ts(Type.ANY,cycle_ptr1,TypeMemPtr.STRPTR));
        TypeMemPtr cycle_ptr2 = TypeMemPtr.make(BitsAlias.FULL.make(0, 8),cycle_str2);
        TypeStruct cycle_str3 = TypeStruct.make(N1V1,Types.ts(Type.ANY,cycle_ptr2,TypeMemPtr.STRPTR));
        cycle_strX = cycle_str3;
      } else {
        // Not unrolled, both structs are folded
        TypeMemPtr cycle_ptr0 = TypeMemPtr.make(BitsAlias.FULL.make(0,7, 8),TypeObj.XOBJ);
        TypeStruct cycle_str1 = TypeStruct.make(N1V1,Types.ts(Type.ANY,cycle_ptr0,TypeMemPtr.STRPTR));
        TypeMemPtr cycle_ptr1 = TypeMemPtr.make(BitsAlias.FULL.make(0,7, 8),cycle_str1);
        TypeStruct cycle_str2 = TypeStruct.make(N1V1,Types.ts(Type.ANY,cycle_ptr1,TypeMemPtr.STRPTR));
        cycle_strX = cycle_str2;
      }
      TypeStruct cycle_strn = cycle_strX.approx(1,7);
      TypeMemPtr cycle_ptrn = (TypeMemPtr)cycle_strn._ts[1];
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
    Root syn = HM.hm("x = { z -> z}; (x { y -> .u y})");
    if( HM.DO_HM )
      assertEquals("{ @{ u = A}[] -> $A }",syn._hmt.p());
    if( HM.DO_GCP ) {
      if( HM.DO_HM ) {
        assertEquals(tfs(Type.SCALAR), syn.flow_type());
      } else {
        assertEquals(tfs(TypeMemPtr.make(BitsAlias.STRBITS0,TypeStr.con("Missing field u"))), syn.flow_type());
      }
    }
  }

  // Example from SimpleSub requiring 'x' to be both:
  // - a recursive self-call function from "w = (x x)": $V66:{ $V66 -> V67 } AND
  // - a function which takes a struct with field 'u'
  // The first arg to x is two different kinds of functions, so fails unification.
  @Test public void test40() {
    Root syn = HM.hm("x = w = (x x); { z -> z}; (x { y -> .u y})");
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
  @Test public void test41() { run("map={lst fcn -> (fcn .y lst) }; "+
                                   "in_int=@{ x=0 y=2}; " +
                                   "in_str=@{ x=0 y=\"abc\"}; " +
                                   "out_str = (map in_int str); " +
                                   "out_bool= (map in_str { xstr -> (eq xstr \"def\")}); "+
                                   "(pair out_str out_bool)"  ,
                                   "( *[4]str, int1)[7]", tuple2); }


  // CCP Can help HM
  @Test public void test42() {
    Root syn = HM.hm("pred = 0; s1 = @{ x=\"abc\" }; s2 = @{ y=3.4 }; .y (if pred s1 s2)");
    if( HM.DO_HM ) {
      if( HM.DO_GCP )
        assertEquals("3.4000000953674316",syn._hmt.p());
      else
        assertEquals("Missing field y in @{ x = *[4]\"abc\"}[7]",syn._hmt.p());
    }
    if( HM.DO_GCP )
      assertEquals(TypeFlt.con(3.4f), syn.flow_type());
  }

  // The z-merge is ignored; the last s2 is a fresh (unmerged) copy.
  @Test public void test43() {
    Root syn = HM.hm("pred = 0; s1 = @{ x=\"abc\" }; s2 = @{ y=3.4 }; z = (if pred s1 s2); .y s2");
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
        assertEquals("Cannot unify 1.2000000476837158 and )[7]",syn._hmt.p());
    }
    if( HM.DO_GCP )
      assertEquals(TypeFlt.con(1.2f), syn.flow_type());
  }

}
