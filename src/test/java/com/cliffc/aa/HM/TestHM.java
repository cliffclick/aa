package com.cliffc.aa.HM;

import com.cliffc.aa.HM.HM.*;
import com.cliffc.aa.type.*;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class TestHM {

  @Before public void reset() { HM.reset(); }

  private void run( String prog, String rez_hm ) { run(prog,rez_hm,null); }
  private void run( String prog, String rez_hm, Type rez_gcp ) {
    Root syn = HM.hm(prog);
    if( HM.DO_HM )
      assertEquals(rez_hm,syn._t.p());
    if( HM.DO_GCP ) {
      assertEquals(rez_gcp,syn.flow_type());

    }
  }
  // Simple no-arg signature returning the type
  private static TypeFunSig tfs(Type ret) {
    return TypeFunSig.make(TypeTuple.make_ret(ret),TypeTuple.make_args());
  }

  private static final TypeMemPtr tuple2  = TypeMemPtr.make(7,TypeStruct.make_tuple(Type.ANY,Type.SCALAR,   Type.SCALAR   ));
  private static final TypeMemPtr tuplen2 = TypeMemPtr.make(7,TypeStruct.make_tuple(Type.ANY,Type.NSCALR,   Type.NSCALR   ));
  private static final TypeMemPtr tuple55 = TypeMemPtr.make(7,TypeStruct.make_tuple(Type.ANY,TypeInt.con(5),TypeInt.con(5)));
  private static final TypeFunSig ret_tuple2 = tfs(tuple2);
  private static final String[] XY = new String[]{"x","y"};
  private static final TypeMemPtr tuple9  = TypeMemPtr.make(9,TypeStruct.make(XY,Types.ts(Type.SCALAR,Type.SCALAR)));


  @Test(expected = RuntimeException.class)
  public void test00() { run( "fred",null,null); }

  @Test public void test01() { run( "3" ,
                                    "3", TypeInt.con(3));  }

  @Test public void test02() { run( "(pair1 3)" ,
                                    "{ A -> ( 3, $A)[7] }", tfs(TypeMemPtr.make(7,TypeStruct.make_tuple(TypeInt.con(3),Type.ANY)))); }

  @Test public void test03() { run( "{ z -> (pair (z 3) (z \"abc\")) }" ,
                                    "{ { all -> A } -> ( $A, $A)[7] }", ret_tuple2); }

  @Test public void test04() { run( "fact = { n -> (if (?0 n) 1 (* n (fact (dec n))))}; fact",
                                    "{ int64 -> int64 }", tfs(TypeInt.INT64) ); }

  // Because {y->y} is passed in, all 'y' types must agree.
  // This unifies 3 and "abc" which results in 'all'
  @Test public void test05() { run( "({ x -> (pair (x 3) (x \"abc\")) } {y->y})",
                                    "( all, all)[7]", tuplen2 ); }

  @Test public void test06() { run( "id={x->x}; (pair (id 3) (id \"abc\"))",
                                    "( 3, \"abc\")[7]", tuplen2  ); }

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
                                   "( *[4]str, (divmod flt64 flt64))[7]", tuple2); }

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
  //                               {b -> pair[b,pair[3,b]]}) } in
  // map takes a function and an element (collection?) and applies it (applies to collection?)
  //   let map = { fun x -> (fun x) }
  //          in { q -> ((map (fcn q)) 5) }
  // Should return { q -> q ? [5,5] : [5,[3,5]] }
  // Ultimately, unifies "a" with "pair[3,a]" which throws recursive unification.
  @Test public void test18() { run("fcn = {p -> (if p {a -> (pair a a)} {b -> (pair b (pair 3 b))})};"+
                                   "map = { fun x -> (fun x)};"+
                                   "{ q -> (map (fcn q) 5)}",
                                   "{ A -> ( B:\"Cannot unify A:( 3, $A)[7] and 5\", $B)[7] }",
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
                                   "{ { nint8 -> A } -> ( $A, $A)[7] }", ret_tuple2); }

  // Basic structure test
  @Test public void test25() { run("@{x=2, y=3}",
                                   "@{ x = 2, y = 3}[9]",
                                   TypeMemPtr.make(9,TypeStruct.make(XY,Types.ts(TypeInt.con(2),TypeInt.con(3))))
                                   ); }

  // Basic field test
  @Test public void test26() { run(".x @{x =2, y =3}",
                                   "2", TypeInt.con(2)); }

  // Basic field test
  @Test public void test27() { run(".x 5",
                                   "\"Cannot unify @{ x = A}[] and 5\"", TypeMemPtr.make(BitsAlias.STRBITS,TypeStr.con("No field x in 5"))); }

  // Basic field test.
  @Test public void test28() { run(".x @{ y =3}",
                                   "\"Missing field x in @{ y = 3}:[9]\"",
                                   TypeMemPtr.make(BitsAlias.STRBITS,TypeStr.con("Missing field x in @{y==3}"))); }

  @Test public void test29() { run("{ g -> @{x=g, y=g}}",
                                   "{ A -> @{ x = $A, y = $A}[9] }", tfs(tuple9)); }

  // Load common field 'x', ignoring mismatched fields y and z
  @Test public void test30() { run("{ pred -> .x (if pred @{x=2,y=3} @{x=3,z= \"abc\"}) }",
                                   "{ A -> nint8 }", tfs(TypeInt.NINT8)); }

  // Load some fields from an unknown struct: area of a square.
  // Since no nil-check, correctly types as needing a not-nil input.
  @Test public void test31() { run("{ sq -> (* .x sq .y sq) }", // { sq -> sq.x * sq.y }
                                   "{ @{ y = int64, x = int64}[] -> int64 }", tfs(TypeInt.INT64)); }

  private static TypeMemPtr build_cycle( int alias, boolean nil, Type fld ) {
    // Build a cycle of length 2.
    String[] N1V1 = new String[]{"n1","v1"};
    BitsAlias aliases = BitsAlias.make0(alias);
    if( nil ) aliases = aliases.meet_nil();
    TypeMemPtr cycle_ptr0 = TypeMemPtr.make(aliases,TypeObj.XOBJ);
    TypeStruct cycle_str1 = TypeStruct.make(N1V1,Types.ts(cycle_ptr0,fld));
    TypeMemPtr cycle_ptr1 = TypeMemPtr.make(aliases,cycle_str1);
    TypeStruct cycle_str2 = TypeStruct.make(N1V1,Types.ts(cycle_ptr1,fld));
    TypeStruct cycle_strn = cycle_str2.approx(1,alias);
    TypeMemPtr cycle_ptrn = (TypeMemPtr)cycle_strn._ts[0];
    return cycle_ptrn;
  }
  
  
  // Recursive linked-list discovery, with no end clause.  Since this code has
  // no exit (its an infinite loop, endlessly reading from an infinite input
  // and writing an infinite output), gcp gets a cyclic approximation.
  @Test public void test32() {
    Root syn = HM.hm("map = { fcn lst -> @{ n1 = (map fcn .n0 lst), v1 = (fcn .v0 lst) } }; map");
    if( HM.DO_HM )
      assertEquals("{ { A -> B } C:@{ v0 = $A, n0 = $C}[] -> D:@{ n1 = $D, v1 = $B}[9] }",syn._t.p());
    if( HM.DO_GCP )
      // Build a cycle of length 2, without nil.
      assertEquals(tfs(build_cycle(9,false,Type.SCALAR)),syn.flow_type());
  }

  // Recursive linked-list discovery, with nil.  Note that the output memory
  // has the output memory alias, but not the input memory alias (which must be
  // made before calling 'map').
  @Test public void test33() {
    Root syn = HM.hm("map = { fcn lst -> (if lst @{ n1=(map fcn .n0 lst), v1=(fcn .v0 lst) } 0) }; map");
    if( HM.DO_HM )
      assertEquals("{ { A -> B } C:@{ v0 = $A, n0 = $C}[0] -> D:@{ n1 = $D, v1 = $B}[0,9] }",syn._t.p());
    if( HM.DO_GCP )
      // Build a cycle of length 2, with nil.
      assertEquals(tfs(build_cycle(9,true,Type.SCALAR)),syn.flow_type());
  }

  // Recursive linked-list discovery, with no end clause
  @Test public void test34() {
    Root syn = HM.hm("map = { fcn lst -> (if lst @{ n1 = (map fcn .n0 lst), v1 = (fcn .v0 lst) } 0) }; (map dec @{n0 = 0, v0 = 5})");
    if( HM.DO_HM )
      assertEquals("A:@{ n1 = $A, v1 = int64}[0,9]",syn._t.p());
    if( HM.DO_GCP )
      assertEquals(build_cycle(9,true,TypeInt.con(4)),syn.flow_type());
  }

  // try the worse-case expo blow-up test case from SO
  @Test public void test35() {
    TypeFunPtr tfp = TypeFunPtr.make(12,3,Type.ANY);
    TypeMemPtr tmp0 = TypeMemPtr.make(8,TypeStruct.make_tuple(Type.ANY,tfp ,tfp ,tfp ));
    TypeMemPtr tmp1 = TypeMemPtr.make(8,TypeStruct.make_tuple(Type.ANY,tmp0,tmp0,tmp0));
    TypeMemPtr tmp2 = TypeMemPtr.make(8,TypeStruct.make_tuple(Type.ANY,tmp1,tmp1,tmp1));
    
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
    Root syn = HM.hm("map = { lst -> (if lst @{ n1= arg= .n0 lst; (if arg @{ n1=(map .n0 arg), v1=(str .v0 arg)} 0), v1=(str .v0 lst) } 0) }; map");
    if( HM.DO_HM )
      assertEquals("{ A:@{ v0 = int64, n0 = @{ n0 = $A, v0 = int64}[0]}[0] -> B:@{ n1 = @{ n1 = $B, v1 = *[4]str}[0,9], v1 = *[4]str}[0,10] }",syn._t.p());
    if( HM.DO_GCP ) {
      String[] N1V1 = new String[]{"n1","v1"};
      TypeMemPtr cycle_ptr0 = TypeMemPtr.make(BitsAlias.FULL.make(0,10),TypeObj.XOBJ);
      TypeStruct cycle_str1 = TypeStruct.make(N1V1,Types.ts(cycle_ptr0,TypeMemPtr.STRPTR));
      TypeMemPtr cycle_ptr1 = TypeMemPtr.make(BitsAlias.FULL.make(0, 9),cycle_str1);
      TypeStruct cycle_str2 = TypeStruct.make(N1V1,Types.ts(cycle_ptr1,TypeMemPtr.STRPTR));
      TypeMemPtr cycle_ptr2 = TypeMemPtr.make(BitsAlias.FULL.make(0,10),cycle_str2);
      TypeStruct cycle_str3 = TypeStruct.make(N1V1,Types.ts(cycle_ptr2,TypeMemPtr.STRPTR));
      TypeStruct cycle_strn = cycle_str3.approx(1,9);
      TypeMemPtr cycle_ptrn = (TypeMemPtr)cycle_strn._ts[0];
      assertEquals(tfs(cycle_ptrn),syn.flow_type());
    }
  }

  @Test public void test37() { run("x = { y -> (x (y y))}; x",
                                   "{ A:{ $A -> $A } -> B }", tfs(Type.XSCALAR)); }

  // Example from SimpleSub requiring 'x' to be both a struct with field
  // 'v', and also a function type - specifically disallowed in 'aa'.
  @Test public void test38() { run("{ x -> y = ( x .v x ); 0}",
                                   "{ \"Cannot unify @{ v = A}[] and { A -> B }\" -> 0 }", tfs(Type.XNIL)); }

  @Test public void test39() { run("x = { z -> z}; (x { y -> .u y})",
                                   "{ @{ u = A}[] -> $A }",null); }

  // Example from SimpleSub requiring 'x' to be both:
  // - a recursive self-call function from "w = (x x)": $V66:{ $V66 -> V67 } AND
  // - a function which takes a struct with field 'u'
  // The first arg to x is two different kinds of functions, so fails unification.
  @Test public void test40() { run("x = w = (x x); { z -> z}; (x { y -> .u y})",
                                   "\"Cannot unify A:{ $A -> B } and @{ u = A}[]\""); }

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
                                   "( *[4]str, int1)[7]"); }


}

/**

noinline_map: { lst:@{y=A} fcn:{A->B} -> B }
in_int : @{ x=Nil, y=int}
out_str: @{ x=Nil, y=str}
pi     : @{ pi=flt }
out_bol: int1/bool
(pair str bool)

Unify_Lift:
  - assigns a type to a tvar, based on tvar?  Structure-for-structure, plus meet of Bases.
  - applies the join to flow types in everywhere tvar appears
  - follow top-level types/tvars
  - No-esc-out uses pre-call memory
  -- Concept: lift flow memory from non-memory TVars.
  -- STUCK HERE...




Example w/Store

mem[#1s:@{y=Nil}]
  Store.y mem #1s 5.2     adr<->@{y=Flt}  val=Flt
mem[#1s:@{y=flt }]

Now unify-lift: mem[#1s].y join with Flt.


Example w/Call

fcn = { mem adr val -> mem[adr].y = val }
fcn: { @{y=A} A -> A }   // H-M tvar type

mem[#1s:@{y=Nil}]   // Leaf:Nil can unify with anything
  Call mem #1s  5.2  fcn
    - val: flow makes it a Scalar
    - lst: flow makes it a TMP[14,16,...]
    - mem: flow makes it mem[14,16,...].y = Scalar
    - fresh { @{y=A} A -> A } with { lst 5.2 -> rez }
    - lst becomes @{y=A}
    - A becomes 5.2
    - unify Nil and 5.2 --> Flt



Conflict on fcns:
- Flow tracks set of valid call fidxs... until i start calling on things that
  have merged, required H-M, and the merge loses the fidxs.

- H-M can play top-down w/Opto/GCP; get H-M types.  So can track fcns thru args
  and calls.  Unify_lift can recover some flow-fcn-fidxs, which can limit flow
  targets.
- Limit flow targets can limit H-M unification requirements:
  fcn = pred ? {A->B} : {C->D}
  (fcn foo)   // Implies foo:A:C all unified
  // Suppose pred=TRUE, so {C->D} never happens, so foo[{A->B}] only
  // Then foo:A




Add combo GCP & HM ?

-- really fighting memory state here
-- did want mem to be indexed by alias#s... but this is variant over GCP time.
-- Similar to the unify of pred case:

-- unify (if pred x y):
  -- pred==0 : y
  -- pred==1 : x
  -- pred==TOP : neither, skip
  -- pred==BOT : x.unify(y)

-- unify of memory loads:  (load.fld mem adr)
  -- adr is an ever-widening set of alais#s
  -- mem[forAll aliases].fld unify Load
  -- New alias in flow types: unify it also

-- Similar to unify of Stores

-- Still need a way to lift flows from unify;
  -- Apply result type can be lifted to join of matching TVar inputs?...
     (fcn arg1 arg2):rez
     fcn is flow-typed as (TFP int:A scalar:B -> scalar:B)
     arg1 is :>int, or else flow error
     arg2 is e.g. str
     rez is scalar, but join with arg2:str.
  -- (fcn arg1 arg2):rez
  -- fcn:{ int:A {xxx -> yyy}:{B -> C} -> C}
     arg1 is int
     -- arg2 is scalar - no lift
     -- arg2 is {bbb -> ccc} - rez.join(ccc)


So... no unify during iter/lift.  Start all unifies at leafs at GCP.
Unify "like normal"


Some decisions:
- HM type structures carry a flowtype at every point, or not.
- - If not, then when the HM type alters at a point, need to walk both HM and
    flow types and "align" them: expect flow types to be sharper than HM, except for Applys, where HM's join.
- - If so, then at each incremental HM union: leaf-vs-non-leaf the leaf type needs to meet with the
    non-leaf-HM's flow types incrementally.
- - or do not ever walk both?  Just JOIN at Applys

Bare-HM-Leafs type as ANY (not ALL), and MEET with the base types they unify
with.  When the Leaf unifies with something with structure, then we have to
decide what to do (meet the structure dataflow and leaf dataflow; walk the
structure and matching dataflow, just taking leaves, etc)


 */
