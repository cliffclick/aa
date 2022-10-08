package com.cliffc.aa.HM;

import com.cliffc.aa.HM.HM.Root;
import com.cliffc.aa.type.*;
import org.junit.BeforeClass;
import org.junit.FixMethodOrder;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runners.MethodSorters;

import static org.junit.Assert.assertEquals;

/*
  Theory: can move the update_root_args back into root._val, and remove pass#2
 */

@FixMethodOrder(MethodSorters.NAME_ASCENDING)
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
    a_basic_00();
  }

  private void _run0s( String prog, String rez_hm, String frez_gcp, int rseed, String esc_ptrs, String esc_funs  ) {
    HM.reset();
    Root syn = HM.hm(prog, rseed, rez_hm!=null, frez_gcp!=null );
    if( frez_gcp!=null )  assertEquals(Type.valueOf(frez_gcp),syn.flow_type());
    if(  rez_hm !=null )  assertEquals(stripIndent(rez_hm),stripIndent(syn._hmt.p()));
    if( rez_hm!=null && frez_gcp!=null && !rez_hm.contains("Cannot") ) {
      // Track expected Root escapes
      String esc_ptrs2 = "*"+esc_ptrs+"()";
      String esc_funs2 =     esc_funs+"{any,3->Scalar}";
      BitsAlias aliases = esc_ptrs==null ? BitsAlias.EMPTY : ((TypeMemPtr)Type.valueOf(esc_ptrs2))._aliases;
      BitsFun   fidxs   = esc_funs==null ? BitsFun  .EMPTY : ((TypeFunPtr)Type.valueOf(esc_funs2)).fidxs() ;
      aliases = aliases.meet(TypeMemPtr.STRPTR._aliases); // Always string alias
      for( HM.EXTLambda elam : Root.EXTS )  if( elam!=null )  fidxs = fidxs.set(elam._fidx); // Always the default escapes
      assertEquals(aliases,Root.ext_aliases());
      assertEquals(fidxs  ,Root.ext_fidxs  ());
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



  
  @Test public void a_basic_00() { run( "3", "3", "3");  }

  @Test public void a_basic_01() {
    rune( "{ x -> (pair 3 x) }" ,
          "{ A -> *( 3, A) }",
          "[23]{any,3 -> *[7](_, 3,Scalar)}",
          "[7]", "[23]" );
  }
  @Test public void a_basic_02() {
    rune( "{ z -> (pair (z 0) (z \"abc\")) }" ,
          "{ { *str:(97)? -> A } -> *( A, A) }",
          "[23]{any,3 ->*[7](_, Scalar, Scalar) }",
          "[7]", "[23,24]" );
  }
  // Because {y->y} is passed in, all 'y' types must agree.
  // This unifies 3 and 5 which results in 'nint8'
  @Test public void a_basic_03() {
    rune("({ id -> (pair (id 3) (id 5) ) } {x->x})",
         "*( nint8, nint8)",   // HMT result type, using both GCP + HMT
         "*( nint8, nint8)",   // HMT result type, HMT alone
         "*[7](_, 3, 5)",  // GCP result type, using both GCP + HMT
         "*[7](_, nint8, nint8)", // GCP result type, GCP alone
          "[7]",null);
  }
  @Test public void a_basic_04() {
    rune("id={x->x}; (pair (id 3) (id \"abc\"))",
         // HM is sharper here than in test05, because id is generalized per each use site
         "*( 3, *str:(97))",
         "*( 3, *str:(97))",
         // GCP with HM
         "*[7](_, 3, *[4]str:(97))",
         // GCP is weaker without HM, reports error tuple
         "*[7](_, nScalar, nScalar)",
         "[4,7]", null );
  }
  // example that demonstrates generic and non-generic variables:
  @Test public void a_basic_05() {
    rune( "{ g -> f = { ignore -> g }; (pair (f 3) (f \"abc\"))}",
          "{ A -> *( A, A) }",
          "[25]{any,3 ->*[7](_, Scalar, Scalar) }",
          "[4,7]","[25]");
  }
  @Test public void a_basic_06() { run("(i* 2 3)","int64","6");  }


  @Test(expected = RuntimeException.class)
  public void a_basic_err_00() { run( "fred","","all"); }


  @Test public void b_recursive_00() {
    rune( "fact = { n -> (if (eq0 n) 1 (i* n (fact (dec n))))}; fact",
          "{ int64 -> int64 }",
          "[27]{any,3 -> int64 }",
          null, "[27]" );
  }
  // recursive unification; normal H-M fails here.
  @Test public void b_recursive_01() {
    rune( "{ f -> (f f) }",
          // We can argue the pretty-print should print:
          // "  A:{ A -> B }"
          "{ A:{ A -> B } -> B }",
          "[22]{any,3 ->Scalar }",
          null, "[22,24]" );
  }
  // Obscure factorial-like
  @Test public void b_recursive_02() {
    run("f0 = { f x -> (if (eq0 x) 1 (f (f0 f (dec x)) 2))}; (f0 i* 99)",
        "int64","int64",
        "int64","int64");
  }
  // Obscure factorial-like
  // let f0 = fn f x => (if (eq0 x) 1 (* (f0 f (dec x)) 2) ) in f0 f0 99
  // let f0 = fn f x => (if (eq0 x) 1 (f (f0 f (dec x)) 2) ) in f0 *  99
  @Test public void b_recursive_03() { run("f0 = { f x -> (if (eq0 x) 1 (i* (f0 f (dec x)) 2))}; (f0 f0 99)", "int64", "int64"); }
  
  // Mutual recursion
  @Test public void b_recursive_04() {
    run("is_even = "+
        "  is_odd = { n -> (if (eq0 n) 0 (is_even (dec n)))}; "+
        "     { n -> (if (eq0 n) 1 (is_odd (dec n)))};"+
        "(is_even 3)" ,
        "int1", "int1");
  }

  // Y-combinator
  // After some study, I believe the combined result is correct.  Essentially
  // the 'x' terms take on whatever values are in the induced recursive
  // functions (e.g. 'int' for a 'fact' function).  With no function passed in
  // (just the Y-combinator alone), there is no flow constraint placed on the
  // 'x' terms, and HM "knows" this and "teaches" it to GCP via apply_lift.
  @Test public void b_recursive_05() {
    rune( "{ f -> ({ x -> (f (x x))} { x -> (f (x x))})}",
          "{{ A -> A } -> A }",
          "{{ A -> A } -> A }",
          "[25]{any,3 -> ~Scalar }",
          "[25]{any,3 ->  Scalar }",
          null, "[24,25]");
  }
  @Test public void b_recursive_06() {
    rune("f0 = { f -> (if (rand 2) 1 (f (f0 f) 2))}; f0",
         "{ { 1 2 -> 1 } -> 1 }","{ { 1 2 -> 1 } -> 1 }",
         "[25]{any,3 ->1 }","[25]{any,3 ->Scalar }",
         null,"[24,25]");
  }
  @Test public void b_recursive_07() {
    rune("I = {x->x};"+
         "K = {x->{y->x}};"+
         "W = {x->(x x)};"+
         "term = {z->{y ->((y (z I))(z K))}};"+
         "test = (term W);"+
         "test",
         "{ { A:{A->A} -> {A->B} } -> B }",
         "[27]{any,3 ->Scalar }",
         null,"[22,23,24,25,27]");
  }

  // Test incorrect argument count
  @Test public void b_recursive_err_00() {
    rune("({x y -> (pair x y) } 1 2 3)","Bad arg count: *(1,2)","*[7](_, 1, 2)","[4,7]",null);
  }
  // Test incorrect argument count
  @Test public void b_recursive_err_01() {
    rune("({x y -> (pair x y) } 1 )","Bad arg count: *(1,A)","*[7](_, 1, ~Scalar)","[4,7]",null);
  }
  @Test public void b_recursive_err_02() {
    rune("I = {x->x};"+
         "K = {x->{y->x}};"+
         "W = {x->(x x)};"+
         "term = {z->{y ->((y (z I))(z K))}};"+
         "test = (term W);"+
         "(test {x -> {y -> (pair (x 3) (((y \"a\") \"b\") \"c\")) } })",
         "*( A:[Cannot unify {A->A} and 3 and *str:(nint8)], A )",
         "*[7](_,  Scalar, Scalar)",
         "[4,7]","[]");
  }
  // Stacked if functions "carry through" precision.
  // Test was buggy, since 'rand' is a known non-zero function pointer constant,
  // GCP folds the 'if' to the true arm.  Instead call: '(rand 2)'
  @Test public void b_recursive_err_03() {
    run("i = {x -> x}; k = {x -> (i x)}; l = {x -> (k x)}; m = {x -> (l x)}; n = {x -> (m x)}; (if (rand 2) (n 1) (n \"a\"))",
        "[Cannot unify 1 and *str:(97)]", "nScalar" );
  }

  
  @Test public void c_composition_00() { run( "g = {f -> 5}; (g g)",  "5", "5"); }
  
  @Test public void c_composition_01() {
    rune( "{ f g -> (f g)}",
          "{ { A -> B } A -> B }",
          "[22]{any,4 ->Scalar }",
          null,"[22,24]");
  }
  // Function composition
  @Test public void c_composition_02() {
    rune( "{ f g -> { arg -> (g (f arg))} }",
          "{ { A -> B } { B -> C } -> { A -> C } }",
          "[23]{any,4 ->[22]{any,3 ->Scalar } }",
          null,"[22,23,24,32]");
  }

  @Test public void c_composition_03() {
    rune("x = { y -> (x (y y))}; x",
         "{ A:{ A -> A } -> B }", "[22]{any,3 ->~Scalar }",
         null,"[22,24]");
  }
  
  // Stacked functions ignoring all function arguments
  @Test public void c_composition_04() { run( "map = { fun -> { x -> 2 } }; ((map 3) 5)", "2", "2"); }

  // map takes a function and an element (collection?) and applies it (applies to collection?)
  @Test public void c_composition_05() {
    rune( "map = { fun -> { x -> (fun x)}}; { p -> 5 }",
          "{ A -> 5 }",  "[25]{any,3 -> 5 }",
          null,"[25]");
  }
  // Looking at when tvars are duplicated ("fresh" copies made).
  // This is the "map" problem with a scalar instead of a collection.
  // Takes a '{a->b}' and a 'a' for a couple of different prims.
  @Test public void c_composition_06() {
    rune("map = { fun -> { x -> (fun x)}};"+
         "(pair ((map str) 5) ((map factor) 2.3))",
         "*( *str:(int8), flt64)",
         "*( *str:(int8), flt64)",
         "*[7](_, *[4]str:(int8), flt64)",
         "*[7](_, Scalar, Scalar)",
         "[4,7]",null);
  }
  // map takes a function and an element (collection?) and applies it (applies to collection?)
  @Test public void c_composition_07() { run("map = { fun x -> (fun x)}; (map {a->3} 5)", "3", "3"); }

  // map takes a function and an element (collection?) and applies it (applies to collection?)
  @Test public void c_composition_08() { rune("map = { fun x -> (fun x)}; (map { a-> (pair a a)} 5)", "*( 5, 5)", "*[7](_, 5, 5)","[4,7]",null); }

  @Test public void c_composition_09() {
    rune("""
fcn = { p -> { a -> (pair a a) }};
map = { fun x -> (fun x)};
{ q -> (map (fcn q) 5)}
""",
         "{ A -> *( 5, 5) }", "[27]{any,3 ->*[7](_, 5, 5) }",
         "[4,7]","[27]");
  }
  @Test public void c_composition_10() {
    run("cons ={x y-> {cadr -> (cadr x y)}};"+
        "cdr ={mycons -> (mycons { p q -> q})};"+
        "(cdr (cons 2 3))",
        "3", "3");
  }
  // Take 2nd element of pair, and applies a function.
  //    let map = fn parg fun => (fun (cdr parg))
  // Some pairs:
  //    let intz = (pair2 false 3)
  //    let strz = (pair2 false "abc")
  // in pair(map(str,intz),map(isempty,strz))
  // Expects: ("2",false)
  @Test public void c_composition_11() {
    rune("""
cons ={x y-> {cadr -> (cadr x y)}};
cdr ={mycons -> (mycons { p q -> q})};
map ={fun parg -> (fun (cdr parg))};
(pair (map str (cons 0 5)) (map isempty (cons 0 "abc")))
""",
         "*( *str:(int8), int1)",
         "*( *str:(int8), int1)",
         "*[7](_, *[4]str:(int8), int64)",
         "*[7](_, Scalar, Scalar)",
         "[4,7]",null );
  }  
  // Toss a function into a pair & pull it back out
  @Test public void c_composition_12() {
    rune("""
{ g -> fgz =
         cons = {x y -> {cadr -> (cadr x y)}};
         cdr = {mycons -> (mycons { p q -> q})};
         (cdr (cons 2 { z -> (g z) }));
      (pair (fgz 3) (fgz 5))
}
""",
         "{ { nint8 -> A } -> *( A, A) }",
         "[29]{any,3 ->*[7](_, Scalar, Scalar) }",
         "[4,7]","[24,29]" );
  }

  
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
  @Test public void c_composition_err_00() {
    rune("fcn = {p -> (if p {a -> (pair a a)} {b -> (pair b (pair 3 b))})};"+
         "map = { fun x -> (fun x)};"+
         "{ q -> (map (fcn q) 5)}",
         "{ A? -> *( B:[Cannot unify 5 and *( 3, B)], B) }",
         "[34]{any,3 -> *[7,8](_, 5, nScalar) }",
         "[4,7,8,9]","[34]" );
  }


  // Basic structure test
  @Test public void d_struct_00() {
    rune("@{x=2; y=3}",
         "*@{ x = 2; y = 3}",
         "*[7]@{_; x=2; y=3}",
         "[4,7]",null);
  }
  @Test public void d_struct_01() {
    rune("{ g -> @{x=g; y=g}}",
         "{ A -> *@{ x = A; y = A} }",
         "[22]{any,3 ->*[7]@{_; x=Scalar; y=Scalar} }",
         "[4,7]","[22]");
  }
  // Basic field test
  @Test public void d_struct_02() { run("@{x =2; y =3}.x", "2", "2"); }

  // Load common field 'x', ignoring mismatched fields y and z
  @Test public void d_struct_03() {
    rune("{ pred -> (if pred @{x=2; y=3} @{x=3; z= \"abc\"}) .x }",
         "{ A? -> nint8 }",
         "[26]{any,3 ->nint8 }",
         null,"[26]" );
  }
  @Test public void d_struct_04() {
    rune("A=@{x=3; y=3.2};"+
         "B=@{x=4; z=\"abc\"};"+
         "rez = { pred -> (if pred A B)};"+
         "rez",
         "{ A? -> *@{x=nint8} }",
         "[26]{any,3 ->*[7,8]@{_; x=nint8} }",
         "[4,7,8]","[26]");
  }
  // Load some fields from an unknown struct: area of a rectangle.
  // Since no nil-check, correctly types as needing a not-nil input.
  @Test public void d_struct_05() {
    rune("{ sq -> (i* sq.x sq.y) }", // { sq -> sq.x * sq.y }
         "{ *@{ x = int64; y = int64; ...} -> int64 }",
         "[23]{any,3 ->int64 }",
         "[4,10]","[23]" );
  }
  // Regression test.  Was unexpectedly large type result.  Cut down version of
  // test from marco.servetto@gmail.com.  Looks like it needs some kind of
  // top-level unification with the true->false->true path, and instead the
  // type has an unrolled instance of the 'true' type embedded in the 'false'
  // type.  Bug is actually a core HM algorithm change to handle cycles.
  @Test public void d_struct_06() {
    rune("left =     "+
         "  rite = @{n1 = left v1 = 7 }; "+
         "  @{ n1 = rite v1 = 7 };"+
         "left"+
         "",
         "A:*@{ n1 = *@{ n1 = A; v1 = 7}; v1 = 7}",
         "PA:*[8]@{_; n1=*[7]@{_; n1=PA; FB:v1=7}; FB}",
         "[4,7,8]",null);
  }
  // Unexpected restriction on extra fields.
  @Test public void d_struct_07() {
    rune("sx = { ignore -> "+
         "  self0=@{ succ = (sx self0)}; "+
         "  self0 "+
         "};"+
         "self1=@{ succ = self1; nope=7 };"+
         "(sx self1)"+
         "",
         "A:*@{ succ=A}",
         "PA:*[7]@{_; succ=PA}",
         "[4,7]",null);
  }
  @Test public void d_struct_08() { rune( "fun = { ptr -> ptr.x }; fun", "{ *@{x=A; ... } -> A }", "[22]{any,3 -> Scalar}","[4,10]","[22]");  }
  @Test public void d_struct_09() { rune(       "{ ptr -> ptr.x }",      "{ *@{x=A; ... } -> A }", "[22]{any,3 -> Scalar}","[4,10]","[22]");  }


  // Basic field test
  @Test public void d_struct_err_00() { run("5.x", "Missing field x in 5", "Scalar"); }

  // Basic field test.
  @Test public void d_struct_err_01() { run("@{ y =3}.x", "Missing field x in *@{ y = 3}", "Scalar"); }

  // Example from SimpleSub requiring 'x' to be both a struct with field
  // 'v', and also a function type - specifically disallowed in 'aa'.
  @Test public void d_struct_err_02() {
    rune("{ x -> y = ( x x.v ); 0}",
         "{ [Cannot unify {A->B} and *@{ v=A;...}] -> C? }",
         "[22]{any,3 ->xnil }",
         "[4,10]","[22,24]");
  }
  // Awful flow-type: function can be called from the REPL with any
  // argument type - and the worse case will be an error.
  @Test public void d_struct_err_03() {
    rune("x = { z -> z}; (x { y -> y.u})",
         "{ *@{ u = A; ...} -> A }",
         "[23]{any,3 ->Scalar }",
         "[4,10]","[23]");
  }

  // Example from SimpleSub requiring 'x' to be both:
  // - a recursive self-call function from "w = (x x)": $V66:{ $V66 -> V67 } AND
  // - a function which takes a struct with field 'u'
  // The first arg to x is two different kinds of functions, so fails unification.
  @Test public void d_struct_err_04() {
    rune("x = w = (x x); { z -> z}; (x { y -> y.u})",
         "A:[Cannot unify { A -> A } and *@{ u = A; ... }]",
         "Scalar",
         "[4,7]","[22,23,24,25]");
  }

  // Broken from Marco; function 'f' clearly uses 'p2.a' but example 'res1' does not
  // pass in a field 'a'... and still no error.  Fixed.
  @Test public void d_struct_err_05() {
    rune("f = { p1 p2 -> (if p2.a p1 p2)}; (f @{a=2} @{b=2.3})",
         "*@{ a= Missing field a: 2 }",
         "*[7,8](_)",
         "[4,7,8]",null);
  }
  // Broken from Marco; function 'f' clearly uses 'p2.a' but example 'res1' does not
  // pass in a field 'a'... and still no error.  Fixed.
  @Test public void d_struct_err_06() {
    run("f = { p1 -> p1.a };"+"(f @{b=2.3})",
        "Missing field a",
        "Scalar");
  }

  // Broken from Marco; function 'f' clearly uses 'p2.a' but example 'res1' does not
  // pass in a field 'a'... and still no error.  Fixed.
  @Test public void d_struct_err_07() {
    rune("f = { p1 p2 -> (if p2.a p1 p2)};"+
         "res1 = (f @{a=2;      c=\"def\"} @{    b=2.3;d=\"abc\"});"+
         "res2 = (f @{a=2;b=1.2;c=\"def\"} @{a=3;b=2.3;d=\"abc\"});"+
         "@{f=f;res1=res1;res2=res2}",

         "*@{ f    =  { A:*@{ a=B;... } A -> A };"+
         "    res1 = *@{ a = Missing field a: 2};"+
         "    res2 = *@{ a=nint8; b=nflt32 }"+
         "}",
         "*@{ f    =  { A:*@{ a=B;... } A -> A };"+
         "    res1 = *@{ a = Missing field a: 2};"+
         "    res2 = *@{ a=nint8; b=nflt32 }"+
         "}",
         "*[12]@{_; f=[23]{any,4 ->*[7,8,9,10,11,13]SA::(_) }; res1=*[7,8]SA; res2=*[9,11]@{_; a=nint8; b=nflt32}}",
         "*[12]@{_; f=[23]{any,4 ->Scalar }; res1=Scalar; res2=Scalar}",
         "[4,7,8,9,10,11,12,13]","[23]");
  }


  // Recursive linked-list discovery, with no end clause.  Since this code has
  // no exit (it is an infinite loop, endlessly reading from an infinite input
  // and writing an infinite output), gcp gets a cyclic approximation.
  @Test public void e_recur_struct_00() {
    rune("map = { fcn lst -> @{ n1 = (map fcn lst.n0); v1 = (fcn lst.v0) } }; map",
         "{ { A -> B } C:*@{ n0 = C; v0 = A; ...} -> D:*@{ n1 = D; v1 = B} }",
         "[22]{any,4 ->PA:*[7]@{_; n1=PA; v1=Scalar} }",
         "[4,7,10]","[22,24]");
  }

  // Recursive linked-list discovery, with nil.  Note that the output memory
  // has the output memory alias, but not the input memory alias (which must be
  // made before calling 'map').
  @Test public void e_recur_struct_01() {
    rune("map = { fcn lst -> (if lst @{ n1=(map fcn lst.n0); v1=(fcn lst.v0) } 0) }; map",
         "{ { A -> B } C:*@{ n0 = C; v0 = A; ...}? -> D:*@{ n1 = D; v1 = B}? }",
         "[26]{any,4 ->PA:*[0,7]@{_; n1=PA; v1=Scalar} }",
         "[4,7,10]","[24,26]");
  }
  // Recursive linked-list discovery, applied
  @Test public void e_recur_struct_02() {
    rune("map = { fcn lst -> (if lst @{ n1 = (map fcn lst.n0); v1 = (fcn lst.v0) } 0) }; (map dec @{n0 = 0; v0 = 5})",
         "A:*@{ n1 = A; v1 = int64}?",
         "PA:*[0,7]@{_; n1=PA; v1=4}",
         "[4,7]",null);
  }
  // Need to see if a map call, inlined a few times, 'rolls up'.  Sometimes
  // rolls up, sometimes not; depends on worklist visitation order.
  @Test public void e_recur_struct_03() {
    rune("map = { lst -> (if lst @{ n1= arg= lst.n0; (if arg @{ n1=(map arg.n0); v1=(str arg.v0)} 0); v1=(str lst.v0) } 0) }; map",
         "{ A:*@{ n0 = *@{ n0 = A; v0 = int64; ...}?; v0 = int64; ...}? -> B:*@{ n1 = *@{ n1 = B; v1 = *str:(int8)}?; v1 = *str:(int8)}? }",
         "[31]{any,3 ->PA:*[8]@{_; n1=*[7]@{_; n1=PA; FB:v1=*[4]str:(_, int8)}?; FB}? }",
         "[4,7,8,10]","[31]" );
  }
  // Checking an AA example
  @Test public void e_recur_struct_04() {
    run("prod = { x -> (if x (i* (prod x.n) x.v) 1)};"+
        "(prod @{n= @{n=0; v=3}; v=2})",
        "int64",
        "int64");
  }
  // Example from TestParse.test15:
  //   map={lst fcn -> lst ? fcn lst.1};
  //   in_int=(0,2);"+       // List of ints
  //   in_str=(0,"abc");" +  // List of strings
  //   out_str = map(in_int,str:{int->str});"+        // Map over ints with int->str  conversion, returning a list of strings
  //   out_bool= map(in_str,{str -> str==\"abc\"});"+ // Map over strs with str->bool conversion, returning a list of bools
  //   (out_str,out_bool)",
  @Test public void e_recur_struct_05() {
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
         "*[9](_, *[4]str:(int8), int64)",
         "*[9](_, Scalar, Scalar)",
         "[4,9]",null);
  }
  @Test public void e_recur_struct_06() {
    rune("""
all = @{
  is_even = { dsp n -> (if (eq0 n) 0 (dsp.is_odd  dsp (dec n)))};
  is_odd  = { dsp n -> (if (eq0 n) 1 (dsp.is_even dsp (dec n)))}
};
{ x -> (all.is_even all x)}
""",
         "{int64 -> int1}", "[31]{any,3 ->int1 }",
         null,"[31]");
  }
  @Test public void e_recur_struct_07() {
    rune("dsp = @{  id = { dsp n -> n}}; (pair (dsp.id dsp 3) (dsp.id dsp \"abc\"))",
         "*( 3, *str:(97))",
         "*( 3, *str:(97))",
         "*[8](_, 3 , *[4]str:(97))",
         "*[8](_, nScalar, nScalar)",
         "[4,8]",null);
  }
  // Test example from AA with expanded ints
  @Test public void e_recur_struct_08() {
    rune("int = { i -> @{ i=i; add={ x y -> (int (+ x.i y.i))} } }; x=(int 3); y=(int 4); (x.add x y)",
        """
A:*@{
  add={
     B:*@{ add={ *@{i=int64;...} *@{i=int64;...} -> B };i=int64}
     C:*@{ add={ *@{i=int64;...} *@{i=int64;...} -> C };i=int64}
     -> A};
  i=int64
}
""",
         "PA:*[7]@{_; i=int64; add=[23]{any,4 ->PA }}",
         "[4,7,10,13]","[23]");
  }

  // Recursive structs.  First: closed structs list available fields;
  // unification produces the set intersection.
  @Test public void e_recur_struct_09() {
    rune("{ p -> (if p @{x=3;y=4} @{y=6;z=\"abc\"})}",
         "{A?->*@{y=nint8}}",
         "[26]{any,3 ->*[7,8]@{_; y=nint8} }",
         "[4,7,8]","[26]");
  }
  // Recursive structs.  Next: open structs list required fields;
  // unification produces the set union.
  @Test public void e_recur_struct_10() {
    rune("{ p rec -> (if p rec.x rec.y)}",
         "{ A? *@{x=B;y=B;...} -> B }",
         "[26]{any,4 ->Scalar }",
         "[4,10]","[26]");
  }
  // Recursive structs.  Next: passing extra fields; they are passed along
  // here.  Required fields are fresh every time.
  @Test public void e_recur_struct_11() {
    rune("fun = { rec -> (pair rec rec.x)}; (pair (fun @{x=3;y=4}) (fun @{x=\"abc\";z=2.1}))",
         "*(*(*@{x=3;y=4},3), *(*@{x=A:*str:(97);z=2.1f},A))",
         "*[8](_, PA:*[7](_, *[9,11]@{_; x=nScalar}, nScalar), PA)",
         "[4,7,8,9,11]","[]");
  }
  // Recursive structs.  Next: passing extra fields, but the function requires
  // the structures to be the same.  Extra fields dropped.  Unify required fields.
  @Test public void e_recur_struct_12() {
    rune("({fun -> "+
         "   (pair (fun @{x=3      ;y=4  } )"+    // available {x,y}
         "         (fun @{x=\"abc\";z=2.1} )  )"+ // available {x,z}
         "  } { rec -> (pair rec rec.x) } )",     // required  {x}
         "*(A:*(*@{x=B:[Cannot unify 3 and *str:(97)]},B),A)",
         "*[7](_, PA:*[11](_, *[8,9]@{_; x=nScalar}, nScalar), PA)",
         "[4,7,8,9,11]","[]");
  }
  // Recursive structs.  Next: passing extra fields, but the function requires
  // the structures to be the same.  Extra fields dropped.  Unify required fields.
  @Test public void e_recur_struct_13() {
    rune("({fun -> "+
         "   (pair (fun @{x=3; y=4  } )"+    // available {x,y}
         "         (fun @{x=4; z=2.1} )  )"+ // available {x,z}
         "  } { rec -> (pair rec rec.x) } )",// required  {x}
         "*(A:*(*@{x=nint8},nint8),A)",
         "*[7](_, PA:*[11](_, *[8,9]@{_; x=nint8}, nint8), PA)",
         "[4,7,8,9,11]","[]");
  }
  // Recursive structs.  
  @Test public void e_recur_struct_14() {
    rune("""
fun = { ff ->
  @{ f = ff;                           // available {f,mul}
     mul = { y -> (fun (f* ff y.f)) }  // required {f}
   }
};
(fun 1.2) // required {f} in inner, available {f,mul} in outer
""",
         "A:*@{f=flt64;mul={*@{f=flt64;...}->A}}", // required {f} in inner, available {f,mul} in outer
         "PA:*[7]@{_; f=flt64; mul=[23]{any,3 ->PA }}",
         "[4,7,10]","[23]");
  }

  // Recursive structs, with deeper expressions.  The type expands with
  // expression depth.
  @Test public void e_recur_struct_15() {
    rune("""
fun = { ff ->
  @{ f = ff;                           // available {f,mul}
     mul = { y -> (fun (f* ff y.f)) }  // required {f}
   }
};
con12=(fun 1.2);   // required {f} in inner, available {f,mul} in outer
(con12.mul con12)  // required {f} in inner, available {f,mul} in outer,middle
""",
         "A:*@{f=flt64;mul={B:*@{f=flt64;mul={*@{f=flt64;...}->B}}->A}}", // required {f} in inner, available {f,mul} in middle,outer
         "PA:*[7]@{_; f=flt64; mul=[23]{any,3 ->PA }}",
         "[4,7,10]","[23]");
  }


  // GCP can help HMT
  @Test public void f_gcp_hmt_00() {
    run("pred = 0; s1 = @{ x=\"abc\" }; s2 = @{ y=3.4 }; (if pred s1 s2).y",
        "3.4f",
        "Missing field y in *(): 3.4f",
        "3.4f",
        "3.4f");
  }
  // The z-merge is ignored; the last s2 is a fresh (unmerged) copy.
  @Test public void f_gcp_hmt_01() {
    run("pred = 0; s1 = @{ x=\"abc\" }; s2 = @{ y=3.4 }; z = (if pred s1 s2).x; s2.y",
        "3.4f","3.4f");
  }
  @Test public void f_gcp_hmt_02() {
    run("fun = (if (isempty \"abc\") {x->x} {x->1.2}); (fun @{})",
        "1.2f",
        "[Cannot unify 1.2f and *()]",
        "1.2f","1.2f");

  }
  // Requires a combo of HM and GCP to get the good answer
  @Test public void f_gcp_hmt_03() {
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
        "[Cannot unify int8 and *str:(nint8)?]", // HM alone cannot do this one
        "*[4]str:(100)",      // Both HM and GCP
        "nScalar");           // GCP alone gets a very weak answer
  }
  // Basic uplifting after check
  @Test public void f_gcp_hmt_04() {
    rune("{ pred -> tmp=(if pred @{x=3} 0); (if tmp tmp.x 4) }",
         "{ A? -> nint8 }", "[29]{any,3 ->nint8 }",null,"[29]");
  }
  // map is parametric in nil-ness
  @Test public void f_gcp_hmt_05() {
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
         "[34]{any,3 ->*[7](_, nint8, nint8) }",
         "[34]{any,3 ->*[7](_, nint8, nint8) }",
         "[4,7]","[34]");
  }
  // Simple nil/default test; takes a nilable but does not return one.
  @Test public void f_gcp_hmt_06() {
    rune( "{ x y -> (if x x y) }",
          "{ A? A -> A }", "[26]{any,4 ->Scalar }",
          null,"[26]");
  }
  // Regression test; double nested.  Failed to unify x and y.
  @Test public void f_gcp_hmt_07() {
    rune( "{ x y -> (if x (if x x y) y) }",
          "{ A? A -> A }", "[29]{any,4 ->Scalar }",
          null,"[29]");
  }
  @Test public void f_gcp_hmt_08() {
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
         "[27]{any,4 ->int64 }",
         "[27]{any,4 ->Scalar }",
         "[4,10,13]","[27]");
  }


  // Basic nil test
  @Test public void f_gcp_hmt_err_00() { run("0.x", "May be nil when loading field x", "~Scalar"); }

  // Basic nil test
  @Test public void f_gcp_hmt_err_01() {
    rune("{ pred -> (if pred @{x=3} 0).x}",
         "{ A? -> May be nil when loading field x: 3 }", "[26]{any,3 ->3 }",
         null,"[26]"  );
  }

  // map is parametric in nil-ness.  Verify still nil-checking.
  @Test public void f_gcp_hmt_err_02() {
    rune("""
{ pred ->
  map = { fun x -> (fun x) };
  (pair (map {str0 ->          str0.x   }          @{x = 3}   )
        (map {str1 ->          str1.x   } (if pred @{x = 5} 0))
  )
}
""",
         "{ A? -> *( 3, May be nil when loading field x: 5 ) }",
         "[30]{any,3 ->*[7](_, nint8, nint8) }",
         "[4,7]","[30]");
  }


  // Simple overload def.  Since no uses, no Field to resolve.
  @Test public void g_overload_00() {
    rune("&["                    +  // Define overloaded fcns
         "  { x -> (i* x 2  ) };"+  // Arg is 'int'
         "  { x -> (f* x 3.0) };"+  // Arg is 'flt'
         " ]",
         "*&[ {int64 -> int64}; {flt64 -> flt64} ]",
         "*[7]ov:(_, [23]{any,3 -> int64 }, [26]{any,3 -> flt64 })",
         "[4,7]","[23,26]"
        );
  }
  @Test public void g_overload_01() {
    rune("""
{ pred ->
  fx = &[ (if pred { x -> (i* x 2)} { x -> (i* x 3)});
          { x -> (f* x 0.5) }
        ];
  (pair (fx 2) (fx 1.2))
}
""",
         "{ A? -> *(int64,flt64) }",
         "{ A? -> *(int64,flt64) }",
         "[34]{any,3 -> *[8](_, nint8, 0.6f) }",
         "[34]{any,3 -> *[8](_, Scalar, Scalar) }",
         "[4,8]","[34]");
  }
  // Test case here is trying to get HM to do some overload resolution.
  // Without, many simple int/flt tests in main AA using HM alone fail to find
  // a useful type.
  @Test public void g_overload_02() {
    rune(
"""
fwrap = { ff ->
  @{ f = ff;
     _*_ = &[
       { y -> (fwrap (f* ff (i2f y.i))) };
       { y -> (fwrap (f* ff      y.f)) }
     ]
   }
};
iwrap = { ii ->
  @{ i = ii;
     _*_ = &[
       { y -> (iwrap (i*      ii  y.i)) };
       { y -> (fwrap (f* (i2f ii) y.f)) }
     ]
   }
};

con2   = (iwrap 2  );
con2_1 = (fwrap 2.1);
(con2_1._*_ con2_1)
""",
        "A:*@{_*_=*&[{*@{i=int64;...}->A};{B:*@{_*_=*&[{*@{i=int64;...}->B};{*@{f=flt64;...}->B}];f=flt64}->A}];f=flt64}",
        "PA:*[8]@{_; _*_=*[7]ov:(_, [25]{any,3 -> PA }, [27]{any,3 -> PA }); f=flt64}",
        "[4,7,8,10,13]","[25,27]");
  }

  // Recursive structs.  More like what main AA will do with wrapped primitives.
  @Ignore
  @Test public void g_overload_03() {
    String hm_rez =  "*("+
      "  *@{_*_=A:*&[{B:*@{_*_=*&[{*@{i=int64;...}->B};{*@{f=flt64;...}->C:*@{_*_=*&[{*@{i=int64;...}->C};{*@{f=flt64;...}->C}];f=flt64}}];i=int64}->D:*@{_*_=A;f=flt64}};{*@{f=flt64;...}->D}];f=flt64},"+
      "E:*@{_*_=  *&[{F:*@{_*_=*&[{*@{i=int64;...}->F};{*@{f=flt64;...}->G:*@{_*_=*&[{*@{i=int64;...}->G};{*@{f=flt64;...}->G}];f=flt64}}];i=int64}->E};{*@{f=flt64;...}->H:*@{_*_=*&[{*@{i=int64;...}->H};{*@{f=flt64;...}->H}];f=flt64}}];i=int64},"+
      "I:*@{_*_=  *&[  {*@{i=int64;...}->I};{J:*@{_*_=*&[{*@{i=int64;...}->J};{*@{f=flt64;...}->J}];f=flt64}->I}];f=flt64}"+
      ")";

    rune(
"""
fwrap = { ff ->
  @{ f = ff;
     _*_ = &[
       { y -> (fwrap (f* ff (i2f y.i))) };
       { y -> (fwrap (f* ff      y.f)) }
     ]
   }
};
iwrap = { ii ->
  @{ i = ii;
     _*_ = &[
       { y -> (iwrap (i*      ii  y.i)) };
       { y -> (fwrap (f* (i2f ii) y.f)) }
     ]
   }
};

con2   = (iwrap 2  );
con2_1 = (fwrap 2.1);
mul2 = { x -> (x._*_ con2)};
(triple (mul2 con2_1)  (con2._*_ con2) (con2_1._*_ con2_1))
""",
        hm_rez,
        hm_rez,
        "*[11](_, 0=PA:*[8]@{_; _*_=*[7]ov:(_, [24]{any,3 -> PA }, [26]{any,3 -> PA }); f=flt64}, 1=PB:*[  10]@{_; _*_=*[  9]ov:(_, [   29]{any,3 -> PB }, [   32]{any,3 -> PA }); i=int64}, 2=PA)",
        "*[11](_, 0=PA:*[8]@{_; _*_=*[7]ov:(_, [24]{any,3 -> PA }, [26]{any,3 -> PA }); f=flt64}, 1=PB:*[8,10]@{_; _*_=*[7,9]ov:(_, [24,29]{any,3 -> PB }, [26,32]{any,3 -> PA })         }, 2=PA)",
        "[4,7,8,9,10,11,12,13,14,15]","[4,5,6,24,26,29,32]");
  }

  // Recursive structs, in a loop.  Test of recursive int wrapper type ("occurs
  // check") in a loop.
  @Ignore
  @Test public void g_overload_04() {
    rune(
"""
// fwrap: a wrapped float
fwrap = { ff ->                 // fwrap is a function which takes a float 'ff' and...
  @{ f = ff;                    //   ...returns a struct with fields f, mul.
     mul = &[                   // mul is an overloaded function, which does a widening multiply
       { y -> (fwrap (f* ff (i2f y.i))) }; // widen before f* (float multiply) and fwrap
       { y -> (fwrap (f* ff      y.f)) }   // f* and fwrap
     ];
   }
};

// iwrap: a wrapped integer.
iwrap = { ii ->                 // iwrap is a function which takes an integer 'ii' and...
  @{ i = ii;                    //   ...returns a struct with fields f, mul, is0, sub1.
     mul = &[                   // mul is an overloaded function, which does a widening multiply
       { y -> (iwrap (i*      ii  y.i)) };  // i* (integer multiply) and iwrap
       { y -> (fwrap (f* (i2f ii) y.f)) }   // widen before f* and fwrap
     ];
     is0 = (eq0 ii);            // is0 is a pre-computed boolean, not a function
     sub1= (iwrap (dec ii))     // pre-compute the decrement, and re-wrap
   }
};

c1 = (iwrap 1);                 // The wrapped constant 1
c5 = (iwrap 5);                 // The wrapped constant 5

// Standard factorial, using wrapped integers
fact = { n -> (if n.is0 c1 (n.mul (fact n.sub1))) };
// Compute 5!
(fact c5)
""",
        "A:*@{i=int64;is0=int1;mul=*&[{*@{i=int64;...}->A};{*@{f=flt64;...}->B:*@{f=flt64;mul=*&[{*@{i=int64;...}->B};{*@{f=flt64;...}->B}]}}];sub1=A}",
        "PA:*[8,10]@{_; mul=*[7,9]ov:(_, [24,29]{any,3 -> PA }, [26,32]{any,3 -> PB:*[8]@{_; f=flt64; mul=*[7]ov:(_, [24]{any,3 -> PB }, [26]{any,3 -> PB })} })}",
        "[4,7,8,9,10,11,12,13,14]","[4,5,6,24,26,29,32]");
  }

  // Test overload as union of primitives
  @Test public void g_overload_05() {
    rune("red=&[ 123; \"red\" ]; (pair (dec red) (isempty red))",
         "*(int64,int1)",
         "*(int64,int1)",
         "*[8](_, 122,xnil)",
         "*[8](_, int64, int1)",
         "[4,8]",null);
  }

  // Test overload as union of primitives.  Merge of 2 related overloads stalls
  // resolution until use at 'dec' and 'isempty'.  Each use resolves separately.
  @Test public void g_overload_06() {
    rune("color = { hex name -> &[ hex; name ]};"+
         "red  = (color 123 \"red\" );"+
         "blue = (color 456 \"blue\");"+
         "{ pred -> c =(if pred red blue); (pair (dec c) (isempty c))}",         
         "{ A? -> *(int64,int1) }",
         "{ A? -> *(int64,int1) }",
         "[30]{any,3 -> *[8](_, int64, xnil) })",
         "[30]{any,3 -> *[8](_, int64, int1) }",
         "[4,8]","[4,5,6,30]");
  }

  // Test overload as union of primitives.  Overload resolution before
  // calling 'fun'
  @Ignore
  @Test public void g_overload_07() {
    rune("fun = { a0 -> (dec a0) }; "            + // a0 is an int
         "(pair (fun &[ 123; \"abc\" ]        )" + // Correct overload is 0x123
         "      (fun &[ \"def\"; @{x=1}; 456 ])" + // Correct overload is 0x456
         ")",
         "*(int64,int64)",
         "*[7](_, int64, int64)",
         "[4,7]",null);
  }

  // 'lite' needs to be told to take an overload with syntax
  @Ignore
  @Test public void g_overload_08() {
    rune("color = { hex name -> &[ hex; name ]};"+
         "red  = (color 123 \"red\" );"+
         "blue = (color 456 \"blue\");"+
         "lite = {c -> (color (dec c) (isempty c))};"+ // Should be "(color (sub c 0x111) (cat "light" c))"
         "(pair (lite red) (lite blue))",
         
         "*( &[int,*str:(nint8)], &[int,*str:(nint8)])",
         "*( &[int,*str:(nint8)], &[int,*str:(nint8)])",
         "*[8](_, 0=PA:*[7]ov:(_, int64, *[4]str:(nint8)), 1=PA)",
         "*[8](_, 0=PA:*[7]ov:(_, int64, Scalar), 1=PA)",
         "[4,8]","[4,5,6,29]");
  }

  // Simple overloaded function test.
  // Insert Fields for all 'f' uses, but some or all may go away.
  @Test public void g_overload_09() {
    rune("f = &["                +  // Define overloaded fcns 'f'
         "  { x -> (i* x 2  ) };"+  // Arg is 'int'
         "  { x -> (f* x 3.0) };"+  // Arg is 'flt'
         "];"+
         "(pair (f 2) (f 1.2))",    // Call with different args
         "*(int64,flt64)", "*(int64,flt64)",
         "*[8](_, 4,3.6000001f)", "*[8](_, Scalar, Scalar)",
         "[4,8]",null);
  }


  // Ambiguous overload, {int->int}, cannot select.
  // Parent of overload is Apply, so 
  @Test public void g_overload_err_00() {
    run("(&["                  +  // Define overloaded fcns
        "   { x -> (i* x 2) };"+  // Arg is 'int'
        "   { x -> (i* x 3) };"+  // Arg is 'int'
        "  ] 4)",                 // Error, ambiguous
        "Ambiguous overload",
        "nint8"
      );
  }
  // Wrong args for all overloads
  @Test public void g_overload_err_01() {
    run("(&[ { x y -> (i* x y) }; { x y z -> (i* y z) };] 4)",
        "Bad arg count: int64",
        "~int64");
  }
  // Mixing unrelated overloads
  @Test public void g_overload_err_02() {
    rune("""
fx = &[ { x -> 3     }; { y -> "abc" }; ];
fy = &[ { z -> "def" }; { a -> 4     }; ];
fz = (if (rand 2) fx fy);
(isempty (fz 1.2))
""",
         "Ambiguous overload: int1",
         "int1",
         null,null);
  }
  // Test overload as union of primitives.  Merge of 2 unrelated overloads
  // forces resolution at the 'if'; hence 'red' is typed as either 'int' or
  // 'str' and one of '(dec red)' or '(isempty red)' must fail.
  @Test public void g_overload_err_03() {
    rune("{ pred -> red=(if pred &[ 123; \"red\" ] &[456;  \"blue\" ]); (pair (dec red) (isempty red))}",
         "{ A? -> *(Mismatched overloads: int64, Mismatched overloads: int1) }",
         "{ A? -> *(Mismatched overloads: int64, Mismatched overloads: int1) }",
         "[29]{any,3 -> *[9](_, int64, xnil) }",
         "[29]{any,3 -> *[9](_, int64, int1) }",
         "[4,9]","[4,5,6,29]");
  }


  // Create a boolean-like structure, and unify.
  @Test public void x_peano_00() {
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
         "bool=@{true=(forceSubtyping 1); false=(forceSubtyping 0); force=forceSubtyping};"+
         // Apply the unified 'false' to two different return contexts
         "testa=(bool.false.then { x-> 3 } { y-> 4 });"+
         "testb=(bool.false.then { z->@{}} { z->@{}});"+
         // Look at the results
         "@{a=testa; b=testb; bool=bool}"+
         "",
         "*@{ a = nint8; b = *( ); bool = *@{ false = A:*@{ and = { A -> A }; or = { A -> A }; then = { { *( ) -> B } { *( ) -> B } -> B }}; force = { C? -> D:*@{ and = { D -> D }; or = { D -> D }; then = { { *( ) -> E } { *( ) -> E } -> E }} }; true = F:*@{ and = { F -> F }; or = { F -> F }; then = { { *( ) -> G } { *( ) -> G } -> G }}}}",
         "*@{ a = nint8; b = *( ); bool = *@{ false = A:*@{ and = { A -> A }; or = { A -> A }; then = { { *( ) -> B } { *( ) -> B } -> B }}; force = { C? -> D:*@{ and = { D -> D }; or = { D -> D }; then = { { *( ) -> E } { *( ) -> E } -> E }} }; true = F:*@{ and = { F -> F }; or = { F -> F }; then = { { *( ) -> G } { *( ) -> G } -> G }}}}",
         "*[15]@{_; a=int64 ; b=*[12,14](_); bool=*[11]@{_; false=PA:*[8,9]@{_; and=[22,26]{any,3 ->Scalar }; or=[23,27]{any,3 ->Scalar }; then=[25,28]{any,4 ->Scalar }}; force=[33]{any,3 ->PA }; true=PA}}",
         "*[15]@{_; a=Scalar; b=Scalar     ; bool=*[11]@{_; false=PA:*[8,9]@{_; and=[22,26]{any,3 ->Scalar }; or=[23,27]{any,3 ->Scalar }; then=[25,28]{any,4 ->Scalar }}; force=[33]{any,3 ->PA }; true=PA}}",
         "[4,7,8,9,11,12,14,15]","[22,23,24,25,26,27,28,32,33]");
  }


  // Regression test; was NPE.  Was testMyBoolsNullPException from marco.servetto@gmail.com.
  @Test public void x_peano_01() {
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
         "*[11]@{_; false=PB:*[8,9]@{_; and=[22,27]{any,3 -> Scalar }; not=[25,29]{any,3 -> PA:*[8]@{_; and=[22]{any,3 -> Scalar }; not=[25]{any,3 -> PA }; or=[23]{any,3 -> PA }; then=[26]{any,4 -> Scalar }} }; or=[23,28]{any,3 -> Scalar }; then=[26,30]{any,4 -> Scalar }}; true=PB}",
         "[7,8,9,11]","[22,23,24,25,26,27,28,29,30,32]");
  }

  @Test public void x_peano_02() {
    rune("""
all =
true = @{
  not = {unused -> all.false};
  then = {then else->(then 7) }
};
false = @{
  not = {unused -> all.true};
  then = {then else->(else 7) }
};
boolSub ={b ->(if b true false)};
@{true=true; false=false; boolSub=boolSub};
all
""",
        "*@{ boolSub = { A? -> *@{ not = { B -> C:*@{ not = { D -> C }; then = { { 7 -> E } { 7 -> E } -> E }} }; then = { { 7 -> F } { 7 -> F } -> F }} }; false = C; true = C}",
        """
*[9]@{_;
  boolSub=[30]{any,3 ->
    PA:*[7,8]@{_; not=[22,25]{any,3 ->PA }; then=[23,26]{any,4 ->Scalar }}
  };
  false=PB:*[8]@{_; not=[25]{any,3 ->PC:*[7]@{_; not=[22]{any,3 ->PB }; then=[23]{any,4 ->Scalar }} }; then=[26]{any,4 ->Scalar }};
  true=PC
}
""",
         "[4,7,8,9]","[22,23,24,25,26,30,32]");
  }

  // Full on Peano arithmetic.
  @Test public void x_peano_03() {
    String gcp_rez = """
*[16]@{_;
  b=*[11]@{_;
    false=PA:*[9]@{_; and_=[27]{any,3 -> PA     }; or__=[28]{any,3 -> Scalar }; then=[29]{any,4 -> Scalar }};
    true =PB:*[8]@{_; and_=[23]{any,3 -> Scalar }; or__=[25]{any,3 -> PB     }; then=[26]{any,4 -> Scalar }}
  };
  n=*[15]@{_;
    s=[38]{any,3 ->
      PC:*[14]@{_;
        add_=[37]{any,3 -> Scalar };
        pred=[35]{any,3 -> Scalar };
        succ=[36]{any,3 -> PC };
        zero=[34]{any,3 -> PA }
      }
    };
    z=*[12]@{_; add_=[33]{any,3 -> Scalar }; pred=[22]{any,3 -> ~Scalar }; succ=[31]{any,3 -> PC }; zero=[30]{any,3 -> PB }}
  };
  one  =PC;
  three=PC;
  two  =Scalar
}
""";
    
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
  @{true=true; false=false};
// Natural numbers are formed from zero (z) and succ (s).
// They are structs which support zero, pred, succ and add.
n=
// Zero, is a struct supporting functions "zero" (always true), "pred"
// (error; no predecessor of zero), "succ" successor, and "add_" which is a no-op.
  z = @{
    zero = {unused ->b.true};
    pred = err
    succ = {unused -> (n.s n.z)};
    add_ = {o-> o}
  };
// Successor, is a function taking a natural number and returning the successor
// (which is just a struct supporting the functions of natural numbers).
  s = { pred ->
    self=@{
      zero = {unused ->b.false};  // zero is always false for anything other than zero
      pred = {unused -> pred };   // careful! 'pred=' is a label, the returned 'pred' was given as the argument 'pred->'
      succ = {unused -> (n.s self)};
      add_ = {m -> ((pred.add_ m).succ void)} // a little odd, but really this counts down (via recursion) on the LHS and applies that many succ on the RHS
    };
    self
  };
  @{s=s; z=z};
// Do some Maths
one = (n.s n.z);      // One is the successor of zero
two = (one.add_ one); // Two is one plus one
three =(n.s two);     // Three is the successor of two
// Return a result, so things are not dead.
@{b=b;n=n; one=one;two=two;three=three}
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
        gcp_rez, gcp_rez,
        "[4,7,8,9,10,11,12,13,14,15,16]","[4,5,6,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38]");
  }

  // Regression during the HM/GCP Apply lift.
  @Test public void x_peano_04() {
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
*[14]@{_;
  false=PC:*[8,9]@{_; and=[23,27]{any,3 -> Scalar }; or=[25,28]{any,3 -> Scalar }; then=[26,29]{any,4 -> Scalar }};
  true =PC;
  s=[45]{any,3 ->
    PA:*[12]@{_;
      add_=[44]{any,3 -> PA };
      pred=[42]{any,3 -> PB:*[10,11,12,13,17,18]@{_; add_=[4,5,22,23,25,27,28,35,36,37,41,42,43,44,45]{any,3 -> Scalar }; pred=[4,5,22,23,24,25,27,28,32,35,36,37,41,42,43,44,45]{any,3 -> PB }; succ=[4,5,22,23,25,27,28,35,36,37,41,42,43,44,45]{any,3 -> PB }; zero=[4,5,22,23,24,25,27,28,32,35,36,37,41,42,43,44,45]{any,3 -> PC }} };
      succ=[43]{any,3 -> PA };
      zero=[41]{any,3 -> PC }
    }
  };
  z=*[11]@{_;
    add_=[37]{any,3 ->  Scalar };
    pred=[22]{any,3 -> ~Scalar };
    succ=[36]{any,3 -> PA };
    zero=[35]{any,3 -> PC }
  }
}
""",
         """
*[14]@{_;
  false=PA:*[8,9]@{_; and=[23,27]{any,3 -> Scalar }; or=[25,28]{any,3 -> Scalar }; then=[26,29]{any,4 -> Scalar }};
  true= PA;
  s=[45]{any,3 -> Scalar };
  z=*[11]@{_; add_=[37]{any,3 -> Scalar }; pred=[22]{any,3 -> ~Scalar }; succ=[36]{any,3 -> Scalar }; zero=[35]{any,3 -> PA }}
}
""",
         "[4,7,8,9,10,11,12,13,14,17,18]",
         "[4,5,6,22,23,24,25,26,27,28,29,32,35,36,37,41,42,43,44,45]"
         );
  }


  // Poster-child collection, larger example
  @Test public void x_peano_05() {
    rune("""
rand = (factor 1.2);
cage = { ->
  put = { pet ->
    @{ put = put;
       get = pet
     }
  };
  (put 0)
};
cat = @{ name="Pete"; purr_vol=1.2 };
dog = @{ name="Spot"; wag_rate=2.3 };
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
         "*[11](_, Scalar, Scalar, *[4]str:(nint8))",
         "[4,11]",null);
  }

  // Shorter version of perf_01
  @Test public void x_perf_00() {
    String rez_hm = "*({A B C -> *(A,B,C)},{D E F -> *(D,E,F)},{GHI->*(G,H,I)})";
    rune("p0 = { x y z -> (triple x y z) };"+
         "p1 = (triple p0 p0 p0);"+
         "p1",

         rez_hm,
         "*[8](_, XA:[23]{any,5 ->*[7](_, Scalar, Scalar, Scalar) }, XA, XA)",
         "[4,7,8]","[23]"  );
  }

  // try the worse-case expo blow-up test case from SO
  @Test public void x_perf_01() {
    String rez_hm = "*( *( *( { A B C -> *( A, B, C) }, { D E F -> *( D, E, F) }, { G H I -> *( G, H, I) }), *( { J K L -> *( J, K, L) }, { M N O -> *( M, N, O) }, { P Q R -> *( P, Q, R) }), *( { S T U -> *( S, T, U) }, { V22 V23 V24 -> *( V22, V23, V24) }, { V25 V26 V27 -> *( V25, V26, V27) })), *( *( { V28 V29 V30 -> *( V28, V29, V30) }, { V31 V32 V33 -> *( V31, V32, V33) }, { V34 V35 V36 -> *( V34, V35, V36) }), *( { V37 V38 V39 -> *( V37, V38, V39) }, { V40 V41 V42 -> *( V40, V41, V42) }, { V43 V44 V45 -> *( V43, V44, V45) }), *( { V46 V47 V48 -> *( V46, V47, V48) }, { V49 V50 V51 -> *( V49, V50, V51) }, { V52 V53 V54 -> *( V52, V53, V54) })), *( *( { V55 V56 V57 -> *( V55, V56, V57) }, { V58 V59 V60 -> *( V58, V59, V60) }, { V61 V62 V63 -> *( V61, V62, V63) }), *( { V64 V65 V66 -> *( V64, V65, V66) }, { V67 V68 V69 -> *( V67, V68, V69) }, { V70 V71 V72 -> *( V70, V71, V72) }), *( { V73 V74 V75 -> *( V73, V74, V75) }, { V76 V77 V78 -> *( V76, V77, V78) }, { V79 V80 V81 -> *( V79, V80, V81) })))";
    rune("p0 = { x y z -> (triple x y z) };"+
         "p1 = (triple p0 p0 p0);"+
         "p2 = (triple p1 p1 p1);"+
         "p3 = (triple p2 p2 p2);"+
         "p3",

         rez_hm,
         "*[11](_, PB:*[9](_, PA:*[8](_, XA:[23]{any,5 ->*[7](_, Scalar, Scalar, Scalar) }, XA, XA), PA, PA), PB, PB)",
         "[4,7,8,9,11]","[23]");
  }
}

