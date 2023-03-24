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
    a_basic_02();
  }

  private void _run0s( String prog, String rprog, String rez_hm, String frez_gcp, int rseed, String esc_ptrs, String esc_funs  ) {
    // Type the program
    HM.reset();
    Root syn = HM.hm(prog, rseed, rez_hm!=null, frez_gcp!=null );
    // Check the expected syntactic rewriting.  'if id e0 e1' expressions are
    // rewritten so that 'id' is known not-nul in 'e0'.  Also inferred field
    // names are actually inferred (or program is in-error).
    if( rprog==null ) rprog=prog;
    //assertEquals(stripIndent("("+rprog+")"),stripIndent(syn.toString()));
    Type gcp = Type.valueOf(frez_gcp);
    
    // Check expected types for HMT and GCP
    Type rflow = null;
    if( gcp    !=null )  if( gcp != (rflow=syn.flow_type()) ) System.err.println(gcp + " =!= " + rflow);
    if( rez_hm !=null )  if( !stripIndent(rez_hm).equals(stripIndent(syn._hmt.p())) ) System.err.println(rez_hm+" =!= "+syn._hmt.p());
    if( gcp    !=null )  assertEquals(gcp,rflow);
    if( rez_hm !=null )  assertEquals(stripIndent(rez_hm),stripIndent(syn._hmt.p()));

    // Track expected Root escapes
    if( rez_hm!=null && gcp!=null && !rez_hm.contains("Cannot") ) {
      String esc_ptrs2 = "*"+esc_ptrs+"()";
      String esc_funs2 =     esc_funs+"{any,3->Scalar}";
      BitsAlias aliases = esc_ptrs==null ? BitsAlias.EMPTY : ((TypeMemPtr)Type.valueOf(esc_ptrs2))._aliases;
      BitsFun   fidxs   = esc_funs==null ? BitsFun  .EMPTY : ((TypeFunPtr)Type.valueOf(esc_funs2)).fidxs() ;
      aliases = aliases.meet(TypeMemPtr.STRPTR._aliases); // Always string alias
      for( HM.EXTLambda elam : Root.EXTS )  if( elam!=null )  fidxs = fidxs.set(elam._fidx); // Always the default escapes
      if( aliases!=Root.ext_aliases() ) System.err.println("ALIAS "+aliases+" =!= "+Root.ext_aliases());
      if( fidxs  !=Root.ext_fidxs  () ) System.err.println("FIDX  "+fidxs  +" =!= "+Root.ext_fidxs  ());
      assertEquals(aliases,Root.ext_aliases());
      assertEquals(fidxs  ,Root.ext_fidxs  ());
    }
  }

  private void _run1s( String prog, String rprog, String rez_hm, String frez_gcp, String esc_ptrs, String esc_funs ) {
    if( JIG )
      _run0s(prog,rprog,rez_hm,frez_gcp,RSEED,esc_ptrs,esc_funs);
    else
      for( int rseed=0; rseed<4; rseed++ )
        _run0s(prog,rprog,rez_hm,frez_gcp,rseed,esc_ptrs,esc_funs);
  }

  // Run same program in all 3 combinations, but answers vary across combos
  private void run( String prog, String rprog, String rez_hm_gcp, String rez_hm_alone, String frez_gcp_hm, String frez_gcp_alone, String esc_ptrs, String esc_funs ) {
    if(   rez_hm_alone == null )   rez_hm_alone = rez_hm_gcp;
    if( frez_gcp_alone == null ) frez_gcp_alone = frez_gcp_hm;
    if( JIG ) {
      _run1s(prog, rprog,
             DO_HMT ? (DO_GCP ?  rez_hm_gcp :   rez_hm_alone ) : null,
             DO_GCP ? (DO_HMT ? frez_gcp_hm : frez_gcp_alone ) : null, esc_ptrs, esc_funs);
    } else {
      _run1s(prog, rprog, null        ,frez_gcp_alone, esc_ptrs, esc_funs);
      _run1s(prog, rprog, rez_hm_alone,     null     , esc_ptrs, esc_funs);
      _run1s(prog, rprog, rez_hm_gcp  ,frez_gcp_hm   , esc_ptrs, esc_funs);
    }
    Type gcp_alone = Type.valueOf(frez_gcp_alone);
    Type gcp_hm    = Type.valueOf(frez_gcp_hm   );
    assert gcp_hm.isa(gcp_alone); // Broken test, expected GCP only improves with more information
  }
  // Same thing with a bunch of default arguments
  private void run( String prog, String rprog, String rez_hm, String frez_gcp, String esc_ptrs, String esc_funs ) { run(prog,rprog,rez_hm,null,frez_gcp,null,esc_ptrs,esc_funs); }
  private void run( String prog,               String rez_hm, String frez_gcp, String esc_ptrs, String esc_funs ) { run(prog,null ,rez_hm,null,frez_gcp,null,esc_ptrs,esc_funs); }
  private void run( String prog,               String rez_hm, String frez_gcp                                   ) { run(prog,null ,rez_hm,null,frez_gcp,null,null    ,null    ); }

  private static String stripIndent(String s){
    String s2 = s.replaceAll("//.*(?=\\n)", "");
    String s3 = s2.replace("\n","").replace(" ","");
    return s3;
  }


  @Test public void a_basic_00() { run( "3", "3", "3");  }

  @Test public void a_basic_01() {
    run( "{ x -> (pair 3 x) }" ,
         "{ A -> *( 3, A) }",
         "[30]{any,3 -> *[17](_, 3,Scalar)}",
         "[17]", "[30]" );
  }
  @Test public void a_basic_02() {
    run( "{ z -> (pair (z 0) (z 5)) }" ,
          "{ { int8 -> A } -> *( A, A ) }",
          "[30]{any,3 ->*[17](_, Scalar, Scalar) }",
          "[17]", "[8,30]" );
  }
  @Test public void a_basic_02a() {
    run( "{ z -> (pair (z 0) (z \"abc\")) }" ,
          "{ { *str:(97)? -> A } -> *( A, A ) }",
          "[30]{any,3 ->*[17](_, Scalar, Scalar) }",
          "[17]", "[8,30]" );
  }
  
  // Because {y->y} is passed in, all 'y' types must agree.
  // This unifies 3 and 5 which results in 'nint8'
  @Test public void a_basic_03() {
    run("({ id -> (pair (id 3) (id 5) ) } {x->x})",
        null,
         "*( nint8, nint8)",   // HMT result type, using both GCP + HMT
         "*( nint8, nint8)",   // HMT result type, HMT alone
         "*[17](_, 3, 5)",      // GCP result type, using both GCP + HMT
         "*[17](_, nint8, nint8)", // GCP result type, GCP alone
          "[17]",null);
  }
  @Test public void a_basic_04() {
    run("id={x->x}; (pair (id 3) (id \"abc\"))",
        null,
        // HM is sharper here than in a_basic_03, because id is generalized per each use site
        "*( 3, *str:(97))",
        "*( 3, *str:(97))",
        // GCP with HM
        "*[17](_, 3, *[4]str:(97))",
        // GCP is weaker without HM, reports error tuple
        "*[17](_, %[4][], %[4][])",
        "[17]", null );
  }
  // example that demonstrates generic and non-generic variables:
  @Test public void a_basic_05() {
    run( "{ g -> f = { ignore -> g }; (pair (f 3) (f \"abc\"))}",
         "{ A -> *( A, A) }",
         "[31]{any,3 ->*[17](_, Scalar, Scalar) }",
         "[17]","[31]");
  }
  @Test public void a_basic_06() { run("(i* 2 3)","%int64","6");  }


  @Test(expected = RuntimeException.class)
  public void a_basic_err_00() { run( "fred","","all"); }

  @Test public void a_basic_err_01() {
    run("(+ \"abc\" 0)",
        "%[Cannot unify int64 and *str:(97)]",
        "int64");
  }


  @Test public void b_recursive_00() {
    run( "fact = { n -> (if (eq0 n) 1 (i* n (fact (dec n))))}; fact",
          "{ %int64 -> %int64 }",
          "[33]{any,3 -> int64 }",
          null, "[33]" );
  }
  // recursive unification; normal H-M fails here.
  @Test public void b_recursive_01() {
    run( "{ f -> (f f) }",
          // We can argue the pretty-print should print:
          // "  A:{ A -> B }"
          "{ A:{ A -> B } -> B }",
          "[29]{any,3 ->Scalar }",
          null, "[8,29]" );
  }
  // Obscure factorial-like
  @Test public void b_recursive_02() {
    run("f0 = { f x -> (if (eq0 x) 1 (f (f0 f (dec x)) 2))}; (f0 i* 99)",
        "%int64","int64");
  }
  // Obscure factorial-like
  // let f0 = fn f x => (if (eq0 x) 1 (* (f0 f (dec x)) 2) ) in f0 f0 99
  // let f0 = fn f x => (if (eq0 x) 1 (f (f0 f (dec x)) 2) ) in f0 *  99
  @Test public void b_recursive_03() { run("f0 = { f x -> (if (eq0 x) 1 (i* (f0 f (dec x)) 2))}; (f0 f0 99)", "%int64", "int64"); }

  // Mutual recursion
  @Test public void b_recursive_04() {
    run("is_even = "+
        "  is_odd = { n -> (if (eq0 n) 0 (is_even (dec n)))}; "+
        "     { n -> (if (eq0 n) 1 (is_odd (dec n)))};"+
        "(is_even 3)" ,
        null,
        "%int64", "%int64",
        "int1", "int1",
        null, null);
  }

  // Y-combinator
  // After some study, I believe the combined result is correct.  Essentially
  // the 'x' terms take on whatever values are in the induced recursive
  // functions (e.g. 'int' for a 'fact' function).  With no function passed in
  // (just the Y-combinator alone), there is no flow constraint placed on the
  // 'x' terms, and HM "knows" this and "teaches" it to GCP via apply_lift.
  @Test public void b_recursive_05() {
    run( "{ f -> ({ x -> (f (x x))} { x -> (f (x x))})}",
         null,
         "{{ A -> A } -> A }",
         "{{ A -> A } -> A }",
         "[31]{any,3 -> ~Scalar }",
         "[31]{any,3 -> Scalar }",
         null, "[8,31]");
  }
  @Test public void b_recursive_06() {
    run("f0 = { f -> (if (rand 2) 1 (f (f0 f) 2))}; f0",
        null,
        "{ { %int64 2 -> %int64 } -> %int64 }",
        "{ { %int64 2 -> %int64 } -> %int64 }",
        "[31]{any,3 ->int64 }",
        "[31]{any,3 ->int64 }",
        null,"[8,31]");
  }
  @Test public void b_recursive_07() {
    run("I = {x->x};"+
        "K = {x->{y->x}};"+
        "W = {x->(x x)};"+
        "term = {z->{y ->((y (z I))(z K))}};"+
        "test = (term W);"+
        "test",
        "{ { A:{A->A} -> {A->B} } -> B }",
        "[33]{any,3 ->Scalar }",
        null,"[8,29,30,31,33]");
  }

  // Test incorrect argument count
  @Test public void b_recursive_err_00() {
    run("({x y -> (pair x y) } 1 2 3)","Bad arg count: *(1,2)","*[17](_, 1, 2)","[17]",null);
  }
  // Test incorrect argument count
  @Test public void b_recursive_err_01() {
    run("({x y -> (pair x y) } 1 )","Bad arg count: *(1,A)","*[17](_, 1, ~Scalar)","[17]",null);
  }


  // At its core, this program defines "W = {x->(x x)}", a recurive type.
  // Later it applies W to I (id): (W I)
  //    W alone types as "A:{ A -> B }"
  //    (W I)   types as "A:{ A -> A }".
  // This difference keeps AA from typing this program, although there
  // exists a beta-reduction order which will type this program.
  @Test public void b_recursive_err_02() {
    run("I = {x->x};"+
        "K = {x->{y->x}};"+
        "W = {x->(x x)};"+
        "term = {z->{y ->((y (z I))(z K))}};"+
        "test = (term W);"+
        "(test {x -> {y -> (pair (x 3) (((y \"abc\") \"def\") \"red\")) } })",
        "*( A:[Cannot unify {A->A} and 3 and *str:(nint8)], A )",
        "*[17](_,  Scalar, Scalar)",
        "[17]","[]");
  }
  
  
  // Stacked if functions "carry through" precision.
  // Test was buggy, since 'rand' is a known non-zero function pointer constant,
  // GCP folds the 'if' to the true arm.  Instead, call: '(rand 2)'
  @Test public void b_recursive_err_03() {
    run("i = {x -> x}; "+
        "k = {x -> (i x)}; "+
        "l = {x -> (k x)}; "+
        "m = {x -> (l x)}; "+
        "n = {x -> (m x)}; "+
        "(if (rand 2) (n 1) (n \"abc\"))",
        "%[Cannot unify int64 and *str:(97)]", "%[4][]" );
  }


  @Test public void c_composition_00() { run( "g = {f -> 5}; (g g)",  "5", "5"); }

  @Test public void c_composition_01() {
    run( "{ f g -> (f g)}",
          "{ { A -> B } A -> B }",
          "[29]{any,4 ->Scalar }",
          null,"[8,29]");
  }
  // Function composition
  @Test public void c_composition_02() {
    run( "{ f g -> { arg -> (g (f arg))} }",
          "{ { A -> B } { B -> C } -> { A -> C } }",
          "[30]{any,4 ->[29]{any,3 ->Scalar } }",
          null,"[8,9,29,30]");
  }

  @Test public void c_composition_03() {
    run("x = { y -> (x (y y))}; x",
         "{ A:{ A -> A } -> B }", "[29]{any,3 ->~Scalar }",
         null,"[8,29]");
  }

  // Stacked functions ignoring all function arguments
  @Test public void c_composition_04() { run( "map = { fun -> { x -> 2 } }; ((map 3) 5)", "2", "2"); }

  // map takes a function and an element (collection?) and applies it (applies to collection?)
  @Test public void c_composition_05() {
    run( "map = { fun -> { x -> (fun x)}}; { p -> 5 }",
          "{ A -> 5 }",  "[31]{any,3 -> 5 }",
          null,"[31]");
  }
  // Looking at when tvars are duplicated ("fresh" copies made).
  // This is the "map" problem with a scalar instead of a collection.
  // Takes a '{a->b}' and a 'a' for a couple of different prims.
  @Test public void c_composition_06() {
    run("map = { fun -> { x -> (fun x)}};"+
        "(pair ((map str) 5) ((map factor) 2.3f))",
        null,
        "*(%*str:(int8),%flt64)",
        "*(%*str:(int8),%flt64)",
        "*[17](_, *[4]str:(int8), flt64)",
        "*[17](_, %[4][]?, %[4][]?)",
        "[17]",null);
  }
  // map takes a function and an element (collection?) and applies it (applies to collection?)
  @Test public void c_composition_07() { run("map = { fun x -> (fun x)}; (map {a->3} 5)", "3", "3"); }

  // map takes a function and an element (collection?) and applies it (applies to collection?)
  @Test public void c_composition_08() { run("map = { fun x -> (fun x)}; (map { a-> (pair a a)} 5)", "*( 5, 5)", "*[17](_, 5, 5)","[17]",null); }

  @Test public void c_composition_09() {
    run("""
fcn = { p -> { a -> (pair a a) }};
map = { fun x -> (fun x)};
{ q -> (map (fcn q) 5)}
""",
         "{ A -> *( 5, 5) }", "[33]{any,3 ->*[17](_, 5, 5) }",
         "[17]","[33]");
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
    run("""
cons ={x y-> {cadr -> (cadr x y)}};
cdr ={mycons -> (mycons { p q -> q})};
map ={fun parg -> (fun (cdr parg))};
(pair (map str (cons 0 5)) (map isempty (cons 0 "abc")))
""",
        null,
        "*(%*str:(int8),%int64)",
        "*(%*str:(int8),%int64)",
        "*[17](_, *[4]str:(int8), int64)",
        "*[17](_, %[4][]?, %[4][]?)",
        "[17]",null );
  }
  // Toss a function into a pair & pull it back out
  @Test public void c_composition_12() {
    run("""
{ g -> fgz =
         cons = {x y -> {cadr -> (cadr x y)}};
         cdr = {mycons -> (mycons { p q -> q})};
         (cdr (cons 2 { z -> (g z) }));
      (pair (fgz 3) (fgz 5))
}
""",
         "{ { nint8 -> A } -> *( A, A) }",
         "[35]{any,3 ->*[17](_, Scalar, Scalar) }",
         "[17]","[8,35]" );
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
    run("fcn = {p -> (if p {a -> (pair a a)} {b -> (pair b (pair 3 b))})};"+
        "map = { fun x -> (fun x)};"+
        "{ q -> (map (fcn q) 5)}",

        "fcn = {p -> (if p ({_p->{a -> (pair a a)}}(notnil p)) {b -> (pair b (pair 3 b))})};"+
        "map = { fun x -> (fun x)};"+
        "{ q -> (map (fcn q) 5)}",

        "{ A? -> *( B:[Cannot unify 5 and *(3, B)], B) }",
        "{ A? -> *( B:[Cannot unify 5 and *(3, B)], B) }",
        "[39]{any,3 -> *[17,18](_, 5, %[19][]) }",
        "[39]{any,3 -> *[17,18](_, 5, %[19][]) }",
        "[17,18,19]","[39]" );
  }

  // Funny test cases checking out how AA handles the difference between
  // "forall A: [{A->A}]" vs "[forall A:{A->A}]".
  @Test public void c_composition_err_01() {
    run( "{ g -> (if (g 1) (g \"abc\") (g \"def\") ) }",
         "{{[Cannot unify 1 and *str:(nint8)] -> A:%B? } -> A }",
         "[30]{any,3 -> Scalar }");
  }

  // Another variant; notice the broken error report; the argument
  // in "{ -> A }" is missing.
  @Test public void c_composition_err_02() {
    run( "f = { x->x }; g = (f f); (pair (g (rand 99)) (\"abc\"))", null,
         "*(%int64,A:[Cannot unify { -> A } and *str:(97)])",
         "*(%int64,A:[Cannot unify { -> A } and *str:(97)])",
         "*[17](_,  int64, Scalar)",
         "*[17](_, Scalar, Scalar)",
          null,null);
  }


  // Basic structure test
  @Test public void d_struct_00() {
    run("@{x=2; y=3}",
         "*@{ x = 2; y = 3}",
         "*[17]@{_; x=2; y=3}",
         "[17]",null);
  }
  @Test public void d_struct_01() {
    run("{ g -> @{x=g; y=g}}",
         "{ A -> *@{ x = A; y = A} }",
         "[29]{any,3 ->*[17]@{_; x=Scalar; y=Scalar} }",
         "[17]","[29]");
  }
  // Basic field test
  @Test public void d_struct_02() { run("@{x =2; y =3}.x", "2", "2"); }

  // Load common field 'x', ignoring mismatched fields y and z
  @Test public void d_struct_03() {
    run("{ pred -> (if pred @{x=2; y=3} @{x=3; z= \"abc\"}) .x }",
        "{ pred -> (if pred ({_pred -> @{x=2; y=3}} (notnil pred)) @{x=3; z= \"abc\"}) .x }",
        "{ A? -> nint8 }",
        "[32]{any,3 ->nint8 }",
        null,"[32]" );
  }
  @Test public void d_struct_04() {
    run("A=@{x=3; y=3.2f};"+
        "B=@{x=4; z=\"abc\"};"+
        "rez = { pred -> (if pred A B)};"+
        "rez",

        "A=@{x=3; y=3.2f};"+
        "B=@{x=4; z=\"abc\"};"+
        "rez = { pred -> (if pred ({_pred -> A}(notnil pred)) B)};"+
        "rez",

        "    { A?  -> %*       @{   x= nint8} }",
        "[32]{any,3 -> *[17,18]@{_; x= nint8} }",
        "[17,18]","[32]");
  }
  // Load some fields from an unknown struct: area of a rectangle.
  // Since no nil-check, correctly types as needing a not-nil input.
  @Test public void d_struct_05() {
    run("{ sq -> (i* sq.x sq.y) }", // { sq -> sq.x * sq.y }
         "{*@{ x=int64; y=int64; ... } -> %int64 }",
         "[30]{any,3 ->int64 }",
         "[5]","[30]" );
  }
  // Regression test.  Was unexpectedly large type result.  Cut down version of
  // test from marco.servetto@gmail.com.  Looks like it needs some kind of
  // top-level unification with the true->false->true path, and instead the
  // type has an unrolled instance of the 'true' type embedded in the 'false'
  // type.  Bug is actually a core HM algorithm change to handle cycles.
  @Test public void d_struct_06() {
    run("left =     "+
        "  rite = @{n1 = left; v1 = 7 }; "+
        "  @{ n1 = rite; v1 = 7 };"+
        "left"+
        "",
        "A:*@{ n1 = *@{ n1 = A; v1 = 7}; v1 = 7}",
        "PA:*[18]@{_; n1=*[17]@{_; n1=PA; FB:v1=7}; FB}",
        "[17,18]",null);
  }
  // Unexpected restriction on extra fields.
  @Test public void d_struct_07() {
    run("sx = { ignore -> "+
        "  self0=@{ succ = (sx self0)}; "+
        "  self0 "+
        "};"+
        "self1=@{ nope=7; succ = self1 };"+
        "(sx self1)"+
        "",
        "A:*@{ succ=A}",
        "PA:*[17]@{_; succ=PA}",
        "[17]",null);
  }
  @Test public void d_struct_08() { run( "fun = { ptr -> ptr.x }; fun", "{ *@{x=A; ... } -> A }", "[29]{any,3 -> Scalar}","[5]","[29]");  }
  @Test public void d_struct_09() { run(       "{ ptr -> ptr.x }",      "{ *@{x=A; ... } -> A }", "[29]{any,3 -> Scalar}","[5]","[29]");  }

  // Awful flow-type: function can be called from the REPL with any
  // argument type - and the worse case will be an error.
  @Test public void d_struct_10() {
    run("x = { z -> z}; (x { y -> y.u})",
        "{ *@{ u = A; ...} -> A }",
        "[30]{any,3 ->Scalar }",
        "[5]","[30]");
  }


  // Basic field test
  @Test public void d_struct_err_00() { run("5.x", "Missing field x in 5", "Scalar"); }

  // Basic field test.
  @Test public void d_struct_err_01() { run("@{ y =3}.x", "Missing field x in *@{ y = 3}", "Scalar"); }

  // Example from SimpleSub requiring 'x' to be both a struct with field
  // 'v', and also a function type - specifically disallowed in 'aa'.
  @Test public void d_struct_err_02() {
    run("{ x -> y = ( x x.v ); 0}",
        // { x:&[ {A->B}; @{v=A;...} ] -> y = ( x.0 x.1.v ); 0}",
        "{ A:[Cannot unify {B->A} and *@{ v=B;...}] -> C? }",
        "[29]{any,3 ->nil }",
        "[5]","[29,7]");
  }

  // Example from SimpleSub requiring 'x' to be both:
  // - a recursive self-call function from "w = (x x)": $V66:{ $V66 -> V67 } AND
  // - a function which takes a struct with field 'u'
  // The first arg to x is two different kinds of functions, so fails unification.
  @Test public void d_struct_err_04() {
    run("x = w = (x x); { z -> z}; (x { y -> y.u})",
        "A:[Cannot unify { A -> A } and *@{ u = A; ... }]",
        "Scalar",
        "[17]","[29,30,7,31]");
  }

  // Broken from Marco; function 'f' clearly uses 'p2.a' but example 'res1' does not
  // pass in a field 'a'... and still no error.  Fixed.
  @Test public void d_struct_err_05() {
    run("f = { p1 p2 -> (if p2.a p1 p2)}; (f @{a=2} @{b=2.3f})",
         "%*@{ a= Missing field a: int8 }",
         "*[17,18](_)",
         "[17,18]",null);
  }
  // Broken from Marco; function 'f' clearly uses 'p2.a' but example 'res1' does not
  // pass in a field 'a'... and still no error.  Fixed.
  @Test public void d_struct_err_06() {
    run("f = { p1 -> p1.a };"+"(f @{b=2.3f})",
        "Missing field a",
        "Scalar");
  }

  // Broken from Marco; function 'f' clearly uses 'p2.a' but example 'res1' does not
  // pass in a field 'a'... and still no error.  Fixed.
  @Test public void d_struct_err_07() {
    run("f = { p1 p2 -> (if p2.a p1 p2)};"+
        "res1 = (f @{a=2;       c=\"def\"} @{    b=2.3f;d=\"abc\"});"+
        "res2 = (f @{a=2;b=1.2f;c=\"def\"} @{a=3;b=2.3f;d=\"abc\"});"+
        "@{f=f;res1=res1;res2=res2}",

        "*@{ f    =  { A:%*@{ a=B?;... } A -> A };"+
        "    res1 = %*@{ a = Missing field a: int8};"+
        "    res2 = %*@{ a=int8; b=nflt32 }"+
        "}",
        "*[21]@{_; f=[30]{any,4 -> PA:*[5,6,17,18,19,20](_) }; res1=PA; res2=PA}",
        "[5,6,17,18,19,20,21]","[30]");
  }

  @Test public void d_struct_err_08() {
    run( "foo={ ptr -> ptr.fld }; (foo 0)",
         "May be nil",
         "~Scalar");
  }


  // Recursive linked-list discovery, with no end clause.  Since this code has
  // no exit (it is an infinite loop, endlessly reading from an infinite input
  // and writing an infinite output), gcp gets a cyclic approximation.
  @Test public void e_recur_struct_00() {
    run("map = { fcn lst -> @{ n1 = (map fcn lst.n0); v1 = (fcn lst.v0) } }; map",
        "{ { A -> B } C:*@{ n0 = C; v0 = A; ...} -> D:*@{ n1 = D; v1 = B} }",
        "[29]{any,4 ->PA:*[17]@{_; n1=PA; v1=Scalar} }",
        "[5,17]","[8,29]");
  }

  // Recursive linked-list discovery, with nil.  Note that the output memory
  // has the output memory alias, but not the input memory alias (which must be
  // made before calling 'map').
  @Test public void e_recur_struct_01() {
    run("map = { fcn lst -> (if lst @{ n1=(map fcn lst.n0); v1=(fcn lst.v0) } 0) }; map",
        "map = { fcn lst -> (if lst ({_lst -> @{ n1=(map fcn _lst.n0); v1=(fcn _lst.v0) }} (notnil lst)) 0) }; map",
        "{ { A -> B } C:*@{ n0 = C; v0 = A; ...}? -> D:%*@{ n1 = D; v1 = B}? }",null,
        "[32]{any,4 ->PA:*[17]@{_; n1=PA; v1=Scalar}? }",null,
        "[5,17]","[8,32]");
  }
  // Recursive linked-list discovery, applied
  @Test public void e_recur_struct_02() {
    run("map = { fcn lst -> (if lst @{ n1 = (map fcn lst.n0); v1 = (fcn lst.v0) } 0) }; (map dec @{n0 = 0; v0 = 5})",
        "map = { fcn lst -> (if lst ({_lst -> @{ n1 = (map fcn _lst.n0); v1 = (fcn _lst.v0) }} (notnil lst)) 0) }; (map dec @{n0 = 0; v0 = 5})",
        "A:%*@{ n1 = A; v1 = %int64 }?",
        "PA:*[17]@{_; n1=PA; v1=4}?",
        "[17]",null);
  }
  // Need to see if a map call, inlined a few times, 'rolls up'.  Sometimes
  // rolls up, sometimes not; depends on worklist visitation order.
  @Test public void e_recur_struct_03() {
    run("map = { lst -> (if lst @{ n1= arg= lst.n0; (if arg @{ n1=(map arg.n0); v1=(str arg.v0)} 0); v1=(str lst.v0) } 0) }; map",
        "map = { lst -> (if lst ({_lst -> @{ n1= arg= _lst.n0; (if arg ({_arg -> @{ n1=(map _arg.n0); v1=(str _arg.v0)}} (notnil arg)) 0); v1=(str _lst.v0) }} (notnil lst)) 0) }; map",
        "{ A:*@{ n0 = *@{ n0 = A; v0 = int64; ...}?; v0 = int64; ...}? -> B:%*@{ n1 = %*@{ n1 = B; v1 = %*str:(int8)}?; v1 = %*str:(int8)}? }",
        "[37]{any,3 ->PA:*[18]@{_; n1=*[17]@{_; n1=PA; FB:v1=*[4]str:(int8)}?; FB}? }",
        "[5,17,18]","[37]" );
  }
  // Checking an AA example
  @Test public void e_recur_struct_04() {
    run("prod = { x -> (if x (i* (prod x.n) x.v) 1)};"+
        "(prod @{n= @{n=0; v=3}; v=2})",
        "prod = { x -> (if x ({_x -> (i* (prod _x.n) _x.v)}(notnil x)) 1)};"+
        "(prod @{n= @{n=0; v=3}; v=2})",
        "%int64", "int64",
        null, null);
  }
  // Example from TestParse.test15:
  //   map={lst fcn -> lst ? fcn lst.1};
  //   in_int=(0,2);"+       // List of ints
  //   in_str=(0,"abc");" +  // List of strings
  //   out_str = map(in_int,str:{int->str});"+        // Map over ints with int->str  conversion, returning a list of strings
  //   out_bool= map(in_str,{str -> str==\"abc\"});"+ // Map over strs with str->bool conversion, returning a list of bools
  //   (out_str,out_bool)",
  @Test public void e_recur_struct_05() {
    run("""
map={lst fcn -> (fcn lst.y) };
in_int=@{ x=0; y=2};
in_str=@{ x=0; y="abc"};
out_str = (map in_int str);
out_bool= (map in_str { xstr -> (eq xstr "def")});
(pair out_str out_bool)
""",
        null,
        "*(%*str:(int8),%int64)",
        "*(%*str:(int8),%int64)",
        "*[19](_, *[4]str:(int8), int64)",
        "*[19](_, %[4][]?, %[4][]?)",
        "[19]",null);
  }
  @Test public void e_recur_struct_06() {
    run("""
all = @{
  is_even = { dsp n -> (if (eq0 n) 0 (dsp.is_odd  dsp (dec n)))};
  is_odd  = { dsp n -> (if (eq0 n) 1 (dsp.is_even dsp (dec n)))}
};
{ x -> (all.is_even all x)}
""",
         "{int64 -> %int64}", "[37]{any,3 ->int1 }",
         null,"[37]");
  }
  @Test public void e_recur_struct_07() {
    run("dsp = @{  id = { dsp n -> n}}; (pair (dsp.id dsp 3) (dsp.id dsp \"abc\"))",
        null,
        "*( 3, *str:(97))",
        "*( 3, *str:(97))",
        "*[18](_, 3 , *[4]str:(97))",
        "*[18](_, %[4][], %[4][])",
        "[18]",null);
  }
  // Test example from AA with expanded ints
  @Test public void e_recur_struct_08() {
    run("int = { i -> @{ add={ x y -> (int (+ x.i y.i))}; i=i } }; x=(int 3); y=(int 4); (x.add x y)",
        """
A:*@{
  add={
     B:*@{ add={ *@{i=int64;...} *@{i=int64;...} -> B };i=%int64}
     C:*@{ add={ *@{i=int64;...} *@{i=int64;...} -> C };i=%int64}
     -> A};
  i=%int64
}
""",
         "PA:*[17]@{_; add=[30]{any,4 -> PA }; i=int64}",
        "[5,6,17]","[30]");
  }

  // Recursive structs.  First: closed structs list available fields;
  // unification produces the set intersection.
  @Test public void e_recur_struct_09() {
    run("{ p -> (if p @{x=3;y=4} @{y=6;z=\"abc\"})}",
        "{ p -> (if p ({_p -> @{x=3;y=4}} (notnil p)) @{y=6;z=\"abc\"})}",
        "{A? -> %*@{ y = nint8 } }",
        "[32]{any,3 ->*[17,18]@{_; y=nint8} }",
        "[17,18]","[32]");
  }
  // Recursive structs.  Next: open structs list required fields;
  // unification produces the set union.
  @Test public void e_recur_struct_10() {
    run("{ p rec -> (if p rec.x rec.y)}",
        "{ p rec -> (if p ({_p -> rec.x} (notnil p)) rec.y)}",
        "{ A? *@{x=B;y=B;...} -> B }",
        "[32]{any,4 ->Scalar }",
        "[5]","[32]");
  }
  // Recursive structs.  Next: passing extra fields; they are passed along
  // here.  Required fields are fresh every time.
  @Test public void e_recur_struct_11() {
    run("fun = { rec -> (pair rec rec.x)}; (pair (fun @{x=3;y=4}) (fun @{x=\"abc\";z=2.1f}))",
         "*(*(*@{x=3;y=4},3), *(*@{x=A:*str:(97);z=2.1f},A))",
         "*[18](_, 0=PA:*[17](_, *[19,20]@{_; x=%[4][]}, %[4][]), 1=PA)",
        "[17,18,19,20]",null);
  }
  // Recursive structs.  Next: passing extra fields, but the function requires
  // the structures to be the same.  Extra fields dropped.  Unify required fields.
  @Test public void e_recur_struct_12() {
    run("({fun -> "+
        "   (pair (fun @{x=3; y=4   } )"+    // available {x,y}
        "         (fun @{x=4; z=2.1f} )  )"+ // available {x,z}
        "  } { rec -> (pair rec rec.x) } )", // required  {x}
        "*(A:*(*@{x=nint8},nint8),A)",
        "*[17](_, 0=PA:*[20](_, *[18,19]@{_; x=nint8}, nint8), 1=PA)",
        "[17,18,19,20]",null);
  }
  // Recursive structs.
  @Test public void e_recur_struct_13() {
    run("""
fun = { ff ->
  @{ f = ff;
     mul = { y -> (fun (f* ff y.f)) }
   }
};
(fun 1.2f)
""",  // required {f} in inner, available {f,mul} in outer
        "A:*@{f=%flt64;mul={*@{f=flt64;...}->A}}", // required {f} in inner, available {f,mul} in outer
        "PA:*[17]@{_; f=flt64; mul=[30]{any,3 ->PA }}",
        "[5,17]","[30]");
  }

  // Recursive structs, with deeper expressions.  The type expands with
  // expression depth.
  @Test public void e_recur_struct_14() {
    run("""
fun = { ff ->
  @{ f = ff;
     mul = { y -> (fun (f* ff y.f)) }
   }
};
con12=(fun 1.2f);
(con12.mul con12)
""",                // required {f} in inner, available {f,mul} in outer,middle
        "A:*@{f=%flt64;mul={B:*@{f=%flt64;mul={*@{f=flt64;...}->B}}->A}}", // required {f} in inner, available {f,mul} in middle,outer
        "PA:*[17]@{_; f=flt64; mul=[30]{any,3 ->PA }}",
        "[5,17]","[30]");
  }

  // Recursive structs.  Next: passing extra fields, but the function requires
  // the structures to be the same.  Extra fields dropped.  Unify required fields.
  @Test public void e_recur_struct_err_00() {
    run("({fun -> "+
        "   (pair (fun @{x=3      ;y=4   } )"+    // available {x,y}
        "         (fun @{x=\"abc\";z=2.1f} )  )"+ // available {x,z}
        "  } { rec -> (pair rec rec.x) } )",      // required  {x}
        "*(A:*(*@{x=B:[Cannot unify 3 and *str:(97)]},B),A)",
        "*[17](_, 0=PA:*[20](_, *[18,19]@{_; x=%[4][]}, %[4][]), 1=PA)",
        "[17,18,19,20]","[]");
  }


  // GCP can help HMT
  @Test public void f_gcp_hmt_00() {
    run("pred = 0; s1 = @{ x=\"abc\" }; s2 = @{ y=3.4f }; (if pred s1 s2).y",
        "pred = 0; s1 = @{ x=\"abc\" }; s2 = @{ y=3.4f }; (if pred ({_pred -> s1}(notnil pred)) s2).y",
        "3.4f", "Missing field y in %*(): 3.4f",
        "3.4f", "3.4f",
        null,null);
  }
  // The z-merge is ignored; the last s2 is a fresh (unmerged) copy.
  @Test public void f_gcp_hmt_01() {
    run("pred = 0; s1 = @{ x=\"abc\" }; s2 = @{ y=3.4f }; z = (if pred s1 s2).x; s2.y",
        "pred = 0; s1 = @{ x=\"abc\" }; s2 = @{ y=3.4f }; z = (if pred ({_pred -> s1}(notnil pred)) s2).x; s2.y",
        "3.4f","3.4f",null,null);
  }
  @Test public void f_gcp_hmt_02() {
    run("fun = (if (isempty \"abc\") {x->x} {x->1.2f}); (fun @{})",
        "fun = (if (isempty \"abc\") {x->x} {x->1.2f}); (fun @{})",
        "1.2f", "[Cannot unify 1.2f and *()]",
        "1.2f","1.2f",
        null,null);

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
    """
id = {x -> x};
loop = { name cnt ->
  (if cnt
    ({_cnt -> (loop
       fltfun = (if name ({_name -> id}(notnil name)) {x->3});
       (fltfun "abc")
       (dec _cnt)
     )} (notnil cnt))
     name
   )
};
(loop "def" (id 2))
""",
        "%*str:(nint8)?",     // Both HM and GCP
        "%[Cannot unify int64 and *str:(nint8)?]", // HM alone cannot do this one
        "*[4]str:(nint8)",    // Both HM and GCP
        "%[4][]",             // GCP alone gets a very weak answer
        null,null);
  }
  // Basic uplifting after check
  @Test public void f_gcp_hmt_04() {
    run("{ pred -> tmp=(if pred @{x=3} 0); (if tmp tmp.x 4) }",
        "{ pred -> tmp=(if pred ({_pred -> @{x=3}} (notnil pred)) 0); (if tmp ({_tmp -> _tmp.x}(notnil tmp)) 4) }",
        "{ A? -> %int64 }", "[35]{any,3 ->nint8 }",null,"[35]");
  }
  // map is parametric in nil-ness
  @Test public void f_gcp_hmt_05() {
    run("""
{ pred ->
  map = { fun x -> (fun x) };
  (pair (map {str0 ->          str0.x   }          @{x = 3}   )
        (map {str1 -> (if str1 str1.x 4)} (if pred @{x = 5} 0))
  )
}
""",
    """
{ pred ->
  map = { fun x -> (fun x) };
  (pair (map {str0 ->          str0.x   }          @{x = 3}   )
        (map {str1 -> (if str1 ({_str1 -> _str1.x} (notnil str1)) 4)} (if pred ({_pred -> @{x = 5}}(notnil pred)) 0))
  )
}
""",
         "{ A? -> *( 3, %int64) }",
         "{ A? -> *( 3, %int64) }",
         "[39]{any,3 ->*[17](_, nint8, nint8) }",
         "[39]{any,3 ->*[17](_, nint8, nint8) }",
         "[17]","[39]");
  }
  // Simple nil/default test; takes a nilable but does not return one.
  @Test public void f_gcp_hmt_06() {
    run( "{ x y -> (if x x y) }",
         "{ x y -> (if x ({_x -> _x} (notnil x)) y) }",
         "{ A? A -> A }", "[32]{any,4 ->Scalar }",
         null,"[32]");
  }
  // Regression test; double nested.  Failed to unify x and y.
  @Test public void f_gcp_hmt_07() {
    run( "{ x y -> (if x (if x x y) y) }",
         "{ x y -> (if x ({_x -> (if _x ({_x -> _x}(notnil _x)) y)}(notnil x)) y) }",
         "{ A? A -> A }", "[35]{any,4 ->Scalar }",
         null,"[35]");
  }
  @Test public void f_gcp_hmt_08() {
    run("total_size = { a as ->" +  // Total_size takes an 'a' and a list of 'as'
        "  (if as "+                // If list is not empty then
        "      (+ a.size "+         // Add the size of 'a' to
        "         (total_size as.val as.next))" + // the size of the rest of the list
        "      a.size"+             // Else the list is empty, just take the a.size
        "  )"+                      // End of (if as...)
        "};" +                      // End of total_size={...}
        "total_size",               // What is this type?

        "total_size = { a as ->" +  // Total_size takes an 'a' and a list of 'as'
        "  (if as "+
        "      ({_as -> (+ a.size "+
        "         (total_size _as.val _as.next))} (notnil as))" +
        "      a.size"+
        "  )"+                      // End of (if as...)
        "};" +                      // End of total_size={...}
        "total_size",               // What is this type?

        "{ A:*@{ size = %int64; ...} B:*@{ next = B; val = A; ...}? -> %int64 }",
        "{ A:*@{ size = %int64; ...} B:*@{ next = B; val = A; ...}? -> %int64 }",
        "[33]{any,4 ->int64 }",
        "[33]{any,4 ->int64 }",
        "[5,6]","[33]");
  }


  // Basic nil test
  @Test public void f_gcp_hmt_err_00() { run("0.x", "May be nil when loading field x", "~Scalar"); }

  // Basic nil test
  @Test public void f_gcp_hmt_err_01() {
    run("{ pred -> (if pred @{x=3} 0).x}",
        "{ pred -> (if pred ({ _pred -> @{x=3}}(notnil pred)) 0).x}",
        "{ A? -> May be nil when loading field x: 3 }", "[32]{any,3 ->3 }",
        null,"[32]"  );
  }

  // map is parametric in nil-ness.  Verify still nil-checking.
  @Test public void f_gcp_hmt_err_02() {
    run("""
{ pred ->
  map = { fun x -> (fun x) };
  (pair (map {str0 ->          str0.x   }          @{x = 3}   )
        (map {str1 ->          str1.x   } (if pred @{x = 5} 0))
  )
}
""",
        """
{ pred ->
  map = { fun x -> (fun x) };
  (pair (map {str0 ->          str0.x   }          @{x = 3}   )
        (map {str1 ->          str1.x   } (if pred ({_pred -> @{x = 5}}(notnil pred)) 0))
  )
}
""",
         "{ A? -> May be nil:*( 3, May be nil when loading field x: 5 ) }",
         "[36]{any,3 ->*[17](_, nint8, nint8) }",
         "[17]","[36]");
  }


  // Simple overload def.  Since no uses, no Field to resolve.
  @Test public void g_overload_00() {
    run("(pair"                  +  // Define a pair of fcns
        "  { x -> (i* x 2   ) }"+  // Arg is 'int'
        "  { x -> (f* x 3.0f) }"+  // Arg is 'flt'
        ")",
        "*( {int64 -> %int64}, {flt64 -> %flt64} )",
        "*[17](_, [31]{any,3 -> int64 }, [33]{any,3 -> flt64 })",
        "[17]","[31,33]"
        );
  }

  // Simple overloaded function test.
  // Insert Fields for all 'f' uses, but some or all may go away.
  @Test public void g_overload_01() {
    run("f = (pair"             +  // Define overloaded fcns 'f'
        "  { x -> (i* x 2   ) }"+  // Arg is 'int'
        "  { x -> (f* x 3.0f) }"+  // Arg is 'flt'
        ");"+
        "(pair (f._ 2) (f._ 1.2f))",// Call with different args
        "f = (pair"              +  // Define overloaded fcns 'f'
        "  { x -> (i* x 2   ) }" +  // Arg is 'int'
        "  { x -> (f* x 3.0f) } "+  // Arg is 'flt'
        ");"+
        "(pair (f.0 2) (f.1 1.2f))",    // Call with different args
        "*(%int64,%flt64)", "*(%int64,%flt64)",
        "*[18](_, 4,3.6000001f)", "*[18](_, 4, 3.6000001f)",
        "[18]",null);
  }

  @Test public void g_overload_02() {
    run("""
{ pred ->
  fx = (pair (if pred { x -> (i* x 2)} { x -> (i* x 3)})
             { x -> (f* x 0.5f) }
        );
  (pair (fx._ 2) (fx._ 1.2f))
}
""",
        """
{ pred ->
  fx = (pair (if pred ({_pred -> { x -> (i* x 2)}}(notnil pred)) { x -> (i* x 3)})
          { x -> (f* x 0.5f) }
        );
  (pair (fx.0 2) (fx.1 1.2f))
}
""",
        "{ A? -> *(%int64,%flt64) }",
        "{ A? -> *(%int64,%flt64) }",
        "[40]{any,3 -> *[18](_, nint8, 0.6f) }",
        "[40]{any,3 -> *[18](_, nint8, 0.6f) }",
        "[18]","[40]");
  }

  // Test overload as union of primitives
  @Test public void g_overload_03() {
    run("red = (pair 123 \"red\" ); (pair (dec red._) (isempty red._))",
        "red = (pair 123 \"red\" ); (pair (dec red.0) (isempty red.1))",
        "*(%int64,%int64)",
        "*(%int64,%int64)",
        "*[18](_, 122, nil)",
        "*[18](_, 122, nil)",
        "[18]",null);
  }

  // Test overload as union of primitives.  Merge of 2 unrelated overloads
  // forces resolution at the 'if'; hence 'red' is typed as either 'int' or
  // 'str' and one of '(dec red)' or '(isempty red)' must fail.
  @Test public void g_overload_04() {
    run("{ pred -> c =(if pred            (pair 123 \"red\" )                (pair 456  \"blue\" )); (pair (dec c._) (isempty c._))}",
        "{ pred -> c =(if pred ({_pred -> (pair 123 \"red\" )}(notnil pred)) (pair 456  \"blue\" )); (pair (dec c.0) (isempty c.1))}",
        "{A? -> *(%int64,%int64) }",
        "{A? -> *(%int64,%int64) }",
        "[37]{any,3 -> *[19](_, int64, nil) }",
        "[37]{any,3 -> *[19](_, int64, nil) }",
        "[19]","[37]");
  }

  // Explicit overload argument
  @Test public void g_overload_05() {
    run("{ x -> (x._ x._.v)}",
        "{ x -> (x._ x._.v)}",
        "{*@{&17 = %Unresolved field &17: { A:Unresolvedfield&19 -> B:Unresolvedfield&17}; &19 = %Unresolvedfield&19:*@{v=A;...};...}->B}",
        "[29]{any,3 -> Scalar }",
        "[5]","[29]");
  }

  @Test public void g_overload_06() {
    run("((pair 1 {x->x})._ 2.1f)",
        "((pair 1 {x->x}).1 2.1f)",
        "2.1f","2.1f",
        null,null );
  }

  // No overload 
  @Test public void g_overload_07() {
    run("{ ptr -> (ptr.x ptr.x) }",
        "{ *@{x= A:{ A-> B}; ...} -> B }",
        "[29]{any,3 -> Scalar }",
        "[5]","[29]");
  }

  // Field order specified
  @Test public void g_overload_08() {
    run("({ ptr -> (ptr._.x ptr._.x) } (pair @{x=3} @{x=str}) )",
        "({ ptr -> (ptr.1.x ptr.0.x) } (pair @{x=3} @{x=str}) )",
        "%*str:(int8)",
        "*[4]str:(51)",
        null,
        null);
  }
  // Field order under-specified, so ambiguous
  @Test public void g_overload_err_08() {
    run("{ ptr -> (ptr._.x ptr._.x) }",
        "{ ptr -> (ptr._.x ptr._.x) }",
        "{*@{&17 = %Unresolvedfield &17: *@{ x = Unresolvedfield&17: { A:Unresolvedfield&20 -> B:Unresolvedfield&17};...};&20 = %Unresolvedfield&20:*@{x=A;...};...}->B}",
        "[29]{any,3 -> Scalar }",
        "[5]", "[29]");
  }

  // Field order specified
  @Test public void g_overload_09() {
    run("({ ptr -> (ptr.x.1 3) } @{x=(pair 3 str)})",
        "({ ptr -> (ptr.x.1 3) } @{x=(pair 3 str)})",
        "%*str:(int8)",
        "*[4]str:(51)",
        null,null);
  }

  // Field order under-specified, so ambiguous
  @Test public void g_overload_err_09() {
    run("{ ptr -> (ptr.x._ ptr.x._) }",
        "{ ptr -> (ptr.x._ ptr.x._) }",
        "{*@{x=*@{&18=%Unresolvedfield&18:{A:%Unresolvedfield&21->B:Unresolvedfield&18};&21=A;...};...}->B}",
        "[29]{any,3 -> ~Scalar }",
        "[5]","[29]");
  }

  // Test overload as union of primitives.  Merge of 2 related overloads stalls
  // resolution until use at 'dec' and 'isempty'.  Each use resolves separately.
  @Test public void g_overload_10() {
    run("color = { hex name -> (pair hex name )};"+
        "red  = (color 123 \"red\" );"+
        "blue = (color 456 \"blue\");"+
        "{ pred -> c =(if pred red blue); (pair (dec c._) (isempty c._))}",

        "color = { hex name -> (pair hex name )};"+
        "red  = (color 123 \"red\" );"+
        "blue = (color 456 \"blue\");"+
        "{ pred -> c =(if pred ({_pred -> red}(notnil pred)) blue); (pair (dec c.0) (isempty c.1))}",

        "{ A? -> *(%int64,%int64) }",
        "{ A? -> *(%int64,%int64) }",
        "[37]{any,3 -> *[18](_, int64, nil) }",
        "[37]{any,3 -> *[18](_, int64, nil) }",
        "[18]","[37]");
  }

  // Test overload as union of primitives.  Overload resolution before
  // calling 'fun'.
  @Test public void g_overload_11() {
    run("fun = { a0 -> (dec a0) }; "  + // a0 is an int
        "(pair (fun (pair   123 \"abc\"        )._)" + // Correct overload is 0x123
        "      (fun (triple \"def\" @{x=1} 456 )._)" + // Correct overload is 0x456
        ")",

        "fun = { a0 -> (dec a0) }; "  + // a0 is an int
        "(pair (fun (pair   123 \"abc\" )       .0)" + // Correct overload is 0x123
        "      (fun (triple \"def\" @{x=1} 456 ).2)" + // Correct overload is 0x456
        ")",

        "*(%int64,%int64)",
        "*[17](_, int64, int64)",
        "[17]",null);
  }

  // 'lite' needs to be told to take an overload with syntax
  @Test public void g_overload_12() {
    run("color = { hex name -> (pair hex name )};"+
        "red  = (color 123 \"red\" );"+
        "blue = (color 456 \"blue\");"+
        "lite = { c -> (color (dec c._) (isempty c._))};"+ // Should be "(color (sub c 0x111) (cat "light" c))"
        "(pair (lite red) (lite blue))",
        
        "color = { hex name -> (pair hex name )};"+
        "red  = (color 123 \"red\" );"+
        "blue = (color 456 \"blue\");"+
        "lite = { c -> (color (dec c.0) (isempty c.1))};"+ // Should be "(color (sub c 0x111) (cat "light" c))"
        "(pair (lite red) (lite blue))",

        "*( *(%int64,%int64), *(%int64,%int64))",
        "*( *(%int64,%int64), *(%int64,%int64))",
        "*[18](_, 0=PA:*[17](_, int64, *[4]str:(nint8)?), 1=PA)",
        "*[18](_, 0=PA:*[17](_, int64, *[4]str:(nint8)?), 1=PA)",
        "[17,18]",null);
  }
  // Test case here is trying to get HM to do some overload resolution.
  // Without, many simple int/flt tests in main AA using HM alone fail to find
  // a useful type.
  @Test public void g_overload_13() {
    run("""
fwrap = { ff ->
  @{ _*_ = (pair
       { y -> (fwrap (f* ff (i2f y.i))) }
       { y -> (fwrap (f* ff      y.f )) }
     );
     f = ff
   }
};
iwrap = { ii ->
  @{ _*_ = (pair
       { y -> (iwrap (i*      ii  y.i)) }
       { y -> (fwrap (f* (i2f ii) y.f)) }
     );
     i = ii;
   }
};

con2   = (iwrap 2   );
con2_1 = (fwrap 2.1f);
(con2_1._*_._ con2_1)
""",
    """
fwrap = { ff ->
  @{ _*_ = (pair
       { y -> (fwrap (f* ff (i2f y.i))) }
       { y -> (fwrap (f* ff      y.f )) }
     );
     f = ff
   }
};
iwrap = { ii ->
  @{ _*_ = (pair
       { y -> (iwrap (i*      ii  y.i)) }
       { y -> (fwrap (f* (i2f ii) y.f)) }
     );
     i = ii
   }
};

con2   = (iwrap 2   );
con2_1 = (fwrap 2.1f);
(con2_1._*_.1 con2_1)
""",
        "A:*@{_*_=*( {*@{i=int64;...}->A}, {B:*@{_*_=*( {*@{i=int64;...}->B}, {*@{f=flt64;...}->B}); f=%flt64}->A});f=%flt64}",
        "PA:*[18]@{_; _*_=*[17](_, [32]{any,3 -> PA }, [34]{any,3 -> PA }); f=flt64}",
        "[5,6,17,18]","[32,34]");
  }

  // Recursive structs.  More like what main AA will do with wrapped primitives.
  @Test public void g_overload_14() {
    String hm_rez = "*("+
      "A:*@{_*_=*({B:*@{_*_=*({*@{i=int64;...}->B},{*@{f=flt64;...}->C:*@{_*_=*({*@{i=int64;...}->C},{*@{f=flt64;...}->C});f=%flt64}});i=%int64}->A},{*@{f=flt64;...}->A});f=%flt64},"+
      "D:*@{_*_=*({E:*@{_*_=*({*@{i=int64;...}->E},{*@{f=flt64;...}->F:*@{_*_=*({*@{i=int64;...}->F},{*@{f=flt64;...}->F});f=%flt64}});i=%int64}->D},{*@{f=flt64;...}->G:*@{_*_=*({*@{i=int64;...}->G},{*@{f=flt64;...}->G});f=%flt64}});i=%int64},"+
      "H:*@{_*_=*({*@{i=int64;...}->H},{I:*@{_*_=*({*@{i=int64;...}->I},{*@{f=flt64;...}->I});f=%flt64}->H});f=%flt64}"+
      ")";

            run("""
fwrap = { ff ->
  @{ _*_ = (pair
       { y -> (fwrap (f* ff (i2f y.i))) }
       { y -> (fwrap (f* ff      y.f)) }
     );
     f = ff
   }
};
iwrap = { ii ->
  @{ _*_ = (pair
       { y -> (iwrap (i*      ii  y.i)) }
       { y -> (fwrap (f* (i2f ii) y.f)) }
     );
     i = ii
   }
};

con2   = (iwrap 2  );
con2_1 = (fwrap 2.1f);
mul2 = { x -> (x._*_._ con2)};
(triple (mul2 con2_1)  (con2._*_.0 con2) (con2_1._*_.1 con2_1))
""",
        """
fwrap = { ff ->
  @{ _*_ = (pair
       { y -> (fwrap (f* ff (i2f y.i))) }
       { y -> (fwrap (f* ff      y.f )) }
     );
     f = ff
   }
};
iwrap = { ii ->
  @{ _*_ = (pair
       { y -> (iwrap (i*      ii  y.i)) }
       { y -> (fwrap (f* (i2f ii) y.f)) }
     );
     i = ii
   }
};

con2   = (iwrap 2  );
con2_1 = (fwrap 2.1f);
mul2 = { x -> (x._*_.0 con2)};
(triple (mul2 con2_1)  (con2._*_.0 con2) (con2_1._*_.1 con2_1))
""",
        hm_rez,
        hm_rez,
        "*[21](_, 0=PA:*[18]@{_; _*_=*[17](_, [32]{any,3 -> PA }, [34]{any,3 -> PA }); f=flt64}, 1=PB:*[20]@{_; _*_=*[19](_, [38]{any,3 -> PB }, [41]{any,3 -> PA }); i=int64}, 2=PA)",
        "*[21](_, 0=PA:*[18]@{_; _*_=*[17](_, [32]{any,3 -> PA }, [34]{any,3 -> PA }); f=flt64}, 1=PB:*[20]@{_; _*_=*[19](_, [38]{any,3 -> PB }, [41]{any,3 -> PA }); i=int64}, 2=PA)",
        "[5,6,7,8,17,18,19,20,21]", "[32,34,38,41]");
  }

  // Recursive structs, in a loop.  Test of recursive int wrapper type ("occurs
  // check") in a loop.
  @Test public void g_overload_15() {
    run("""
fwrap = { ff ->
  @{ f = ff;
     mul = (pair
       { y -> (fwrap (f* ff (i2f y.i))) }
       { y -> (fwrap (f* ff      y.f )) }
     );
   }
};

iwrap = { ii ->
  @{ i = ii;
     is0 = (eq0 ii);
     mul = (pair
       { y -> (iwrap (i*      ii  y.i)) }
       { y -> (fwrap (f* (i2f ii) y.f)) }
     );
     sub1= (iwrap (dec ii))
   }
};

c1 = (iwrap 1);
c5 = (iwrap 5);

fact = { n -> (if n.is0 c1 (n.mul._ (fact n.sub1))) };

(fact c5)
""",
        """
fwrap = { ff ->
  @{ f = ff;
     mul = (pair
       { y -> (fwrap (f* ff (i2f y.i))) }
       { y -> (fwrap (f* ff      y.f )) }
     )
   }
};

iwrap = { ii ->
  @{ i = ii;
     is0 = (eq0 ii);
     mul = (pair
       { y -> (iwrap (i*      ii  y.i)) }
       { y -> (fwrap (f* (i2f ii) y.f)) }
     );
     sub1= (iwrap (dec ii))
   }
};

c1 = (iwrap 1);
c5 = (iwrap 5);

fact = { n -> (if n.is0 c1 (n.mul.0 (fact n.sub1))) };

(fact c5)
""",
        "A:%*@{i=%int64;is0=%int64;mul=*({A->A},{*@{f=flt64;...}->B:*@{f=%flt64;mul=*({*@{i=int64;...}->B},{*@{f=flt64;...}->B})}});sub1=A}",
        "A:%*@{i=%int64;is0=%int64;mul=*({A->A},{*@{f=flt64;...}->B:*@{f=%flt64;mul=*({*@{i=int64;...}->B},{*@{f=flt64;...}->B})}});sub1=A}",
        "PA:*[20]@{_; i=int64; is0=int1; mul=*[19](_, [39]{any,3 -> PA }, [42]{any,3 -> PB:*[18]@{_; f=flt64; mul=*[17](_, [32]{any,3 -> PB }, [34]{any,3 -> PB })} }); sub1=PA}",

        "PA:*[20]@{_; i=int64; is0=int1; mul=*[19](_, [39]{any,3 -> PA }, [42]{any,3 -> PB:*[18]@{_; f=flt64; mul=*[17](_, [32]{any,3 -> PB }, [34]{any,3 -> PB })} }); sub1=PA}",
        "[5,6,7,8,17,18,19,20]","[32,34,39,42]");
  }

  // Ambiguous overload, {int->int}, cannot select.
  // Parent of overload is Apply, so
  @Test public void g_overload_err_00() {
    run("((pair"              +  // Define overloaded fcns
        "   { x -> (i* x 2) }"+  // Arg is 'int'
        "   { x -> (i* x 3) }"+  // Arg is 'int'
        "  )._ 4)",              // Error, ambiguous
        "((pair { x -> (i* x 2 ) } { x -> (i* x 3 ) } )._ 4)",
        "Unresolved field &28",
        "nint8",
        null,null
      );
  }
  // Wrong args for all overloads
  @Test public void g_overload_err_01() {
    run("((pair { x y -> (i* x y) } { x y z -> (i* y z) })._ 4)",
        "Unresolved field &28",
        "~int64");
  }
  // Mixing unrelated overloads
  @Test public void g_overload_err_02() {
    run("""
fx = (pair { x -> 3     } { y -> "abc" });
fy = (pair { z -> "def" } { a -> 4     });
fz = (if (rand 2) fx fy);
(isempty (fz._ 1.2f))
""",
         "%Unresolved field &37 [Cannot unify int64 and *str:(int8) ]",
         "int1",
         null,null);
  }

  // Another ambiguous field layout
  @Test public void g_overload_err_03() {
    run("{ x -> (x._ x._.v)}",
        "{ x -> (x._ x._.v )}",
        "{*@{ &17 = %Unresolved field &17: { A:Unresolved field &19 -> B:Unresolved field &17 }; &19 = %Unresolvedfield &19: *@{v=A;...};...}->B}",
        "[29]{any,3 ->Scalar }",
        "[5]","[29]");
  }



  // A List, effectively a List<Object>.  Make a list with
  // mixed ints and strings.
  @Test public void h_variance_00() {
    String  list = "List = { lst val -> @{ nxt=lst; val=val }};";
    String  size = "size = { lst -> (if lst            (+ (size  lst.nxt) 1)                  0) };";
    String rsize = "size = { lst -> (if lst ({ _lst -> (+ (size _lst.nxt) 1) } ( notnil lst)) 0) };";
    String prog = """
list_int0 = (List 0 17);
list_int1 = (List list_int0 19);
list_int2 = (List list_int1 "abc");
(pair (size list_int2) list_int2)
""";
    run(list +  size + prog,
        list + rsize + prog,
        // Note that the H-M type is completely unrolled, same as the code
        "*( %int64, *@{ nxt=*@{ nxt=*@{ nxt=A?; val=17}; val=19}; val=*str:(97)})",
        "*[18](_, int64, 1=PA:*[17]@{_; nxt=PA; val=%[4][]})",
        "[17,18]",null);
  }

  // A List of Ints, forced by use as an Int by "(dec val)'.
  @Test public void h_variance_01() {
    String prog = """
ListInt = { lst val ->
    dummy = (dec val);
    @{ nxt=lst; val=val }
};
list_int0 = (ListInt 0 17);
list_int1 = (ListInt list_int0 "abc");
list_int1
""";
    // Note that the H-M type is completely unrolled, same as the code
    run(prog,
        prog,
        "*@{nxt=*@{nxt=A?;val=int64};val=[Cannot unify int64 and *str:(97)]}",
        "*@{nxt=*@{nxt=A?;val=int64};val=[Cannot unify int64 and *str:(97)]}",
        "PA:*[17]@{_; nxt=PA; val=%[4][]}",
        "PA:*[17]@{_; nxt=PA; val=%[4][]}",
        "[17]",null);
  }

  // Core aa for computing size of linked list.  Only cares that 'lst' has a
  // next field pointing to more things with more next fields.
  static final String  SIZE = "_size = { lst -> (if lst            (+ 1 (_size  lst.next))                  0) };";
  static final String RSIZE = "_size = { lst -> (if lst ({ _lst -> (+ 1 (_size _lst.next)) } ( notnil lst)) 0) };";

  static final String LIST = """
// Constructor for a typed linked-list.  Constructor is passed in a
// type-verifier function: a function which will not type if elements are the
// wrong type.
List = { generic ->
  // Hidden internal function to make a new List container
  list = { head ->
    // Structure for the List container
    @{
       append = { value ->
         ignore = (generic value); // Type check element
         // The list entries have only a next and value field
         (list @{next=head; value=value})
       };
       head = head;
       size = { -> (_size head) }
    }
  };

  // This is the constructor function.  Call with no args to make a new
  // zero-length typed list.  Same as "new List<T>()"
  { -> (list 0)}
};

ListInt = (List {value -> (dec     value)}); // Confirm elements are ints   ; same as "new List<int>()"
ListStr = (List {value -> (isempty value)}); // Confirm elements are strings; same as "new List<String>()"
""";
    
  // A generic List, which is given a way to force the values to be a specific
  // type.
  @Test public void h_variance_02() {
    String prog = """
list_int1 = ((ListInt).append 17   );
list_str1 = ((ListStr).append "red");
(pair list_int1 list_str1)
""";
    // Note that the H-M type is completely unrolled, same as the code
    run(SIZE  + LIST + prog,
        RSIZE + LIST + prog,
        "*( A:*@{append = {  int64      ->A}; head = B:*@{next=B; value=int64}?; size = {->%int64} } ,"+
        "   C:*@{append = {D:*str:(int8)->C}; head = E:*@{next=E; value=D    }?; size = {->%int64} } )",
        "*[19](_, 0=PA:*[18]@{_; append=[34]{any,3 -> PA }; head=PB:*[17]@{_; next=PB; value=Scalar}?; size=[35]{any,2 -> int64 }}, 1=PA)",
        "[17,18,19]","[34,35]");
  }

  // A generic List, which is given a way to force the values to be a specific
  // type.  Errors if created with the wrong type.
  @Test public void h_variance_03() {
    String prog = """
list_int0 = ((ListInt) "red");
list_str0 = ((ListStr) 17   );
(pair list_int0 list_str0)
""";
    run(SIZE  + LIST + prog,
        RSIZE + LIST + prog,
        "*( A:[Cannot unify {*str:(114)->A} and *@{append={   int64     -> A }; head = B:*@{next=B;value=int64}?;size={->%int64}}] ," +
        "   C:[Cannot unify {17       -> C} and *@{append={D:*str:(int8)-> C }; head = E:*@{next=E;value=D    }?;size={->%int64}}] )" ,
        "*[19](_, Scalar, Scalar)",
        "[17,18,19]",null);
  }



  // Create a boolean-like structure, and unify.
  @Test public void x_peano_00() {
    run("void = @{};"+              // Same as '()'; all empty structs are alike
        "true = @{"+                // 'true' is a struct with and,or,then
        "  and= {at -> at};"+
        "  or = {ot -> true};"+
        "  then = {then ig_else -> (then void) }"+
        "};"+
        "false = @{"+               // 'false' is a struct with and,or,then
        "  and= {af -> false};"+
        "  or = {of -> of};"+
        "  then = {ig_then else -> (else void) }"+
        "};"+
        "forceSubtyping ={pred ->(if pred true false)};"+ // A unified version
        // Trying really hard here to unify 'true' and 'false'
        "bool=@{false=(forceSubtyping 0); true=(forceSubtyping 1); force=forceSubtyping};"+
        // Apply the unified 'false' to two different return contexts
        "testa=(bool.false.then { x-> 3 } { y-> 4 });"+
        "testb=(bool.false.then { z->@{}} { z->@{}});"+
        // Look at the results
        "@{a=testa; b=testb; bool=bool}"+
        "",

        "void = @{};"+              // Same as '()'; all empty structs are alike
        "true = @{"+                // 'true' is a struct with and,or,then
        "  and= {at -> at};"+
        "  or = {ot -> true};"+
        "  then = {then ig_else -> (then void) }"+
        "};"+
        "false = @{"+               // 'false' is a struct with and,or,then
        "  and= {af -> false};"+
        "  or = {of -> of};"+
        "  then = {ig_then else -> (else void) }"+
        "};"+
        "forceSubtyping ={pred ->(if pred ({_pred -> true}(notnil pred)) false)};"+ // A unified version
        // Trying really hard here to unify 'true' and 'false'
        "bool=@{false=(forceSubtyping 0); force=forceSubtyping; true=(forceSubtyping 1)};"+
        // Apply the unified 'false' to two different return contexts
        "testa=(bool.false.then { x-> 3 } { y-> 4 });"+
        "testb=(bool.false.then { z->@{}} { z->@{}});"+
        // Look at the results
        "@{a=testa; b=testb; bool=bool}"+
        "",

        "*@{ a = nint8; b = *( ); bool = *@{ false = A:%*@{ and = { A -> A }; or = { A -> A }; then = { { *( ) -> B } { *( ) -> B } -> B }}; force = { C? -> D:%*@{ and = { D -> D }; or = { D -> D }; then = { { *( ) -> E } { *( ) -> E } -> E }} }; true = F:%*@{ and = { F -> F }; or = { F -> F }; then = { { *( ) -> G } { *( ) -> G } -> G }}}}",
        "*@{ a = nint8; b = *( ); bool = *@{ false = A:%*@{ and = { A -> A }; or = { A -> A }; then = { { *( ) -> B } { *( ) -> B } -> B }}; force = { C? -> D:%*@{ and = { D -> D }; or = { D -> D }; then = { { *( ) -> E } { *( ) -> E } -> E }} }; true = F:%*@{ and = { F -> F }; or = { F -> F }; then = { { *( ) -> G } { *( ) -> G } -> G }}}}",
        "*[23]@{_; a=nint8 ; b=*[21,22](_); bool=*[20]@{_; false=PA:*[18,19]@{_; and=[29,32]{any,3 -> Scalar }; or=[30,33]{any,3 -> Scalar }; then=[31,34]{any,4 -> Scalar }}; force=[38]{any,3 -> PA }; true=PA}}",
        "*[23]@{_; a=Scalar; b=Scalar     ; bool=*[20]@{_; false=PA:*[18,19]@{_; and=[29,32]{any,3 -> Scalar }; or=[30,33]{any,3 -> Scalar }; then=[31,34]{any,4 -> Scalar }}; force=[38]{any,3 -> PA }; true=PA}}",
        "[17,18,19,20,21,22,23]","[8,9,29,30,31,32,33,34,38]"
        );    
  }

  // Regression test; was NPE.  Was testMyBoolsNullPException from marco.servetto@gmail.com.
  @Test public void x_peano_01() {
    run("""
void = @{};
true = @{
  and      = {b -> b};
  or       = {b -> true};
  not      = {unused ->true};
  then = {then else->(then void) }
};
false = @{
  and      = {b -> false};
  or       = {b -> b};
  not      = {unused ->true};
  then = {then else->(else void) }
};
boolSub ={b ->(if b true false)};
@{true=(boolSub 1); false=(boolSub 0)}
""",
        """
void = @{};
true = @{
  and      = {b -> b};
  not      = {unused ->true};
  or       = {b -> true};
  then = {then else->(then void) }
};
false = @{
  and      = {b -> false};
  not      = {unused ->true};
  or       = {b -> b};
  then = {then else->(else void) }
};
boolSub ={b ->(if b ({_b -> true}(notnil b)) false)};
@{false=(boolSub 0); true=(boolSub 1)}
""",
         "*@{ false = A:%*@{ and = { A -> A }; "+
               "not = { B -> A }; "+
               "or = { A -> A }; "+
               "then = { { *( ) -> C } { *( ) -> C } -> C }"+
             "}; "+
             "true = D:%*@{ and = { D -> D }; "+
               "not = { E -> D }; "+
               "or = { D -> D }; "+
               "then = { { *( ) -> F } { *( ) -> F } -> F }"+
             "}"+
         "}",
        "*[20]@{_; false=PB:*[18,19]@{_; and=[29,33]{any,3 -> Scalar }; not=[31,35]{any,3 -> PA:*[18]@{_; and=[29]{any,3 -> Scalar }; not=[31]{any,3 -> PA }; or=[30]{any,3 -> PA }; then=[32]{any,4 -> Scalar }} }; or=[30,34]{any,3 -> Scalar }; then=[32,36]{any,4 -> Scalar }}; true=PB}",
        "[17,18,19,20]","[8,9,29,30,31,32,33,34,35,36]");
  }

  @Test public void x_peano_02() {
    run("""
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
    """
all =
true = @{
  not = {unused -> all.false};
  then = {then else->(then 7) }
};
false = @{
  not = {unused -> all.true};
  then = {then else->(else 7) }
};
boolSub ={b ->(if b ({_b -> true}(notnil b)) false)};
@{boolSub=boolSub; false=false; true=true };
all
""",
        "*@{ boolSub = { A? -> %*@{ not = { B -> C:*@{ not = { D -> C }; then = { { 7 -> E } { 7 -> E } -> E }} }; then = { { 7 -> F } { 7 -> F } -> F }} }; false = C; true = C}",
        """
*[19]@{_;
  boolSub=[36]{any,3 ->
    PA:*[17,18]@{_; not=[29,31]{any,3 ->PA }; then=[30,32]{any,4 ->Scalar }}
  };
  false=PB:*[18]@{_; not=[31]{any,3 ->PC:*[17]@{_; not=[29]{any,3 ->PB }; then=[30]{any,4 ->Scalar }} }; then=[32]{any,4 ->Scalar }};
  true=PC
}
""",
        "[17,18,19]","[8,9,29,30,31,32,36]");
  }

  // Full on Peano arithmetic.
  @Test public void x_peano_03() {
    String gcp_rez = """
*[24]@{_;
  b=*[20]@{_;
    false=PA:*[19]@{_; and_=[33]{any,3 -> PA     }; or__=[34]{any,3 -> Scalar }; then=[35]{any,4 -> Scalar }};
    true =PB:*[18]@{_; and_=[30]{any,3 -> Scalar }; or__=[31]{any,3 -> PB     }; then=[32]{any,4 -> Scalar }}
  };
  n=*[23]@{_;
    s=[43]{any,3 ->
      PC:*[22]@{_;
        add_=[39]{any,3 -> Scalar };
        pred=[40]{any,3 -> Scalar };
        succ=[41]{any,3 -> PC };
        zero=[42]{any,3 -> PA }
      }
    };
    z=*[21]@{_; add_=[36]{any,3 -> Scalar }; pred=[29]{any,3 -> ~Scalar }; succ=[37]{any,3 -> PC }; zero=[38]{any,3 -> PB }}
  };
  one  =PC;
  three=PC;
  two  =Scalar
}
""";

   run("""
void = @{};
err  = {unused->(err unused)};
b=
  true = @{
    and_ = {o -> o};
    or__ = {o -> b.true};
    then = {then else->(then void) }
  };
  false = @{
    and_ = {o -> b.false};
    or__ = {o -> o};
    then = {then else->(else void) }
  };
  @{ false=false; true=true };
n=
  z = @{
    add_ = {o-> o};
    pred = err;
    succ = {unused -> (n.s n.z)};
    zero = {unused ->b.true}
  };
  s = { pred ->
    self=@{
      add_ = {m -> ((pred.add_ m).succ void)};
      pred = {unused -> pred };
      succ = {unused -> (n.s self)};
      zero = {unused ->b.false}
    };
    self
  };
  @{s=s; z=z};
one = (n.s n.z);
two = (one.add_ one);
three =(n.s two);
@{b=b; n=n; one=one; three=three; two=two}
""",
       null,
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
       "[5,6,17,18,19,20,21,22,23,24]","[8,9,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43]");
  }

  // Regression during the HM/GCP Apply lift.
  @Test public void x_peano_04() {
    run("""
all=
  void = @{};
  err  = {unused->(err unused)};
  true = @{
    and  = {b -> b};
    or   = {b -> all.true};
    then = {then else->(then void) }
    };
  false = @{
    and  = {b -> all.false};
    or   = {b -> b};
    then = {then else->(else void) }
    };
  boolSub ={b ->(if b true false)};
  z = @{
    zero = {unused ->all.true};
    pred = err;
    succ = {n -> (all.s n)};
    add_ = {n-> n}
    };
  orZero = {n ->(true.then {unused ->n} {unused ->z})};
  s = {pred ->
    self=@{
      zero = {unused ->all.false};
      pred = {unused->pred};
      succ = {unused -> (all.s self)};
      add_ ={m -> (self.succ (pred.add_ m))}
      };
    (orZero self)
    };
  one =(s z);
  @{true=(boolSub 1); false=(boolSub 0); z=z; s=s};
all
""",
        """
all=
  void = @{};
  err  = {unused->(err unused)};
  true = @{
    and  = {b -> b};
    or   = {b -> all.true};
    then = {then else->(then void) }
    };
  false = @{
    and  = {b -> all.false};
    or   = {b -> b};
    then = {then else->(else void) }
    };
  boolSub ={b ->(if b ({_b -> true}(notnil b)) false)};
  z = @{
    add_ = {n-> n};
    pred = err;
    succ = {n -> (all.s n)};
    zero = {unused ->all.true}
    };
  orZero = {n ->(true.then {unused ->n} {unused ->z})};
  s = {pred ->
    self=@{
      add_ ={m -> (self.succ (pred.add_ m))};
      pred = {unused->pred};
      succ = {unused -> (all.s self)};
      zero = {unused ->all.false}
      };
    (orZero self)
    };
  one =(s z);
  @{false=(boolSub 0); s=s; true=(boolSub 1); z=z};
all
""",
         """
*@{
  false=A:%*@{
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
  false=A:%*@{
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
*[22]@{_;
  false=PC:*[18,19]@{_; and=[30,33]{any,3 -> Scalar }; or=[31,34]{any,3 -> Scalar }; then=[32,35]{any,4 -> Scalar }};
  s=[50]{any,3 ->
    PA:*[21]@{_;
      add_=[49]{any,3 -> PA };
      pred=[47]{any,3 -> PB:*[5,6,7,20,21]@{add_=[5,29,30,31,33,34,40,41,42,46,47,48,49,50]{any,3 -> Scalar }; pred=[5,8,9,29,30,31,33,34,40,41,42,46,47,48,49,50]{any,3 -> PB }; succ=[5,29,30,31,33,34,40,41,42,46,47,48,49,50]{any,3 -> PB }; zero=[5,8,9,29,30,31,33,34,40,41,42,46,47,48,49,50]{any,3 -> PC }} };
      succ=[48]{any,3 -> PA };
      zero=[46]{any,3 -> PC }
    }
  };
  true =PC;
  z=*[20]@{_;
    add_=[42]{any,3 ->  Scalar };
    pred=[29]{any,3 -> ~Scalar };
    succ=[41]{any,3 -> PA };
    zero=[40]{any,3 -> PC }
  }
}
""",
         """
*[22]@{_;
  false=PA:*[18,19]@{_; and=[30,33]{any,3 -> Scalar }; or=[31,34]{any,3 -> Scalar }; then=[32,35]{any,4 -> Scalar }};
  s    =[50]{any,3 -> Scalar };
  true =PA;
  z    =*[20]@{_; add_=[42]{any,3 -> Scalar }; pred=[29]{any,3 -> ~Scalar }; succ=[41]{any,3 -> Scalar }; zero=[40]{any,3 -> PA }}
}
""",
        "[5,6,7,17,18,19,20,21,22]",
        "[8,9,29,30,31,32,33,34,35,40,41,42,46,47,48,49,50]"
         );
  }


  // Poster-child collection, larger example
  @Test public void x_peano_05() {
    run("""
rand = (factor 1.2f);
cage = { ->
  put = { pet ->
    @{ put = put;
       get = pet
     }
  };
  (put 0)
};
cat = @{ name="red"; purr_vol=1.2f };
dog = @{ name="blue"; wag_rate=2.3f };
cage1 = (cage);
cage2 = (cage);
catcage = (cage1.put cat);
dogcage = (cage2.put dog);
petcage = (if (rand 2) catcage dogcage);
maybecat = catcage.get;
maybedog = dogcage.get;
maybepet = petcage.get;
(triple (if maybecat maybecat.purr_vol 9.9f)
        (if maybedog maybedog.wag_rate 9.9f)
        (if maybepet maybepet.name "abc")
)
""",
        """
rand = (factor 1.2f);
cage = { ->
  put = { pet ->
    @{ get = pet;
       put = put
     }
  };
  (put 0)
};
cat = @{ name="red"; purr_vol=1.2f };
dog = @{ name="blue"; wag_rate=2.3f };
cage1 = (cage);
cage2 = (cage);
catcage = (cage1.put cat);
dogcage = (cage2.put dog);
petcage = (if rand catcage dogcage);
maybecat = catcage.get;
maybedog = dogcage.get;
maybepet = petcage.get;
(triple (if maybecat ({_maybecat -> _maybecat.purr_vol }(notnil maybecat)) 9.9f )
        (if maybedog ({_maybedog -> _maybedog.wag_rate }(notnil maybedog)) 9.9f )
        (if maybepet ({_maybepet -> _maybepet.name     }(notnil maybepet)) "abc")
)
""",
        "*(%flt64,%flt64,%*str:(nint8))",
        "*(%flt64,%flt64,%*str:(nint8))",
        "*[20](_, flt64,  flt64,  *[4]str:(nint8))",
        "*[20](_, Scalar, Scalar, *[4]str:(nint8))",
        "[20]",null);
  }

  // Shorter version of perf_01
  @Test public void x_perf_00() {
    String rez_hm = "*({A B C -> *(A,B,C)},{D E F -> *(D,E,F)},{GHI->*(G,H,I)})";
    run("p0 = { x y z -> (triple x y z) };"+
         "p1 = (triple p0 p0 p0);"+
         "p1",

        rez_hm,
        "*[18](_, 0=XA:[30]{any,5 ->*[17](_, Scalar, Scalar, Scalar) }, 1=XA, 2=XA)",
        "[17,18]","[30]"  );
  }

  // try the worse-case expo blow-up test case from SO
  @Test public void x_perf_01() {
    String rez_hm = "*( *( *( { A B C -> *( A, B, C) }, { D E F -> *( D, E, F) }, { G H I -> *( G, H, I) }), *( { J K L -> *( J, K, L) }, { M N O -> *( M, N, O) }, { P Q R -> *( P, Q, R) }), *( { S T U -> *( S, T, U) }, { V22 V23 V24 -> *( V22, V23, V24) }, { V25 V26 V27 -> *( V25, V26, V27) })), *( *( { V28 V29 V30 -> *( V28, V29, V30) }, { V31 V32 V33 -> *( V31, V32, V33) }, { V34 V35 V36 -> *( V34, V35, V36) }), *( { V37 V38 V39 -> *( V37, V38, V39) }, { V40 V41 V42 -> *( V40, V41, V42) }, { V43 V44 V45 -> *( V43, V44, V45) }), *( { V46 V47 V48 -> *( V46, V47, V48) }, { V49 V50 V51 -> *( V49, V50, V51) }, { V52 V53 V54 -> *( V52, V53, V54) })), *( *( { V55 V56 V57 -> *( V55, V56, V57) }, { V58 V59 V60 -> *( V58, V59, V60) }, { V61 V62 V63 -> *( V61, V62, V63) }), *( { V64 V65 V66 -> *( V64, V65, V66) }, { V67 V68 V69 -> *( V67, V68, V69) }, { V70 V71 V72 -> *( V70, V71, V72) }), *( { V73 V74 V75 -> *( V73, V74, V75) }, { V76 V77 V78 -> *( V76, V77, V78) }, { V79 V80 V81 -> *( V79, V80, V81) })))";
    run("p0 = { x y z -> (triple x y z) };"+
         "p1 = (triple p0 p0 p0);"+
         "p2 = (triple p1 p1 p1);"+
         "p3 = (triple p2 p2 p2);"+
         "p3",
        
        rez_hm,
        "*[20](_, 0=PB:*[19](_, 0=PA:*[18](_, 0=XA:[30]{any,5 ->*[17](_, Scalar, Scalar, Scalar) }, 1=XA, 2=XA), 1=PA, 2=PA), 1=PB, 2=PB)",
        "[17,18,19,20]","[30]");
  }

  // A more substantial test to check the running time of a worst-case H-M result.
  // This program is a core-AA clone of the equivalent Haskell program:
  //    let dup x = (x,x)
  //    in    dup . dup . dup . ... . dup   // Where "." is a Haskell composition operator
  @Ignore @Test public void x_perf_02() {
    String dup = "dup = { x -> (pair x x) }; ";
    String fog = "fog = { f g -> { x -> (f (g x)) } }; "; // Core AA does not have a composition operator
    String base = "(fog dup dup)";
    // Running time and the result program type are both linear in the program size.
    // Be sure to turn off asserts when running, or the cubic asserts will blow out the runtime!    
    for( int i=0; i<100; i++ ) {
      String core = "(fog dup "+base+" )";
      String prog = dup+fog+core;
      long t0 = System.currentTimeMillis();
      Root syntax = HM.hm(prog, 0, true, false ); // HM, no GCP
      String rez = syntax._hmt.p();
      long t1 = System.currentTimeMillis();
      System.out.println("Program size: "+prog.length()+", type size: "+rez.length()+", runtime: "+(t1-t0)+"ms" );
      base = core;
    }
  }

  // A more substantial test to check the running time of a worst-case H-M result.
  // This program is a core-AA clone of the Example 1.1 in 1990 ACM paper
  // "Deciding ML Typability is Complete for Deterministic Exponential Time" by
  // HARRY G. MAIRSON
  @Ignore @Test public void x_perf_03() {
    String xn = "x0";
    String base = "x0 = { z -> z}; ";
    // Running time and the result program type are both *exponential* in the program size.
    // Be sure to turn off asserts when running, or the cubic asserts will blow out the runtime!    
    for( int i=0; i<10; i++ ) {
      String xn1 = "x"+(i+1);
      base = base + xn1 + "= (pair "+xn+" "+xn+"); ";
      xn = xn1;
      String prog = base + xn1;
      long t0 = System.currentTimeMillis();
      Root syntax = HM.hm(prog, 0, true, false ); // HM, no GCP
      String rez = syntax._hmt.p();
      long t1 = System.currentTimeMillis();
      System.out.println("Program size: "+prog.length()+", type size: "+rez.length()+", runtime: "+(t1-t0)+"ms" );
    }
  }

}
