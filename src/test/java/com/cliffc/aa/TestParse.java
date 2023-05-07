package com.cliffc.aa;

import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.SB;
import org.junit.BeforeClass;
import org.junit.Ignore;
import org.junit.Test;

import java.util.function.Function;
import java.util.function.Supplier;

import static com.cliffc.aa.AA.unimpl;

public class TestParse {
  private static final BitsFun TEST_FUNBITS = BitsFun.make0(43);

  // Set to TRUE to run one test once, with fixed arguments.
  // Set to FALSE for each test to all combinations of HMT and GCP, with a bunch of random seeds.
  private static boolean JIG=false, DO_HMT=false, DO_GCP=false;
  private static int RSEED=0;
  @BeforeClass
  public static void jig_setup() {
    JIG=false;
    Object dummy = Env.GVN;
  }
  @Ignore @Test public void testJig() {
    JIG=true;

    DO_GCP=true;
    DO_HMT=false;
    RSEED=0;
    test("x:=y:=0; z=x++ && y++;(x,y,z)", // increments x, but it starts zero, so y never increments
            "*[11](1, nil,nil)","*(int:int64,A?,B?)",null,null,"[11]",null);
  }
  static private void assertTrue(boolean t) {
    if( t ) return;
    System.err.println("False");
    org.junit.Assert.assertTrue(t);
  }
  static private void assertNull(Object t) {
    if( t==null ) return;
    System.err.println("NotNull "+(t));
    org.junit.Assert.assertNull(t);
  }
  static private void assertEquals(Object x, Object y) {
    if( x==y || x.equals(y) ) return;
    System.err.println("Not Equals "+x+" != "+y);
    org.junit.Assert.assertEquals(x,y);
  }

  // Some HM related type tests
  @Test public void testParse99() {
    test("1", "1", "int:1");
    // Simple primitive expansion, pre-combo
    test("1+2", "3", "int:3");
    // Big enough that the primitives do not all inline before Combo, so Combo
    // has to deal with primitive expansions.
    test("1+2 * 3+4 *5", "27", "int:27");
    // Simple no-arg anonymous function, being called
    test("{5}()", "5", "int:5");
    // TestParse.a_basic_01
    test("{ x -> ( 3, x )}", "[55]{any,4 -> *[11](3, %[2,11][2,55]?) }", "{ A B -> *[11](int:3, B) }", null, null, "[11]", "[55]");
    // TestParse.a_basic_02
    test("{ z -> ((z 0), (z \"abc\")) }", "[55]{any,4 -> *[12](%[2,11,12][2,55]?, %[2,11,12][2,55]?) }",
         "{A {B *[11]str:(int:97)? -> C } -> *[12](C,C) }",
         null, null,
         "[11,12]", "[55]" );

   
    // TestParse.a_basic_05
    // example that demonstrates generic and non-generic variables:
    // 'g' is not-fresh in function 'f'.
    // 'f' IS fresh in the body of 'g' pair.
    test("{ g -> f = { ignore -> g }; (f 3, f \"abc\")}",
         "[55]{any,4 -> *[13](%[2,5,13][2,55]?, %[2,5,13][2,55]?) }",
         "{ A B -> *[13]( B, B) }",
         null,null,"[5,13]","[55]");

    // TestParse.g_overload_err_00
    testerr("( { x -> x*2 }, { x -> x*3 })._ 4", "Ambiguous, matching choices ({ A B -> C }, { D E -> F }) vs { G int:4 -> H }",30);

    // Variations on a simple wrapped add.  Requires full annotations to type -
    // because in fact it is all ambiguous and cannot be typed without seeing all
    // the usages.
    testerr("{ x -> x+1 }", "Unable to resolve operator '_+_': { A int:1 -> B }",8);       // LHS is not known, unknown clazz, oper (pinned, no clazz to report)
    testerr("{ x -> 1+x }", "Ambiguous, matching choices ({ int:int64 int:int64 -> int:int64 }, { int:int64 flt:nflt64 -> flt:flt64 }) vs { int:1 A -> B }",8);
    testerr("{ x y -> x+y }", "Unable to resolve operator '_+_': { A B -> C }",10);
    testerr("( { x -> x*2 }, { x -> x*3 })._ 4", "Ambiguous, matching choices ({ A B -> C }, { D E -> F }) vs { G int:4 -> H }",30);
    testerr("@{x=7}.y",  "Unknown field '.y' in @{x= A}: ",7); // LHS is known, not a clazz, field not found in instance
    testerr("\"abc\".y", "Unknown field '.y' in str:(A): ",6);  // LHS is known, has clazz, field not found in either, field is not oper (not pinned)
    testerr("\"abc\"&1", "Unknown operator '_&_' in str:(int:97): ( ..., )",5); // LHS is known, has clazz, field not found in either, field it oper (pinned, so report clazz)
    test("{x:flt y:int -> x+y}", "[55]{any,5 -> flt64 }", "{ A flt:flt64 int:int64 -> flt:flt64 }", null, null, null, "[55]");

    // error, missing a comma
    testerr("{ x -> ( 3 x )}", "A function is being called, but 3 is not a function",11);

    // TestParse.b_recursive_01
    test("{ f -> (f f) }", "[55]{any,4 -> %[2][2,55]? }", "{A B:{C B -> D } -> D }", null, null, "[]", "[55]" );

    // TestParse.b_recursive_02
    test("fun = { fx x -> x ? fx( fun(fx,x-1) ) : 1 }; fun(2._*_._, 99)",
            "int:int64",
            "int:int64");

    // TestParse.b_recursive_05, Y combinator
    test("{ f -> ({ x -> (f (x x))} { x -> (f (x x))})}",
         "[55]{any,4 -> %[2,5][2,55]? }", "{ A { B C -> C } -> C }",
         null, null,
         "[5]", "[55]" );

    // TestParse.b_recursive_06
    test("fun = { fx -> math.rand(2) ? 1 : fx(fun(fx),2) }; fun",
         "[55]{any,4 -> %[2,5][2,55]? }",
         // Currently allowing 'fun' display to stay alive.
         "A:{ *[9]@{fun=A} {B C:int:int64 int:int64-> C } -> C }",
         null, null,
         "[5]","[55]");
  }

  @Test public void testParse00() {
    test("1", "1", "int:1");
    // Unary operator
    test("-1", "-1", "int:-1");
    test("!1", "nil", "A?");
    // Binary operators
    test("1+2", "3", "int:3");
    test("1-2", "-1",  "int:-1");
    test("1+2*3", "7", "int:7");
    test("1  < 2", "1", "int:1");
    test("1  <=2", "1", "int:1");
    test("1  > 2", "nil", "A?");
    test("1  >=2", "nil", "A?");
    test("1  ==2", "nil", "A?");
    test("1  !=2", "1", "int:1");
    test("1.2< 2", "1", "int:1");
    test("1.2<=2", "1", "int:1");
    test("1.2> 2", "nil", "A?");
    test("1.2>=2", "nil", "A?");
    test("1.2==2", "nil", "A?");
    test("1.2!=2", "1", "int:1");

    // Binary with precedence check
    test(" 1+2 * 3+4 *5", "27", "int:27");
    test("(1+2)*(3+4)*5", "105", "int:105");
    test("1// some comment\n+2", "3", "int:3"); // With bad comment
    test("-1-2*3-4*5", "-27", "int:-27");
    test("1&3|1&2", "1", "int:1");

    // Float
    test("1.2+3.4", "4.6", "flt:4.6");
    // Mixed int/float with conversion
    test("1+2.3", "3.3", "flt:3.3");

    // Variable lookup
    test("math.pi", "3.141592653589793", "flt:3.141592653589793");
    // bare function lookup; returns a union of '+' functions
    testerr("+", "Syntax error; trailing junk",0);
    testerr("!", "Missing term after operator '!_'",1);
    testerr("_+_", "Syntax error; trailing junk",0);
    testerr("!_", "Missing term after operator '!_'",1);
    // Function application, traditional paren/comma args
    test("1._+_._(2)", "3", "int:3" );
    test("1._-_._(2)", "-1", "int:-1"); // binary version
    test("1.-_._()"  , "-1", "int:-1"); // unary version
    // error; mismatch arg count
    testerr("math.pi(1)", "A function is being called, but 3.141592653589793 is not a function",7);
    testerr("1._+_._(2,3)", "Passing 2 arguments to _+_ which takes 1 arguments",7);

    // Parsed as +(1,(2*3))
    test("1._+_._(2 * 3) ", "7", "int:7");
    // Parsed as (1+2*3)+(4*5+6)
    test("(1 + 2 * 3)._+_._(4 * 5 + 6) ", "33", "int:33");
    // Statements
    test("(1;2 )", "2", "int:2");
    test("(1;2;)", "2", "int:2"); // final semicolon is optional
    test("1._+_._(2;3)", "4", "int:4"); // statements in arguments
    // Operators squished together
    test("-1== -1",  "1",  "int:1");
    test("0== !!1",  "nil", "A?");
    test("2==-1",    "nil", "A?");
    test("-1==--1",  "nil", "A?");
    test("-1==---1", "1",  "int:1");
    testerr("-1== --", "Missing term after operator '-_'",7);
  }

  @Test public void testParse01() {
    // Syntax for variable assignment
    test("x=1", "1", "int:1");
    test("x=y=1", "1", "int:1");
    testerr("x=y=", "Missing ifex after assignment of 'y'",4);
    testerr("x=z" , "Unknown ref 'z'",2);
    testerr("x=1+y","Unknown ref 'y'",4);
    testerr("x=y; x=y","Unknown ref 'y'",2);
    test("x=2; y=x+1; x*y", "6", "int:6");
    // Re-use ref immediately after def; parses as: x=(2*3); 1+x+x*x
    test("1+(x=2*3)+x*x", "43", "int:43");
    testerr("x=(1+(x=2)+x); x", "Cannot re-assign final field '.x' in @{x=2}",0);
    test("x:=1;x++", "1", "int:int64");
    test("x:=1;x++;x", "2", "int:2");
    test("x:=1;x++ + x--","3", "int:3");
    test("x++","nil", "int:int64");
    test("x++;x","1", "int:1");

    // Conditional:
    test   ("0 ?    2  : 3", "3", "int:3"); // false
    test   ("2 ?    2  : 3", "2", "int:2"); // true
    test   ("math.rand(2)?x=4:x=3;x", "nint8", "int:nint8"); // x defined on both arms, so available after
    test   ("math.rand(2)?x=2:  3;4", "4", "int:4"); // x-defined on 1 side only, but not used thereafter
    test   ("math.rand(2)?(y=2;x=y*y):x=3;x", "nint8", "int:int64"); // x defined on both arms, so available after, while y is not
    testerr("math.rand(2)?x=2: 3 ;x", "'x' not defined on false arm of trinary",20);
    testerr("math.rand(2)?x=2: 3 ;y=x+2;y", "'x' not defined on false arm of trinary",20);
    testerr("0 ? x=2 : 3;x", "'x' not defined on false arm of trinary",11);
    test   ("2 ? x=2 : 3;x", "2", "int:2"); // off-side is constant-dead, so missing x-assign is ignored
    test   ("2 ? x=2 : y  ", "2", "int:2"); // off-side is constant-dead, so missing 'y'      is ignored
    testerr("x=1;2?(x=2):(x=3);x", "Cannot re-assign final field '.x' in @{x=1}",7);
    test   ("x=1;2?   2 :(x=3);x", "1", "int:1"); // Re-assigned allowed & ignored in dead branch
    test   ("math.rand(2)?1:int:2:int","nint8", "int:nint8"); // no ambiguity between conditionals and type annotations
    testerr("math.rand(2)?1: :2:int","missing expr after ':'",16); // missing type
    testerr("math.rand(2)?1::2:int","missing expr after ':'",15); // missing type
    test   ("math.rand(2)?1","int1","int:int1"); // Missing optional else defaults to nil
    test   ("x:=0;math.rand(2)?(x:=1);x","int1","int:int1");
    testerr("a.b.c();","Unknown ref 'a'",0);
  }

  // Short-circuit tests
  @Test public void testParse01a() {
    test("0 && 0", "nil","A?");
    test("1 && 2", "int:2","int:2");
    test("0 && 2", "nil","A?");
    test("0 || 0", "nil","A?");
    test("0 || 2", "int:2","int:2");
    test("1 || 2", "int:1","int:1");
    test("0 && 1 || 2 && 3", "int:3","int:3");    // Precedence

    test("x:=y:=0; z=x++ && y++;(x,y,z)", // increments x, but it starts zero, so y never increments
         "*[11](1, nil,nil)","*(int:int64,A?,B?)",null,null,"[11]",null);
    test("x:=y:=0; x++ && y++; z=x++ && y++; (x,y,z)", // x++; x++; y++; (2,1,0)
            "*[12](2, 1, nil)","*(int:int64,int:int64,int:int64)", null, null, "[12]", null);
    test("(x=1) && x+2", "int:3", "int:3"); // Def x in 1st position

    testerr("1 && (x=2;0) || x+3 && x+4", "'x' not defined prior to the short-circuit",5); // x maybe alive
    testerr("0 && (x=2;0) || x+3 && x+4", "'x' not defined prior to the short-circuit",5); // x definitely not alive
    test("math.rand(2) && (x=2;x*x) || 3 && 4", "int:int8", "int:int64"); // local use of x in short-circuit; requires unzip to find 4
  }

  @Test public void testParse02() {
    // Anonymous function definition.  Note: { x -> x&1 }; 'x' can be any struct with an operator '_&_'.
    test("{x:int -> x&1}","[55]{any,4 -> int1 }","{A int:int64 -> int:int64}",null,null,null,"[55]");
    test("{5}()", "5", "int:5"); // No args nor -> required; this is simply a function returning 5, being executed
    testerr("{x:flt y -> x+y}", "Ambiguous, matching choices ({ flt:flt64 flt:flt64 -> flt:flt64 }, { flt:flt64 int:int64 -> flt:flt64 }) vs { flt:flt64 A -> B }",13); // {Scalar Scalar -> Scalar}

    // Function execution and result typing
    test("x=3; andx={y -> x & y}; andx(2)", "2", "int:2"); // trivially inlined; capture external variable
    test("x=3; and2={x -> x & 2}; and2(x)", "2", "int:2"); // trivially inlined; shadow  external variable
    testerr("plus2={x -> x+2}; x", "Unknown ref 'x'",18); // Scope exit ends lifetime
    testerr("fun={x -> }; fun(0)", "Missing function body",10);
    testerr("fun(2)", "Unknown ref 'fun'", 0);
    test("mul3={x -> y=3; x*y}; mul3(2)", "6","int:6"); // multiple statements in func body
    test("x=3; addx={y -> x+y}; addx(2)", "5","int:5");
    test("x=3; mul2={x -> x*2}; mul2(2.1)", "4.2","flt:4.2"); // must inline to resolve overload {*}:Flt with I->F conversion
    test("x=3; mul2={x -> x*2}; mul2(2.1)+mul2(x)", "10.2","flt:10.2"); // Mix of types to mul2(), mix of {*} operators
    test("sq={x -> x*x}; sq 2.1", "4.41","flt:4.41"); // No () required for single args
    testerr("sq={x -> x&x}; sq(\"abc\")", "Unknown operator '_&_' in str:(int:97): ( ..., )",10);
    testerr("sq={x -> x*x}; sq(\"abc\")", "Unknown operator '_*_' in str:(int:97): ( ..., )",10);
    // Recursive:
    test("fact = { x -> x <= 1 ? x : x*fact(x-1) }; fact(3)","6","int:6");
    test("fib = { x -> x <= 1 ? 1 : fib(x-1)+fib(x-2) }; fib(4)","int64","int:int64");
    test("f0 = { x -> x ? 1+(f0(x-1)) : 0 }; f0(2)", "2","int:2");
    testerr("fact = { x -> x <= 1 ? x : x*fact(x-1) }; fact()","Passing 0 arguments to fact which takes 1 arguments",46);
    test("fact = { x -> x <= 1 ? x : x*fact(x-1) }; (fact(0),fact(1),fact(2))","*[13](nil,1,2)","*(int:int64,A:int:int64,A)", null, null, "[13]", null);

    // Co-recursion requires parallel assignment & type inference across a lexical scope
    test("is_even = { n -> n ? is_odd(n-1) : 1}; is_odd = {n -> n ? is_even(n-1) : 0}; is_even(4)", "1", "int:1" );
    test("is_even = { n -> n ? is_odd(n-1) : 1}; is_odd = {n -> n ? is_even(n-1) : 0}; is_even(99)", "int1", "int:int1" );

    // This test merges 2 TypeFunPtrs in a Phi, and then fails to resolve.
    test("(math.rand(1) ? 2._+_ : 2._*_) ._ (3)","int64","int:int64"); // either 2+3 or 2*3, or {5,6} which is INT8.
    test("(math.rand(1) ? 2._+_._ : 2._*_._)(3)","int64","int:int64"); // either 2+3 or 2*3, or {5,6} which is INT8.
    test("f = g = {-> 3}; f() == g();", "1", "int:1");
    testerr("add = {x:int x:int -> x + x}", "Duplicate parameter name 'x'", 13);
  }

  @Test public void testParse03() {
    // Type annotations
    test("-1:int", "-1","int:-1");
    test("(1+2.3):flt", "3.3", "flt:3.3");
    test("x:int = 1", "int:1", "int:1");
    test("x:flt = 1", "int:1", "int:1"); // casts for free to a float
    testerr("x:flt32 = 123456789", "123456789 is not a flt32",0);
    testerr("1:","Syntax error; trailing junk",1); // missing type
    testerr("2:x", "Syntax error; trailing junk", 1);
    testerr("(2:)", "Syntax error; trailing junk", 2);

    test   (" -1 :int1", "-1", "int:-1"); // parses as -(1:int)
    testerr("(-1):int1", "-1 is not a int1",4);
    testerr("\"abc\":int", "*str:(97) is not a int64",5);
    testerr("1:str", "1 is not a *str:(int8)",1);

    test   ("{x:int -> x*2}(1)", "2","int:2"); // Types on parms
    testerr("{x:str -> x}(1)", "1 is not a *str:(int8)", 2);

    // Type annotations on dead args are ignored
    test   ("fun:{int str -> int}={x y -> x+2}; fun(2,3)", "4","int:4");
    testerr("fun:{int str -> int}={x y -> x+y}; fun(2,3)", "3 is not a *str:(int8)",41);
    testerr("x=3; fun:{int->int}={x -> x*2}; fun(2.1)+fun(x)", "2.1 is not a int64",36);
    // Test that the type-check is on the variable and not the function.
    test   ("fun={x y -> x*2}; bar:{int str -> int} = fun; baz:{int @{x;y} -> int} = fun; (fun(2,3),bar(2,\"abc\"))",
            "*[12](4,4)", "*(A:int:int64,A)", null, null, "[12]", null);
    testerr("fun={x y -> x+y}; baz:{int @{x;y} -> int} = fun; (fun(2,3), baz(2,3))",
            "3 is not a *@{x:=Scalar; y:=Scalar; ...}", 66);
    testerr("fun={x y -> x+y}; baz={x:int y:@{x;y} -> foo(x,y)}; (fun(2,3), baz(2,3))",
            "Unknown ref 'foo'", 41);
    // This test failed because the inner fun does not inline until GCP,
    // and then it resolves and lifts the DISPLAY (which after resolution
    // is no longer needed).  Means: cannot resolve during GCP and preserve
    // monotonicity.  Would like '.fun' to load BEFORE GCP.
    testerr("fun={x y -> x+y}; baz={x:int y:@{x;y} -> fun(x,y)}; (fun(2,3), baz(2,3))",
            "3 is not a *@{x:=Scalar; y:=Scalar; ...}", 69);
  }

  @Test public void testParse04() {
    // simple anon struct tests
    testerr("a=@{x=1.2;y}; x", "Unknown ref 'x'",14);
    testerr("a=@{x=1;x=2}.x", "Cannot re-assign final field '.x' in @{x=1}",8);
    test   ("a=@{x=1.2;y;}; a.x", "1.2", "flt:1.2"); // standard "." field naming; trailing semicolon optional
    test   ("x=@{n:=1;v:=2}; x.n := 3; x", "*[10]@{_; n:=3; v:=2}","*@{n=int:nint8; v=int:2}", null, null, "[10]", null);
    testerr("(a=@{x=0;y=0}; a.)", "Missing field name after '.'",17);
    testerr("a=@{x=0;y=0}; a.x=1; a","Cannot re-assign final field '.x' in @{x=nil; y=nil}",16);
    test   ("a=@{x=0;y=1}; b=@{x=2}  ; c=math.rand(1)?a:b; c.x", "int8", "int:int8"); // either 0 or 2; structs can be partially merged
    testerr("a=@{x=0;y=1}; b=@{x=2}; c=math.rand(1)?a:b; c.y",  "Unknown field '.y' in @{x= A:int:B:int8}: ",46);
    testerr("dist={p->p.x*p.x+p.y*p.y}; dist(@{x=1})", "Unknown field '.y' in @{x=1}",19);
    test   ("dist={p->p.x*p.x+p.y*p.y}; dist(@{x=1;y=2})", TypeInt.con(5));     // passed in to func
    test   ("dist={p->p.x*p.x+p.y*p.y}; dist(@{x=1;y=2;z=3})", TypeInt.con(5)); // extra fields OK
    test   ("dist={p:@{x;y} -> p.x*p.x+p.y*p.y}; dist(@{x:=1;y:=2})", TypeInt.con(5)); // Typed func arg
    test   ("a=@{x=(b=1.2)*b;y=b}; a.y", TypeFlt.con(1.2 )); // ok to use temp defs
    test   ("a=@{x=(b=1.2)*b;y=x}; a.y", TypeFlt.con(1.44)); // ok to use early fields in later defs
    testerr("a=@{x=(b=1.2)*b;y=b}; b", "Unknown ref 'b'",22);
    test   ("t=@{n=0;val=1.2}; u=math.rand(1) ? t : @{n=t;val=2.3}; u.val", TypeFlt.FLT64); // structs merge field-by-field
    // Comments in the middle of a struct decl
    test   ("dist={p->p//qqq\n.//qqq\nx*p.x+p.y*p.y}; dist(//qqq\n@{x//qqq\n=1;y=2})", TypeInt.con(5));
    testerr("@{x;y]","Expected closing '}' but found ']' instead",1);

    // Lexical scoping.  Struct assignments make new fields, shadowing external variables.
    test("x=@{a:=1;b=@{a=  2;b=@{a=3;b=0}}}; x.b.b.a",TypeInt.con(3));
    // Lexical scoping.  Before a new field is created, the external variable is used.
    // After the new field, the new field is used.
    test("x=@{a:=1;b=@{a=a+1;c=a}}; x.a*10+x.b.c",TypeInt.con(1*10+2));
    // Similar to Python; if the first ref to a variable finds it in some
    // (possibly external) scope, further refs all refer to the same variable.
    // Here 'a:=a+1' or 'a++' in the scope of 'b' increments the external variable.
    // If the first ref to a variable is a set/store, then the variable
    // is defined locally.  Hence, 'b=0' shadows the external x.b, and x.b
    // is NOT set to 0.
    test("x=@{a:=1;b= {a=a+1;b=0}}; x.b(); x.a",TypeInt.con(2));

    // Tuple
    test("(0,\"abc\")","*(0, *\"abc\")","(0,*\"abc\")");
    test("(1,\"abc\").0", "int:1", "int:1");
    test("(1,\"abc\").1", TypeStruct.ISUSED);

    test   ("math.rand(1)?@{}","@{^=@{^=*[5]()?}}","@{^=@{^=A}?}?");
  }

  @Test public void testParse05() {
    // nilable and not-nil pointers
    test   ("x:str? = 0", TypeNil.NIL); // question-type allows nil or not; zero digit is nil
    test_obj("x:str? = \"abc\"", TypeStruct.ISUSED); // question-type allows nil or not
    testerr("x:str  = 0", "0 is not a *str", 1);
    test("math.rand(1)?0:\"abc\"", "*\"abc\"?","*\"abc\"?");
    testerr("(math.rand(1)?0 : @{x=1}).x", "Struct might be nil when reading field '.x'", 26);
    test   ("p=math.rand(1)?0:@{x=1}; p ? p.x : 0", TypeInt.BOOL); // not-nil-ness after a nil-check
    test   ("x:int = y:str? = z:flt = 0", TypeNil.NIL); // nil/0 freely recasts
    test   ("\"abc\"==0", "int:0", "int:1"); // No type error, just not nil
    test   ("\"abc\"!=0", "int:1", "int:1"); // No type error, just not nil
    test   ("nil=0; \"abc\"!=nil", "int:1", "int:1"); // Another way to name nil
    test   ("""
      a = math.rand(1) ? 0 : @{x=1}; // a is nil or a struct
      b = math.rand(1) ? 0 : @{c=a}; // b is nil or a struct
      b ? (b.c ? b.c.x : 0) : 0      // Nil-safe field load""", TypeInt.BOOL); // Nested nil-safe field load
  }

  @Test public void testParse03a() {
    // Named types
    //test_named_tuple("A= :(       )" ); // Zero-length tuple
    //test_named_tuple("A= :(   ,   )", Type.SCALAR); // One-length tuple
    //test_named_tuple("A= :(   ,  ,)", Type.SCALAR  ,Type.SCALAR  );
    //test_named_tuple("A= :(flt,   )", TypeFlt.FLT64 );
    //test_named_tuple("A= :(flt,int)", TypeFlt.FLT64,TypeInt.INT64);
    //test_named_tuple("A= :(   ,int)", Type.SCALAR  ,TypeInt.INT64);
    //
    //test("A= :(str?, int); A( \"abc\",2 )",
    //     (ignore-> TypeMemPtr.make(29,TypeStruct.make_test("A:",TypeMemPtr.make(17,TypeStruct.EMPTY),TypeInt.con(2)))),
    //     null, "(*\"abc\",2)");
    //test("A= :(str?, int); A( (\"abc\",2) )",
    //     (ignore-> TypeMemPtr.make(18,TypeStruct.make_test("A:",TypeMemPtr.make(17,TypeStruct.EMPTY),TypeInt.con(2)))),
    //     null, "(*\"abc\",2)");
    //testerr("A= :(str?, int)?","Named types are never nil",16);

    // Named type variables
    //test("gal=:flt; gal", TypeFunPtr.make(BitsFun.make0(82),4, TypeMemPtr.NO_DISP, TypeFlt.FLT64.set_name("gal:")));
    //test("gal=:flt; 3==gal(2)+1", "int:1");
    //test("gal=:flt; tank:gal = gal(2)", TypeInt.con(2).set_name("gal:"));
    //// test    ("gal=:flt; tank:gal = 2.0", TypeName.make("gal",TypeFlt.con(2))); // TODO: figure out if free cast for bare constants?
    //testerr ("gal=:flt; tank:gal = gal(2)+1", "3 is not a gal:flt64",14);
    //
    //test    ("Point=:@{x;y}; dist={p:Point -> p.x*p.x+p.y*p.y}; dist(Point(1,2))", TypeInt.con(5));
    //test    ("Point=:@{x;y}; dist={p       -> p.x*p.x+p.y*p.y}; dist(Point(1,2))", TypeInt.con(5));
    //testerr ("Point=:@{x;y}; dist={p:Point -> p.x*p.x+p.y*p.y}; dist((@{x=1;y=2}))", "*@{x=1; y=2} is not a *Point:@{x:=; y:=}",55);
    //testerr ("Point=:@{x;y}; Point((0,1))", "*(0, 1) is not a *Point:@{x:=; y:=}",21);
    //testerr("x=@{n: =1;}","Missing type after ':'",7);
    //testerr("x=@{n=;}","Missing ifex after assignment of 'n'",6);
    //test("x=@{n}",(ignore->TypeMemPtr.make(14,TypeStruct.make(TypeFld.NO_DISP,TypeFld.make("n",TypeNil.NIL,Access.RW)))),
    //     null,"@{n=0}");
    throw unimpl();
  }

  @Test public void testParse06() {
//    // Building recursive types
//    test("A= :int; A(1)", "int:1".set_name("A:"));
//    test("A= :(str?, int); A(0,2)","*A:(0, 2)","(0,2)"); // TODO: Named types in HM
//    // Named recursive types
//    test("A= :(A?, int); A(0,2)","*A:(0, 2)","(0,2)");
//    test("A= :(A?, int); A(0,2)","*A:(0, 2)","(0,2)");
//    test("A= :@{n=A?; v=flt}; A(@{n=0;v=1.2}).v;", "1.2","1.2");
//    test("A= :(A?, int); A(A(0,2),3)","*A:(*A:(0, 2), 3)","((0,2),3)");
//
//    test("A= :@{n=A?; v=int}; A(@{n=0;v=3})","*A:@{n=0; v=3}","@{n=0,v=3}");
//
//    // Missing type B is also never worked on.
//    test("A= :@{n=B?; v=int}", "[~78+88]{->*use }","A");
//    test("A= :@{n=B?; v=int}; a = A(0,2)", "*A:@{n=0; v=2}","@{n=0,v=2}");
//    test("A= :@{n=B?; v=int}; a = A(0,2); a.n", "0", "0");
//    // Mutually recursive types
//    test("A= :@{n=B; v=int}; B= :@{n=A; v=flt}; (A,B)", "*([~78+88]{->any }, [~29+82]{->any })", "(A,B)");
//    test("A= :@{n=B; v=int}; B= :@{n=A; v=flt}; (A,B)", "*([~29+82]{->any }, [~78+88]{->any })", "(A,B)");
//    test("A= :@{n=C?; v=int}; B= :@{n=A?; v=flt}; C= :@{n=B?; v=str}; (A,B,C)", "*([~78+88]{->any }, [~29+82]{->any }, [~95+96]{->any })", "(A,B,C)");
//    // Mixed ABC's, making little abc's in-between.
//    test("""
//A= :@{n=B?; v=int};
//a= A(0,5);
//B= :@{n=A?; v=flt};
//b= B(a,3.14);
//C= :@{n=B?; v=str};
//c= C(b,"abc");
//(a,b,c)
//""",     "*(*A:@{n=0; v=5}, *B:@{n=$; v=3.14}, *C:@{n=$; v=*\"abc\"})",
//         "(@{n=0,v=5},@{n=@{n=0,v=5},v=3.14},@{n=@{n=@{n=0,v=5},v=3.14},v=*\"abc\"})");
    throw unimpl();
  }

  @Test public void testParse07() {
    // Simple recursive call being returned.
    test("A= :@{n=A?; v=int}; f={x:A? -> x ? A(f(x.n),x.v*x.v) : 0}", "","");
    test("f={x -> x ? (f x.n,x.v&x.v)}", "[74]{->*use? }","[74]{A:@{n=A,v=int64,...}?->B:(B,int64)?}");
    test("T= :@{n=T?; v=int}; f={x -> x ? T(f(x.n),x.v&x.v)}", "[76]{->*use? }","[76]{ A:@{ n=A, v=int64, ...}? -> B:@{ n=B, v=int64}? }");
    // Passing a function recursively
    test("f0 = { f x -> x ? f(f0(f,x-1),1) : 0 }; f0(_&_,2)", "0","0");
    test("f0 = { f x -> x ? f(f0(f,x-1),1) : 0 }; f0(_+_,2)", "2","2");
    test("A= :@{n=A?; v=int}; f={x:A? -> x ? A(f(x.n),x.v*x.v) : 0}", "","");
    test("A= :@{n=A?; v=flt}; f={x:A? -> x ? A(f(x.n),x.v*x.v) : 0}; f(A(0,1.2)).v;", TypeFlt.con(1.2*1.2));
    test("tmp=((0,1.2),2.3); sq={x->x*x}; map={f t -> t ? (map(f,t.0),f t.1) : 0}; map(sq,tmp).1",TypeFlt.con(2.3*2.3));
    // Calling a function twice which returns the same alias.  Verify no pointer confusion.
    test("noinline_x={@{a}}; x0=noinline_x(); x1=noinline_x(); x0.a:=2; x1.a",  TypeInt.INT8);

    // Longer variable-length list (so no inline-to-trivial).  Pure integer
    // ops, no overload resolution.  Does final stores into new objects
    // interspersed with recursive computation calls.
    //test_obj_isa("map={x -> x ? @{nn=map(x.n);vv=x.v&x.v} : 0};"+
    //             "map(@{n=math.rand(1)?0:@{n=math.rand(1)?0:@{n=math.rand(1)?0:@{n=0;v=1};v=2};v=3};v=4})",
    //             TypeStruct.make(TypeMemPtr.DISP_FLD,TypeFld.make("nn",TypeMemPtr.ISUSED0),TypeFld.make("vv",TypeInt.INT8)));
    //// Test does loads after recursive call, which should be allowed to bypass.
    //test("sum={x -> x ? sum(x.n) + x.v : 0};"+
    //     "sum(@{n=math.rand(1)?0:@{n=math.rand(1)?0:@{n=math.rand(1)?0:@{n=0;v=1};v=2};v=3};v=4})",
    //     (ignore ->TypeInt.INT64), null, "int64");
    //
    //// User-defined linked list.
    //String ll_def = "List=:@{next;val};";
    //String ll_con = "tmp=List(List(0,1.2),2.3);";
    //String ll_map = "map = {fun list -> list ? List(map(fun,list.next),fun(list.val)) : 0};";
    //String ll_fun = "sq = {x -> x*x};";
    //String ll_apl = "map(sq,tmp);";
    //
    //test_isa(ll_def, TypeFunPtr.GENERIC_FUNPTR);
    //test(ll_def+ll_con+"; tmp.next.val", TypeFlt.con(1.2));
    //test_isa(ll_def+ll_con+ll_map, TypeFunPtr.GENERIC_FUNPTR);
    //test_isa(ll_def+ll_con+ll_map+ll_fun, TypeFunPtr.GENERIC_FUNPTR);

    //// TODO: Needs a way to easily test simple recursive types
    //TypeEnv te4 = Exec.go(Env.file_scope(Env.top_scope()),"args",ll_def+ll_con+ll_map+ll_fun+ll_apl);
    //if( te4._errs != null ) System.err.println(te4._errs.toString());
    //assertNull(te4._errs);
    //TypeStruct tt4 = (TypeStruct)te4._tmem.sharpen((TypeMemPtr)te4._t)._obj;
    //assertEquals("List:", tt4._name);
    //TypeFld nxfld = tt4.fld_find("next");
    //TypeFld vxfld = tt4.fld_find("val" );
    //assertNotNull(nxfld);
    //assertNotNull(vxfld);
    //assertTrue(nxfld._t instanceof TypeMemPtr);
    //assertEquals(2.3*2.3,vxfld._t.getd(),1e-6);
    //
    //// Test inferring a recursive struct type, with a little help
    //test_struct("map={x:@{n=;v=flt}? -> x ? @{nn=map(x.n);vv=x.v*x.v} : 0}; map(@{n=0;v=1.2})",
    //            TypeStruct.make(TypeFld.NO_DISP,
    //                            TypeFld.make("nn",TypeNil.NIL,           ARG_IDX  ),
    //                            TypeFld.make("vv",TypeFlt.con(1.2*1.2),ARG_IDX+1)));
    //
    //// Test inferring a recursive struct type, with less help.  This one
    //// inlines so doesn't actually test inferring a recursive type.
    //test_struct("map={x -> x ? @{nn=map(x.n);vv=x.v*x.v} : 0}; map(@{n=0;v=1.2})",
    //            TypeStruct.make(TypeFld.NO_DISP,
    //                            TypeFld.make("nn",TypeNil.NIL,           ARG_IDX  ),
    //                            TypeFld.make("vv",TypeFlt.con(1.2*1.2),ARG_IDX+1)));
    //
    //// Test inferring a recursive struct type, with less help. Too complex to
    //// inline, so actual inference happens
    //test_obj_isa("map={x -> x ? @{nn=map(x.n);vv=x.v*x.v} : 0};"+
    //             "map(@{n=math.rand(1)?0:@{n=math.rand(1)?0:@{n=math.rand(1)?0:@{n=0;v=1.2};v=2.3};v=3.4};v=4.5})",
    //            TypeStruct.make(TypeMemPtr.DISP_FLD,
    //                            TypeFld.make("nn",TypeMemPtr.STRUCT0  ),
    //                            TypeFld.make("vv",TypeFlt.FLT64     ,ARG_IDX+1)));
    //
    //// Test inferring a recursive tuple type, with less help.  This one
    //// inlines so doesn't actually test inferring a recursive type.
    //test_ptr("map={x -> x ? (map(x.0),x.1*x.1) : 0}; map((0,1.2))",
    //         (alias) -> TypeMemPtr.make(alias,TypeStruct.make_test(TypeNil.NIL,TypeFlt.con(1.2*1.2))));
    //
    //test_obj_isa("map={x -> x ? (map(x.0),x.1*x.1) : 0};"+
    //             "map((math.rand(1)?0: (math.rand(1)?0: (math.rand(1)?0: (0,1.2), 2.3), 3.4), 4.5))",
    //             TypeStruct.maket(TypeMemPtr.STRUCT0,TypeFlt.FLT64));
    throw unimpl();
  }


  @Test public void testParse08() {
//    // Main issue with the map() test is final assignments crossing recursive
//    // not-inlined calls.  Smaller test case:
//    test("""
//tmp = @{ val=2; nxt= @{ val=1; nxt=0} };
//noinline_map={ tree -> tree ? @{ vv=tree.val&tree.val; nn=noinline_map(tree.nxt)} : 0};
//noinline_map(tmp)
//""", "*@{nn=$; noinline_map=any; vv=int8}?","A:@{nn=A,noinline_map=any,vv=int64}?");

    // Too big to inline, multi-recursive
    test("""
tmp=@{
  l=@{
    l=@{ l=0; r=0; v=3 };
    r=@{ l=0;
         r=@{ l=0; r=0; v=9 };
         v=7
    };
    v=5
  };
  r=@{
    l=@{ l=0; r=0; v=15 };
    r=@{ l=0; r=0; v=22 };
    v=20
  };
  v=12
};
map={tree -> tree
     ? @{ ll=map(tree.l);
          rr=map(tree.r);
          vv=tree.v & tree.v
       }
     : 0};
map(tmp)
""",
         "@{ll=*@{ll=*@{ll=0; rr=0; vv=3}; rr=*@{ll=*@{$; rr=$; vv=int8}?; $; vv=7}; vv=5}; rr=*@{$; rr=*@{$; $; vv=22}; vv=20}; vv=12}",
         "");


    // Failed attempt at a Tree-structure inference test.  Triggered all sorts
    // of bugs and error reporting issues, so keeping it as a regression test.
    testerr("tmp=@{"+
         "  l=@{"+
         "    l=@{ l=0; v=3 };"+
         "    l=0;"+
         "    v=5"+
         "  };"+
         "  v=12 "+
         "};"+
         "map={tree -> tree"+
         "     ? @{ll=map(tree.l);vv=tree.v}"+
         "     : 0};"+
         "map(tmp)",
            "Cannot re-assign final field '.l' in @{l=*~use; v:=0}",36);

    // Good tree-structure inference test
    test_ptr("tmp=@{"+
         "  l=@{"+
         "    l=@{ l=0; r=0; v=3 };"+
         "    r=@{ l=0; r=0; v=7 };"+
         "    v=5"+
         "  };"+
         "  r=@{"+
         "    l=@{ l=0; r=0; v=15 };"+
         "    r=@{ l=0; r=0; v=22 };"+
         "    v=20"+
         "  };"+
         "  v=12 "+
         "};"+
         "map={tree fun -> tree"+
         "     ? @{l=map(tree.l,fun);r=map(tree.r,fun);v=fun(tree.v)}"+
         "     : 0};"+
         "map(tmp,{x->x+x})",
         "@{l=*@{l=*@{l=0; r=0; v=6}; r=*@{l=*@{$; r=$; v=30}?; $; v=14}; v=10}; r=*@{$; r=*@{$; $; v=44}; v=40}; v=24}");

    // A linked-list mixing ints and strings, always in pairs
    String ll_cona = "a=0; ";
    String ll_conb = "b=math.rand(1) ? ((a,1),\"abc\") : a; ";
    String ll_conc = "c=math.rand(1) ? ((b,2),\"def\") : b; ";
    String ll_cond = "d=math.rand(1) ? ((c,3),\"ghi\") : c; ";
    String ll_cone = "e=math.rand(1) ? ((d,4),\"jkl\") : d; ";
    String ll_cont = "tmp=e; ";
    // Standard pair-UN-aware map call
    String ll_map2 = "map = {fun list -> list ? (map(fun,list.0),fun(list.1)) : 0};";
    String ll_fun2 = "plus = {x -> x+x};";
    String ll_apl2 = "map(plus,tmp);";
    // End type: ((((*?,scalar)?,str)?,int64),str)?

    // After inlining once, we become pair-aware.

    //TypeStruct xts_int = TypeStruct.make_test(TypeMemPtr.ISUSED0,TypeInt.INT64);
    //TypeMemPtr xpt_int = TypeMemPtr.make (BitsAlias.ALLX,xts_int);
    //TypeStruct xts_str = TypeStruct.make_test(xpt_int,TypeMemPtr.STRPTR);
    //TypeMemPtr xtmp = TypeMemPtr.make(BitsAlias.ALL,xts_str);
    //
    //test_isa(ll_cona+ll_conb+ll_conc+ll_cond+ll_cone+ll_cont+ll_map2+ll_fun2+ll_apl2,xtmp);
    throw unimpl();
  }

  @Test public void testParse09() {
    // Test re-assignment
    test("x=1", "int:1", "int:1");
    test("x=y=1", "int:1", "int:1");
    testerr("x=y=", "Missing ifex after assignment of 'y'",4);
    testerr("x=z" , "Unknown ref 'z'",2);
    testerr("x=1+y","Unknown ref 'y'",4);

    test("x:=1", "int:1", "int:1");
    //test_obj("x:=0; a=x; x:=1; b=x; x:=2; (a,b,x)", TypeStruct.make_test(TypeNil.NIL,TypeInt.con(1),TypeInt.con(2)));
    //
    //testerr("x=1; x:=2; x", "Cannot re-assign final field '.x' in @{x=1}", 5);
    //testerr("x=1; x =2; x", "Cannot re-assign final field '.x' in @{x=1}", 5);
    //
    //test("math.rand(1)?(x=4):(x=3);x", TypeInt.NINT8); // x defined on both arms, so available after
    //test("math.rand(1)?(x:=4):(x:=3);x", TypeInt.NINT8); // x defined on both arms, so available after
    //test("math.rand(1)?(x:=4):(x:=3);x:=x+1", TypeInt.INT64); // x mutable on both arms, so mutable after
    //test   ("x:=0; 1 ? (x:=4):; x:=x+1", TypeInt.con(5)); // x mutable ahead; ok to mutate on 1 arm and later
    //test   ("x:=0; 1 ? (x =4):; x", TypeInt.con(4)); // x final on 1 arm, dead on other arm
    //testerr("x:=0; math.rand(1) ? (x =4):3; x=2; x", "Cannot re-assign read-only field '.x' in @{x==int8}",31);
    //// A final store, but defs of @{a} do not escape into nonline_x, hence do
    //// not merge and escape out.
    //test("noinline_x={@{a}}; noinline_x().a=2; noinline_x().a",  TypeInt.INT8);
    throw unimpl();
  }

  // Ffnls are declared with an assignment.  This is to avoid the C++/Java
  // problem of making final-field cycles.  Java requires final fields to be
  // only assigned in constructors before the value escapes, which prevents any
  // final-cyclic structures.  Final assignments have to be unambiguous - they
  // fold into a 'New' at some point, same as casting to a 'Name', but they can
  // interleave with other operations (such as other News) as long as the store
  // is unambiguous.
  //                                                   unknown
  // Field mod status makes a small lattice:      final       read/write
  //                                                  read-only

  // Type-error if a final assignment does not fold into a New.  Cannot cast
  // final to r/w, nor r/w to final.  Can cast both to r/o.  The reason you
  // cannot cast to a final, is that some other caller/thread with some other
  // r/w copy of the same pointer you have, can modify the supposedly final
  // object.  Hence, you cannot cast to "final", but you can cast to "read-only"
  // which only applies to you, and not to other r/w pointers.
  @Test public void testParse10() {
    //// Test re-assignment in struct
    //test_obj_isa("x=@{n:=1;v:=2}", TypeStruct.make(TypeMemPtr.DISP_FLD,
    //                                               TypeFld.make("n",TypeInt.con(1),Access.RW),
    //                                               TypeFld.make("v",TypeInt.con(2),Access.RW)));
    //testerr ("x=@{n =1;v:=2}; x.n  = 3; x.n", "Cannot re-assign final field '.n' in @{n=1; v:=2}",18);
    //test    ("x=@{n:=1;v:=2}; x.n  = 3", TypeInt.con(3));
    //test_ptr("x=@{n:=1;v:=2}; x.n := 3; x", "@{n:=3; v:=2}");
    //testerr ("x=@{n:=1;v:=2}; x.n  = 3; x.v = 1; x.n = 4; x.n", "Cannot re-assign final field '.n' in @{n=3; v=1}",37);
    //test    ("x=@{n:=1;v:=2}; y=@{n=3;v:=4}; tmp = math.rand(1) ? x : y; tmp.n", TypeInt.NINT8);
    //testerr ("x=@{n:=1;v:=2}; y=@{n=3;v:=4}; tmp = math.rand(1) ? x : y; tmp.n = 5; tmp.n", "Cannot re-assign read-only field '.n' in @{n==nint8; v:=nint8}",63);
    //test    ("x=@{n:=1;v:=2}; foo={q -> q.n=3}; foo(x); x.n",TypeInt.con(3)); // Side effects persist out of functions
    //// Tuple assignment
    //testerr ("x=(1,2); x.0=3; x", "Cannot re-assign final field '.0' in (1, 2)",11);
    //// Final-only and read-only type syntax.
    //testerr ("ptr2rw = @{f:=1}; ptr2final:@{f=} = ptr2rw; ptr2final", "*@{f:=1} is not a *@{f=; ...}",27); // Cannot cast-to-final
    //
    //test_obj_isa("ptr2   = @{f =1}; ptr2final:@{f=} = ptr2  ; ptr2final", // Good cast
    //             TypeStruct.make(TypeMemPtr.DISP_FLD,TypeFld.make("f",TypeInt.con(1))));
    //testerr ("ptr=@{f=1}; ptr2rw:@{f:=} = ptr; ptr2rw", "*@{f=1} is not a *@{f:=; ...}", 18); // Cannot cast-away final
    //test    ("ptr=@{f=1}; ptr2rw:@{f:=} = ptr; 2", TypeInt.con(2)); // Dead cast-away of final
    //test    ("@{x:=1;y =2}:@{x;y=}.y", TypeInt.con(2)); // Allowed reading final field
    //testerr ("f={ptr2final:@{x;y=} -> ptr2final.y  }; f(@{x:=1;y:=2})", "*@{x:=1; y:=2} is not a *@{x:=; y=; ...}",42); // Another version of casting-to-final
    //testerr ("f={ptr2final:@{x;y=} -> ptr2final.y=3; ptr2final}; f(@{x:=1;y =2})", "Cannot re-assign final field '.y' in @{x:=1; y=2}",34);
    //test    ("f={ptr:@{x==;y:=} -> ptr.y=3; ptr}; f(@{x:=1;y:=2}).y", TypeInt.con(3)); // On field x, cast-away r/w for r/o
    //test    ("f={ptr:@{x=;y:=} -> ptr.y=3; ptr}; f(@{x =1;y:=2}).y", TypeInt.con(3)); // On field x, cast-up r/o for final but did not read
    //testerr ("f={ptr:@{x=;y:=} -> ptr.y=3; ptr}; f(@{x:=1;y:=2}).x", "*@{x:=1; y:=2} is not a *@{x=; y:=; ...}",37); // On field x, cast-up r/w for final and read
    //test    ("f={ptr:@{x;y} -> ptr.y }; f(@{x:=1;y:=2}:@{x;y==})", TypeInt.con(2)); // cast r/w to r/o, and read
    //test    ("f={ptr:@{x==;y==} -> ptr }; f(@{x=1;y=2}).y", TypeInt.con(2)); // cast final to r/o and read
    //test    ("ptr=@{f:=1}; ptr:@{f=}.f=2",TypeInt.con(2)); // Checking that it is-a final does not make it final
    //// In general for these next two, want a 'MEET' style type assertion where
    //// locally at the function parm we "finalize" ptr.y, so the function body
    //// cannot modify it.  However, no final store occurs so after the function,
    //// ptr.y remains writable.
    //testerr ("f={ptr:@{x;y=} -> ptr.y=3}; f(@{x:=1;y:=2});", "*@{x:=1; y:=2} is not a *@{x:=; y=; ...}",30);
    ////testerr ("f={ptr:@{x;y} -> ptr.y=3}; f(@{x:=1;y:=2}:@{x;y=})", "*@{.==nScalar} is not a *@{x:=; y:=; ...}",29);
    //test    ("ptr=@{a:=1}; val=ptr.a; ptr.a=2; val",TypeInt.con(1));
    //// You are allowed to build final pointer cycles
    //test    ("ptr0=@{p:=0;v:=1}; ptr1=@{p=ptr0;v:=2}; ptr0.p=ptr1; ptr0.p.v+ptr1.p.v+(ptr0.p==ptr1)", TypeInt.con(4)); // final pointer-cycle is ok
    throw unimpl();
  }

  // Early function exit
  @Test public void testParse11() {
    test("x:=0; {1 ? ^2; x=3}(); x",TypeNil.NIL);  // Following statement is ignored
    test("{ ^3; 5}()",TypeInt.con(3)); // early exit
    test("x:=0; {^3; x++}(); x",TypeNil.NIL);  // Following statement is ignored
    test("x:=0; {^1 ? (x=1); x=3}(); x",TypeInt.con(1));  // Return of an ifex
    test("x:=0; {^1 ?  x=1 ; x=3}(); x",TypeInt.con(1));  // Return of an ifex
    test("f={0 ? ^0; 7}; f()", TypeInt.con(7));
    // Find: returns 0 if not found, or first element which passes predicate.
    test("find={list pred -> !list ? ^0; pred(list.1) ? ^list.1; find(list.0,pred)}; find(((0,3),2),{e -> e&1})", TypeInt.INT8);
    test("x:=0; {1 ? ^2; x=3}(); x",TypeNil.NIL);  // Following statement is ignored
    // Curried functions
    test("for={A->    A+3 }; for 2  ", TypeInt.con(5));
    test("for={A->{B->A+B}}; for 2 3", TypeInt.con(5));
    test("for={pred->{body->!pred()?^;tmp=body(); tmp?^tmp;7}}; for {1}{0}", TypeInt.con(7));
  }

  // Upwards exposed closure tests
  @Test public void testParse12() {
    test("incA= {cnt:=0; {cnt++}       }(); incA();incA()",TypeInt.con(1));
    test("cnt:=0; incA={cnt++}; incA();incA()+cnt",TypeInt.con(1+2));
    test("incA= {cnt:=0; {cnt++}       }();                      incA()       ",TypeNil.NIL);
    test("incA= {cnt:=0; {cnt++}       }();                      incA();incA()",TypeInt.con(1));
    test("tmp = {cnt:=0;({cnt++},{cnt})}();incA=tmp.0;getA=tmp.1;incA();incA()+getA()",TypeInt.con(1+2));
    test("gen = {cnt:=0;({cnt++},{cnt})};" +
         "tmp:=gen(); incA=tmp.0;getA=tmp.1;"+
         "tmp:=gen(); incB=tmp.0;getB=tmp.1;"+
         "incA();incB();incA(); getA()*10+getB()",
         TypeInt.con(2*10+1));
  }

  // Serial loops; using variable 'for': "for pred body".
  // If 'pred' is false , the loop exits with false.
  // If 'body' is truthy, the loop exits with this value.
  // To 'continue', use '^0'.  To 'break' with non-zero 'val' use '^val'.
  // Break cannot exit with '0'.
  private final String FORELSE="for={pred->{body->!pred()?^;(tmp=body())?^tmp; for pred body}};";
  // If 'pred' is false, the loop exits with false, else loop continues.  'body' value is ignored.
  // To 'continue', use '^'.
  // There is no 'break'.
  private final String DO="do={pred->{body->!pred()?^;body(); do pred body}};";

  @Test public void testParse13() {
    test(DO+"i:=0; do {i++ < 2} {i== 9}; i",TypeInt.con(3));    // Late exit, body never returns true.
    test(FORELSE+"i:=0; for {i++ < 100} {i== 5} ",TypeInt.BOOL); // Not sure of exit value, except bool
    test(FORELSE+"i:=0; for {i++ < 100} {i==50?i}",TypeInt.INT64); // Early exit on condition i==50
    test(DO+"sum:=0; i:=0; do {i++ < 100} {sum:=sum+i}; sum",TypeInt.INT64);
  }

  // Array syntax examples
  @Test public void testParse14() {
    test_ptr("[3]", "[$]0/obj");
    test    ("ary = [3]; ary[0]", TypeNil.NIL);
    test    ("[3][0]", TypeNil.NIL);
    test    ("ary = [3]; ary[0]:=2", TypeInt.con(2));
    //test_obj("ary = [3]; ary[0]:=0; ary[1]:=1; ary[2]:=2; (ary[0],ary[1],ary[2])", // array create, array storing
    //         TypeStruct.make_test(TypeInt.INT8,TypeInt.INT8,TypeInt.INT8));
    //testary("0[0]","0 is not a *[]Scalar/obj",1);
    //testary("[3] [4]","Index must be out of bounds",5);
    //testary("[3] [-1]","Index must be out of bounds",5);
    //test_obj("[3]:[int]", TypeAry.make(TypeInt.con(3),TypeNil.NIL,TypeStruct.ISUSED)); // Array of 3 XNILs in INTs.
    ////test("[1,2,3]", TypeAry.make(TypeInt.con(1),TypeInt.con(3),TypeInt.INT8)); // Array of 3 elements
    //test("ary=[3];#ary",TypeInt.con(3)); // Array length
    //test_ptr(DO+"ary=[99]; i:=0; do {i++ < #ary} {ary[i]:=i*i};ary", "[$]int64/obj"); // sequential iteration over array
    //// ary.{e -> f(e)} // map over array elements
    //// ary.{e -> f(e)}.{e0 e1 -> f(e0,e1) } // map/reduce over array elements
    throw unimpl();
  }

  // Strings
  @Test public void testParse15() {
    //// Simple strings
    //test_ptr("\"Hello, world\"", TypeStr.con("Hello, world"), "\"Hello, world\"");
    //test_ptr("3.14.str()"      , TypeStr.con("3.14"), "3.14");
    //test_ptr("3.str()"         , TypeStr.con("3"   ), "3");
    test("\"abc\"==\"abc\"","int:1", "1"); // Constant strings intern
    //testerr("math.rand(1)?1:\"a\"", "Cannot mix GC and non-GC types",18);
    throw unimpl();
  }

  private static TypeStruct make2fldsD( String f1, Type t1, String f2, Type t2 ) {
    //return TypeStruct.make("",false,TypeFld.NO_DISP,TypeFld.make(f1,t1),TypeFld.make(f2,t2));
    throw unimpl();
  }

  // Combined H-M and GCP Typing
  @Ignore
  @Test public void testParse16() {
    //test("-1", (ignore->TypeInt.con(-1)), null, "-1");
    //test("(1,2)", (ignore -> TypeMemPtr.make(13,TypeStruct.make_test(TypeInt.con(1),TypeInt.con(2)))), null, "[13]( 1,2)");
    //
    //test("@{ n=0; v=1.2 }",
    //     (ignore -> TypeMemPtr.make(13, make2fldsD("n",TypeNil.NIL,"v",TypeFlt.con(1.2)))),
    //     null,
    //     "[13]@{ n = 0, v = 1.2}");
    //
    //test("{&}",
    //     (ignore -> TypeFunPtr.make(BitsFun.make0(35),5, TypeMemPtr.NO_DISP,TypeInt.INT64)),
    //     (() -> TypeStruct.make_test("x",TypeInt.INT64,"y",TypeInt.INT64)),
    //     "[35]{ int64 int64 -> int64 }");
    //
    //test("{ g -> (g,3)}",
    //     (ignore -> TypeFunPtr.make(TEST_FUNBITS,4, TypeMemPtr.NO_DISP,
    //                            // TODO: how do i express the expected return state of memory
    //                            //TypeMem.make(14,TypeStruct.make2fldsD("0",Type.SCALAR,"1",TypeInt.con(3))),
    //                            TypeMemPtr.make(14,TypeStruct.ISUSED))),
    //     (() -> TypeStruct.make(TypeFld.make(" mem",TypeMem.ALLMEM),
    //                             TypeFld.make("^",Type.ALL),
    //                             TypeFld.make("g",Type.SCALAR))),
    //     "[43]{ A -> [14]( A, 3) }");
    //
    //test("{ g -> f = { ignore -> g }; ( f(3), f(\"abc\"))}",
    //     (ignore -> TypeFunPtr.make(TEST_FUNBITS,4, TypeMemPtr.make(12,TypeStruct.ISUSED),
    //                            // TODO: how do i express the expected return state of memory
    //                            //TypeMem.make(18,TypeStruct.make2fldsD("0",Type.SCALAR,"1",Type.SCALAR)),
    //                            TypeMemPtr.make(18,TypeStruct.ISUSED))),
    //     (() -> TypeStruct.make(TypeFld.make(" mem",TypeMem.ALLMEM),
    //                            TypeFld.make("^",TypeMemPtr.make(12,TypeStruct.ISUSED)),
    //                            TypeFld.make("g",Type.SCALAR))),
    //     "[43]{ A -> [18]( A, A) }");
    //// id accepts and returns all types and keeps precision
    //test("noinline_id = {x->x};(noinline_id(5)&7, #noinline_id([3]))",
    //     (ignore -> TypeMemPtr.make(18,TypeStruct.make_test(TypeInt.INT8,TypeInt.con(3)))),
    //     null,
    //     "[99](int8, 3)");
    //
    //
    //
    //// Should be typable with H-M
    //test_ptr("noinline_map={lst fcn -> lst ? fcn lst.1};"+
    //    "in_int=(0,2);"+       // List of ints
    //    "in_str=(0,\"abc\");"+ // List of strings
    //    "out_str =noinline_map(in_int,str:{int->str});"+        // Map over ints with int->str  conversion, returning a list of strings
    //    "out_bool=noinline_map(in_str,{str -> str==\"abc\"});"+ // Map over strs with str->bool conversion, returning a list of bools
    //    "(out_str,out_bool)",
    //  "(*\"2\",int1)");
    //
    //// ID in different contexts; in general requires a new TypeVar per use; for
    //// such a small function it is always inlined completely, has the same effect.
    //test("id={x->x};id(1)",TypeInt.con(1));
    //test("{x->x}(3.14)",TypeFlt.con(3.14));
    //test_prim("{x->x}({+})","+");
    //test("id={x->x};id({+})(id(1),id(math.pi))",TypeFlt.make(0,64,Math.PI+1));
    //
    //// Straight from TestHM.test08; types as {A -> (A,A)}.
    //// Function is never called, so returns the uncalled-function type.
    //test("fun={ g -> f={x -> g}; (f 3,f 1)}", TypeFunPtr.make(BitsFun.make0(46),1,Type.ANY,null));
    //// Called with different typevars A
    //test_ptr("fun={ g -> f={x -> g}; (f 3,f 1)}; (fun \"abc\",fun 3.14)",
    //  "(*(*\"abc\", $), *(3.14, 3.14))");
    //
    //// recursive unification.  Trivially types as a dead fcn ptr.
    //test_isa("x={x -> x x}",TypeFunPtr.make(BitsFun.make0(46),3,TypeMemPtr.NO_DISP,null));
    //// recursive unification.  Passing an ID to x then passes ID to ID, returning ID.
    //test_isa("x={x -> x x}; x({y->y})",TypeFunPtr.make(BitsFun.make0(47),4,TypeMemPtr.NO_DISP,null));
    //// Looks like recursive unification, but x is a function of 0 arguments,
    //// being called with 1 argument.  Error to call it.
    //testerr("x={x x};x(1)","Passing 1 arguments to x which takes 0 arguments",9);
    //// id accepts and returns both ints and reference types (arrays).
    //test_struct("noinline_id = {x->x};(noinline_id(5)&7, #noinline_id([3]))",
    //            TypeStruct.make_test(TypeInt.INT8,TypeInt.con(3)));
    //// Should be typable with H-M
    //test_ptr("noinline_map={lst fcn -> lst ? fcn lst.1};"+
    //         "in_int=(0,2);"+       // List of ints
    //         "in_str=(0,\"abc\");"+ // List of strings
    //         "out_str =noinline_map(in_int,str:{int->str});"+        // Map over ints with int->str  conversion, returning a list of strings
    //         "out_bool=noinline_map(in_str,{str -> str==\"abc\"});"+ // Map over strs with str->bool conversion, returning a list of bools
    //         "(out_str,out_bool)",
    //         "(*\"2\",int1)");
    //// Only odd thing here is losing not-nil-ness on list_int.
    //test_ptr("noinline_map={tup fcn -> (0,fcn tup.1)};"+
    //    "lst_int=(0,2      );"+ //
    //    "lst_str=(0,\"abc\");"+ //
    //    "lst_istr=noinline_map(lst_int,str);"+      // Map over ints with int->str conversion, returning a list of strings
    //    "lst_bool=noinline_map(lst_str,{str-> str==\"abc\"});"+ // Map over strs with str->bool conversion, returns bools
    //    "(lst_istr,lst_bool)",
    //  "(*(0, *\"2\")?, *(0, int1))");
    //// map being called with 2 different functions & lists
    //test("noinline_map={lst fcn -> lst ? (noinline_map(lst.0,fcn),fcn lst.1)};"+
    //     "in_int=(((0,2),3),5);"+ // List of 3 ints
    //     "in_str= ((0,\"abc\"),\"def\");"+ // List of 2 strings
    //     "out_istr=noinline_map(in_int,str);"+      // Map over ints with int->str conversion, returning a list of strings
    //     "out_bool=noinline_map(in_str,{str:str ->str==\"abc\"});"+ // Map over strs with str->bool conversion, returns bools
    //     "(out_istr,out_bool)",
    //     Type.ANY);
    throw unimpl();

  }

  /*
// type variables are free in : type expressions

// Define a pair as 2 fields "a" and "b" both with the same type T.  Note that
// 'a' and 'b' and 'T' are all free, but the @ parses this as a struct, so 'a'
// and 'b' become field names and 'T' becomes a free type-var.
Pair = :@{ a:T, b:T }

// Since 'A' and 'B' are free and not field names, they become type-vars.
MapType = :{ {A->B} List[A] -> List[B] }

// map: no leading ':' so a function definition, not a type def
map:MapType  = { f list -> ... }

// A List type.  Named types are not 'null', so not valid to use "List = :...?".
// Type List takes a type-variable 'A' (which is free in the type expr).
// List is a self-recursive type.
// Field 'next' can be null or List(A).
// Field 'val' is type A.
List = :@{ next:List?, val:A }
   */

  /*** Fanciful attempt at a HashTable class.  No resize, size, clear, etc.
HashTable = {@{
  _tab = [7];

  get = { key ->
    entry = _tab[key.hash() % #_tab];
    entry && key.eq(entry.key) ? entry.val;
  }
  put = { key val ->
    idx = key.hash() % #_tab;
    entry = _tab[idx];
    entry && key.eq(entry.key) ? (oldval=entry.val; entry.val:=val; ^oldval);
    _tab[idx]= @{key=key; val=val; next=entry};
    entry ? entry.val;
  }
}}
   */


  static private void test( String program, Type expected ) {
    throw unimpl(); // replace with full test
  }

  // Run a program once, with a given seed and typing flags.
  // If GCP !=null, test against GCP results.  If GCP expects a TFP, also check formals.
  // If HMT !=null, test against HMT results.  Ignore err.
  // If both are null and err is set, test against err.
  // if both are set, also check esc_ptrs and esc_funs.
  static private void _test0( String program, String gcp, String hmt, String esc_ptrs, String esc_funs, String err, int cur_off, int rseed ) {
    TypeEnv te = Exec.file("test",program,rseed,gcp!=null,hmt!=null);
    // Check GCP result
    if( gcp != null && (err==null || cur_off<0) ) {
      assertNull(te._errs);
      Type actual = te._t;      // Sharpen any memory pointers
      Type expect = Type.valueOf(gcp);
      assertEquals(expect,actual);
    }
    // Check HMT result
    if( hmt != null && err==null ) {
      assertNull(te._errs);
      TV3 actual = te._hmt;
      String actual_str = actual.p();
      assertEquals(stripIndent(hmt),stripIndent(actual_str));
    }
    // If ran both, also track expected Root escapes
    if( gcp != null && hmt != null && (err==null || cur_off<0) ) {
      assertNull(te._errs);
      String esc_ptrs2 = "*"+esc_ptrs+"()";
      String esc_funs2 =     esc_funs+"{any,3->Scalar}";
      BitsAlias aliases = esc_ptrs==null ? BitsAlias.EMPTY : ((TypeMemPtr)Type.valueOf(esc_ptrs2))._aliases;
      BitsFun   fidxs   = esc_funs==null ? BitsFun  .EMPTY : ((TypeFunPtr)Type.valueOf(esc_funs2)).fidxs() ;
      aliases = aliases.set(BitsAlias.EXTX);
      fidxs   = fidxs  .set(BitsFun  .EXTX);
      assertEquals(fidxs  ,te._fidxs  );
      assertEquals(aliases,te._aliases);
    }
    // If err!=null
    if( err != null &&
        (cur_off>=0 ||
         // Specific to a weak solo HMT: without GCP nearly everything escapes, so
         // everything has a default input, so many things cannot resolve.
         (gcp==null && hmt!=null)) ) {
      assertTrue(te._errs != null && te._errs.size()>=1);
      if( cur_off>=0 ) {
        String cursor = new String(new char[cur_off]).replace('\0', ' ');
        String err2 = new SB().p("test:1:").p(err).nl().p(program).nl().p(cursor).p('^').nl().toString();
        assertEquals(err2,te._errs.get(0).toString());
      } else {
        String err2 = new SB().p("test:1:").p(err).nl().toString();
        assertTrue(te._errs.get(0).toString().startsWith(err2));
      }
    }
  }
  private static String stripIndent(String s){ return s.replace("\n","").replace(" ",""); }

  // Run a program once-per-rseed
  static private void _test1( String program, String gcp, String hmt_expect, String esc_ptrs, String esc_funs, String err, int cur_off ) {
    if( JIG )
      _test0(program,gcp,hmt_expect,esc_ptrs,esc_funs,err,cur_off,RSEED);
    else
      for( int rseed=0; rseed<4; rseed++ )
        _test0(program,gcp,hmt_expect,esc_ptrs,esc_funs,err,cur_off,rseed);
  }

  // Run a program in all 3 modes, with all rseeds
  static private void _test2( String program, String gcp, String hmt, String gcp_both, String hmt_both, String esc_ptrs, String esc_funs, String err, int cur_off ) {
    if( gcp_both==null ) gcp_both=gcp;
    if( hmt_both==null ) hmt_both=hmt;
    if( !JIG || ( DO_GCP && !DO_HMT) )  _test1(program,gcp     ,null    ,esc_ptrs,esc_funs,err,cur_off);
    if( !JIG || (!DO_GCP &&  DO_HMT) )  _test1(program,null    ,hmt     ,esc_ptrs,esc_funs,err,cur_off);
    if( !JIG || ( DO_GCP &&  DO_HMT) )  _test1(program,gcp_both,hmt_both,esc_ptrs,esc_funs,err,cur_off);
  }

  // Run a program in all 3 modes, yes function returns, no errors
  // Short form test: simple GCP, no formal args
  private void test( String program, String gcp, String hmt ) {
    _test2(program,gcp,hmt,gcp,hmt,null,null,null,0);
  }
  // Short form test: simple GCP, no formal args
  static private void test( String program, String gcp, String hmt, String gcp_both, String hmt_both ) {
    _test2(program,gcp,hmt,gcp_both,hmt_both,null,null,null,0);
  }

  static private void test( String program, String gcp, String hmt, String gcp_both, String hmt_both, String esc_ptrs, String esc_funs ) {
    _test2(program,gcp,hmt,gcp_both,hmt_both,esc_ptrs,esc_funs,null,0);
  }

  // Run a program in all 3 modes, yes function returns, no errors
  private void test( String program, Function<Type,Type> gcp_maker, Supplier<TypeStruct> formals_maker, String hmt_expect ) {
    //_test2(program,gcp_maker,formals_maker,hmt_expect,null,0);
    throw unimpl();
  }

  // Short form test: simple GCP, no formal args
  private void test( String program, Type gcp, String hmt_expect ) {
    //_test2(program,ignore->gcp,null,hmt_expect,null,0);
    throw unimpl();
  }

  // Result is expected to be a pointer, with an uninteresting alias.  The
  // expected ptr._obj is passed.
  private void test_ptr( String program, TypeStruct gcp_expect, String hmt_expect ) {
    throw unimpl();
    //_test2(program,
    //       actual -> actual instanceof TypeMemPtr ? ((TypeMemPtr)actual).make_from(gcp_expect) : gcp_expect,
    //       null,hmt_expect,null,0);
  }
  // Result is expected to be a pointer, with an uninteresting alias and an
  // interesting nil.  The expected nil-ness and _obj is passed.
  private void test_ptr0( String program, TypeMemPtr gcp_expect, String hmt_expect ) {
    throw unimpl();
    //_test2(program,
    //       actual -> actual instanceof TypeMemPtr ? gcp_expect.make_from_nil(((TypeMemPtr)actual)._aliases) : gcp_expect,
    //       null,hmt_expect,null,0);
  }

  static void testerr( String program, String err, int cur_off ) {
    _test2(program,"","",null,null,null,null,err,cur_off);
  }


  static private void test_prim( String program, String prim ) {
    //Type expected = Env.TOP.lookup_valtype(prim);
    //TypeEnv te = run(program);
    //if( te._errs != null ) System.err.println(te._errs);
    //assertNull(te._errs);
    //assertEquals(expected,te._t);
    throw unimpl();
  }
  static private void test_named_tuple( String program, Type... args ) {
    //TypeEnv te = run(program);
    //assertTrue(te._t instanceof TypeFunPtr);
    //TypeFunPtr actual = (TypeFunPtr)te._t;
    //assertEquals(ARG_IDX+args.length,actual.nargs());
    //assertTrue(actual._ret instanceof TypeMemPtr && actual._ret.simple_ptr()==actual._ret);
    //if( te._formals.is_tup() )
    //  for( TypeFld fld : te._formals.flds() )
    //    assertEquals(args[fld._order-ARG_IDX],fld._t);
    throw unimpl();
  }

  static private void test_obj( String program, TypeStruct expected) {
    //TypeEnv te = run(program);
    //assertTrue(te._t instanceof TypeMemPtr);
    //TypeStruct actual = te._tmem.ld((TypeMemPtr)te._t);
    //assertEquals(expected,actual);
    throw unimpl();
  }
  static private void test_struct( String program, TypeStruct expected) {
    //TypeEnv te = run(program);
    //TypeStruct actual = (TypeStruct)te._tmem.ld((TypeMemPtr)te._t);
    //actual = actual.replace_fld(TypeFld.NO_DISP);
    //assertEquals(expected,actual);
    throw unimpl();
  }
  static private void test_obj_isa( String program, TypeStruct expected) {
    //TypeEnv te = run(program);
    //int alias = ((TypeMemPtr)te._t)._aliases.strip_nil().getbit(); // internally asserts only 1 bit set
    //TypeStruct actual = te._tmem.sharpen((TypeMemPtr)te._t)._obj;
    //assertTrue(actual.isa(expected));
    throw unimpl();
  }
  static private void test_ptr( String program, String expected ) {
    //TypeEnv te = run(program);
    //assertTrue(te._t instanceof TypeMemPtr);
    //TypeStruct to = te._tmem.ld((TypeMemPtr)te._t); // Peek thru pointer
    //SB sb = to.str(new SB(),new VBitSet(),te._tmem,false);      // Print what we see, with memory
    //assertEquals(expected,strip_alias_numbers(sb.toString()));
    throw unimpl();
  }
  static private void test_isa( String program, Type expected ) {
    //TypeEnv te = run(program);
    //Type actual = te._tmem.sharptr(te._t);
    //assertTrue(actual.isa(expected));
    throw unimpl();
  }
  ////private static String strip_alias_numbers( String err ) {
  //  // Remove alias#s from the result string: *[123]@{x=1,y=2} ==> *[$]@{x=1,y=2}
  //  //     \\      Must use two \\ because of String escaping for every 1 in the regex.
  //  // Thus replacing: \[[,0-9]*  with:  \[\$
  //  // Regex breakdown:
  //  //     \\[     prevents using '[' as the start of a regex character class
  //  //     [,0-9]  matches digits and commas
  //  //     *       matches all the digits and commas
  //  //     \\[     Replacement [ because the first one got matched and replaced.
  //  //     \\$     Prevent $ being interpreted as a regex group start
  ////  return err.replaceAll("\\[[,0-9]*", "\\[\\$");
  ////}
  static private void testary( String program, String err, int cur_off ) {
    //TypeEnv te = Exec.go(Env.file_scope(new Env()),"args",program);
    //assertTrue(te._errs != null && te._errs.size()>=1);
    //String cursor = new String(new char[cur_off]).replace('\0', ' ');
    //String err2 = new SB().p("args:1:").p(err).nl().p(program).nl().p(cursor).p('^').nl().toString();
    //assertEquals(err2,te._errs.get(0).toString());
    throw unimpl();
  }
}
