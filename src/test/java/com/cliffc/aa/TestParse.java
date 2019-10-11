package com.cliffc.aa;

import com.cliffc.aa.type.*;
import org.junit.Assert;
import org.junit.Test;

import java.util.HashMap;
import java.util.function.Function;

import static org.junit.Assert.*;

public class TestParse {
  private static String[] FLDS = new String[]{"n","v"};

  // temp/junk holder for "instant" junits, when debugged moved into other tests
  @Test public void testParse() {
    Object dummy = Env.GVN; // Force class loading cycle

    // A collection of tests which like to fail easily
    testerr ("Point=:@{x,y}; Point((0,1))", "*[$](nil,1) is not a *[$]@{x=,y=}",27);
    test_ptr("x=@{n:=1,v:=2}; x.n := 3; x", "@{n:=3,v:=2}");
    testerr("dist={p->p.x*p.x+p.y*p.y}; dist(@{x=1})", "Unknown field '.y'",20);
    testerr("{+}(1,2,3)", "Passing 3 arguments to {+} which takes 2 arguments",10);
    test("x=3; mul2={x -> x*2}; mul2(2.1)+mul2(x)", TypeFlt.con(2.1*2.0+3*2)); // Mix of types to mul2(), mix of {*} operators
    testerr("x=1+y","Unknown ref 'y'",5);
    test("fact = { x -> x <= 1 ? x : x*fact(x-1) }; fact(3)",TypeInt.con(6));
    test_isa("{x y -> x+y}", TypeFunPtr.make(BitsFun.make0(BitsFun.peek()),TypeTuple.SCALAR2,Type.SCALAR)); // {Scalar Scalar -> Scalar}
    test("is_even = { n -> n ? is_odd(n-1) : 1}; is_odd = {n -> n ? is_even(n-1) : 0}; is_even(4)", TypeInt.TRUE );
    test("f0 = { f x -> x ? f(f0(f,x-1),1) : 0 }; f0({&},2)", TypeInt.FALSE);
  }

  @Test public void testParse00() {
    // Simple int
    test("1",   TypeInt.TRUE);
    // Unary operator
    test("-1",  TypeInt.con( -1));
    test("!1",  TypeInt.con(  0));
    // Binary operators
    test("1+2", TypeInt.con(  3));
    test("1-2", TypeInt.con( -1));
    test("1+2*3", TypeInt.con(  7));
    test("1  < 2", TypeInt.TRUE );
    test("1  <=2", TypeInt.TRUE );
    test("1  > 2", TypeInt.FALSE);
    test("1  >=2", TypeInt.FALSE);
    test("1  ==2", TypeInt.FALSE);
    test("1  !=2", TypeInt.TRUE );
    test("1.2< 2", TypeInt.TRUE );
    test("1.2<=2", TypeInt.TRUE );
    test("1.2> 2", TypeInt.FALSE);
    test("1.2>=2", TypeInt.FALSE);
    test("1.2==2", TypeInt.FALSE);
    test("1.2!=2", TypeInt.TRUE );

    // Binary with precedence check
    test(" 1+2 * 3+4 *5", TypeInt.con( 27));
    test("(1+2)*(3+4)*5", TypeInt.con(105));
    test("1// some comment\n+2", TypeInt.con(3)); // With bad comment

    // Float
    test("1.2+3.4", TypeFlt.make(0,64,4.6));
    // Mixed int/float with conversion
    test("1+2.3",   TypeFlt.make(0,64,3.3));

    // Simple strings
    test_ptr("\"Hello, world\"", (alias)-> TypeMemPtr.make(alias,TypeStr.con("Hello, world")));
    test_ptr("str(3.14)"   , (alias)-> TypeMemPtr.make(alias,TypeStr.con("3.14")));
    test_ptr("str(3)"      , (alias)-> TypeMemPtr.make(alias,TypeStr.con("3"   )));
    test_ptr("str(\"abc\")", (alias)-> TypeMemPtr.make(alias,TypeStr.ABC));

    // Variable lookup
    test("math_pi", TypeFlt.PI);
    // bare function lookup; returns a union of '+' functions
    testerr("+", "Syntax error; trailing junk",0);
    test("{+}", Env.lookup_valtype("+"));
    test("!", Env.lookup_valtype("!")); // uniops are just like normal functions
    // Function application, traditional paren/comma args
    test("{+}(1,2)", TypeInt.con( 3));
    test("{-}(1,2)", TypeInt.con(-1)); // binary version
    test(" - (1  )", TypeInt.con(-1)); // unary version
    // error; mismatch arg count
    testerr("!()       ", "Passing 0 arguments to !={->} which takes 1 arguments",3);
    testerr("math_pi(1)", "A function is being called, but 3.141592653589793 is not a function",10);
    testerr("{+}(1,2,3)", "Passing 3 arguments to {+} which takes 2 arguments",10);

    // Parsed as +(1,(2*3))
    test("{+}(1, 2 * 3) ", TypeInt.con(7));
    // Parsed as +( (1+2*3) , (4*5+6) )
    test("{+}(1 + 2 * 3, 4 * 5 + 6) ", TypeInt.con(33));
    // Statements
    test("(1;2 )", TypeInt.con(2));
    test("(1;2;)", TypeInt.con(2)); // final semicolon is optional
    test("{+}(1;2 ,3)", TypeInt.con(5)); // statements in arguments
    test("{+}(1;2;,3)", TypeInt.con(5)); // statements in arguments
  }

  @Test public void testParse01() {
    // Syntax for variable assignment
    test("x=1", TypeInt.TRUE);
    test("x=y=1", TypeInt.TRUE);
    testerr("x=y=", "Missing ifex after assignment of 'y'",4);
    testerr("x=z" , "Unknown ref 'z'",3);
    testerr("x=1+y","Unknown ref 'y'",5);
    testerr("x=y; x=y","Unknown ref 'y'",3);
    test("x=2; y=x+1; x*y", TypeInt.con(6));
    // Re-use ref immediately after def; parses as: x=(2*3); 1+x+x*x
    test("1+(x=2*3)+x*x", TypeInt.con(1+6+6*6));
    testerr("x=(1+(x=2)+x)", "Cannot re-assign final val 'x'",13);

    // Conditional:
    test   ("0 ?    2  : 3", TypeInt.con(3)); // false
    test   ("2 ?    2  : 3", TypeInt.con(2)); // true
    test   ("math_rand(1)?(x=4):(x=3);x", TypeInt.NINT8); // x defined on both arms, so available after
    test   ("math_rand(1)?(x=2):   3 ;4", TypeInt.con(4)); // x-defined on 1 side only, but not used thereafter
    test   ("math_rand(1)?(y=2;x=y*y):(x=3);x", TypeInt.NINT8); // x defined on both arms, so available after, while y is not
    testerr("math_rand(1)?(x=2):   3 ;x", "'x' not defined on false arm of trinary",24);
    testerr("math_rand(1)?(x=2):   3 ;y=x+2;y", "'x' not defined on false arm of trinary",24);
    testerr("0 ? (x=2) : 3;x", "'x' not defined on false arm of trinary",13);
    test   ("2 ? (x=2) : 3;x", TypeInt.con(2)); // off-side is constant-dead, so missing x-assign is ignored
    test   ("2 ? (x=2) : y  ", TypeInt.con(2)); // off-side is constant-dead, so missing 'y'      is ignored
    testerr("x=1;2?(x=2):(x=3);x", "Cannot re-assign final val 'x'",10);
    test   ("x=1;2?   2 :(x=3);x",TypeInt.con(1)); // Re-assigned allowed & ignored in dead branch
    test   ("math_rand(1)?1:int:2:int",TypeInt.NINT8); // no ambiguity between conditionals and type annotations
    testerr("math_rand(1)?1: :2:int","missing expr after ':'",16); // missing type
    testerr("math_rand(1)?1::2:int","missing expr after ':'",15); // missing type
    testerr("math_rand(1)?1:\"a\"", "Cannot mix GC and non-GC types",18);
    testerr("a.b.c();","Unknown ref 'a'",1);
  }

  @Test public void testParse02() {
    Object dummy = Env.GVN; // Force class loading cycle
    // Anonymous function definition
    test_isa("{x y -> x+y}", TypeFunPtr.make(BitsFun.make0(35),TypeTuple.SCALAR2,Type.SCALAR)); // {Scalar Scalar -> Scalar}
    test("{5}()", TypeInt.con(5)); // No args nor -> required; this is simply a function returning 5, being executed

    // ID in different contexts; in general requires a new TypeVar per use; for
    // such a small function it is always inlined completely, has the same effect.
    test("id", Env.lookup_valtype("id"));
    test("id(1)",TypeInt.con(1));
    test("id(3.14)",TypeFlt.con(3.14));
    test("id({+})",Env.lookup_valtype("+")); //
    test("id({+})(id(1),id(math_pi))",TypeFlt.make(0,64,Math.PI+1));

    // Function execution and result typing
    test("x=3; andx={y -> x & y}; andx(2)", TypeInt.con(2)); // trivially inlined; capture external variable
    test("x=3; and2={x -> x & 2}; and2(x)", TypeInt.con(2)); // trivially inlined; shadow  external variable
    testerr("plus2={x -> x+2}; x", "Unknown ref 'x'",19); // Scope exit ends lifetime
    testerr("fun={x -> }; fun(0)", "Missing function body",10);
    testerr("fun(2)", "Unknown ref 'fun'", 3);
    test("mul3={x -> y=3; x*y}; mul3(2)", TypeInt.con(6)); // multiple statements in func body
    // Needs overload cloning/inlining to resolve {+}
    test("x=3; addx={y -> x+y}; addx(2)", TypeInt.con(5)); // must inline to resolve overload {+}:Int
    test("x=3; mul2={x -> x*2}; mul2(2.1)", TypeFlt.con(2.1*2.0)); // must inline to resolve overload {*}:Flt with I->F conversion
    test("x=3; mul2={x -> x*2}; mul2(2.1)+mul2(x)", TypeFlt.con(2.1*2.0+3*2)); // Mix of types to mul2(), mix of {*} operators
    test("sq={x -> x*x}; sq 2.1", TypeFlt.con(4.41)); // No () required for single args
    testerr("sq={x -> x&x}; sq(\"abc\")", "*[$]\"abc\" is not a int64",12);
    testerr("sq={x -> x*x}; sq(\"abc\")", "*[$]\"abc\" is not a flt64",12);
    testerr("f0 = { f x -> f0(x-1) }; f0({+},2)", "Passing 1 arguments to f0={->} which takes 2 arguments",21);
    // Recursive:
    test("fact = { x -> x <= 1 ? x : x*fact(x-1) }; fact(3)",TypeInt.con(6));
    test("fib = { x -> x <= 1 ? 1 : fib(x-1)+fib(x-2) }; fib(4)",TypeInt.con(5));
    test("f0 = { x -> x ? {+}(f0(x-1),1) : 0 }; f0(2)", TypeInt.con(2));
    testerr("fact = { x -> x <= 1 ? x : x*fact(x-1) }; fact()","Passing 0 arguments to fact={->} which takes 1 arguments",48);
    test_ptr("fact = { x -> x <= 1 ? x : x*fact(x-1) }; (fact(0),fact(1),fact(2))",
             (alias)-> TypeMemPtr.make(alias,TypeStruct.make_tuple(alias,Type.NIL,TypeInt.con(1),TypeInt.con(2))));

    // Co-recursion requires parallel assignment & type inference across a lexical scope
    test("is_even = { n -> n ? is_odd(n-1) : 1}; is_odd = {n -> n ? is_even(n-1) : 0}; is_even(4)", TypeInt.TRUE );
    test("is_even = { n -> n ? is_odd(n-1) : 1}; is_odd = {n -> n ? is_even(n-1) : 0}; is_even(5)", Type.NIL  );

    // Not currently inferring top-level function return very well.  Acting
    // "as-if" called by Scalar, which pretty much guarantees a fail result.
    // Note that this is correct scenario: the returned value is reporting that
    // it might type-err on some future unknown call with Scalar args.  Would
    // like to lift the type to (i64,i64->i64) and move that future maybe-error
    // to the function args and away from the primitive call.
    //test("{x y -> x & y}", TypeFun.make(TypeFunPtr.make(TypeTuple.INT64_INT64,TypeInt.INT64,Bits.FULL,2)));

    // This test shows that I am passing a TypeFun to a CallNode, not a
    // TypeFunPtr as the test merges 2 TypeFunPtrs in a Phi.
    testerr("(math_rand(1) ? {+} : {*})(2,3)","An ambiguous function is being called"/*TypeInt.INT8*/,31); // either 2+3 or 2*3, or {5,6} which is INT8.
  }

  @Test public void testParse03() {
    // Type annotations
    test("-1:int", TypeInt.con( -1));
    test("(1+2.3):flt", TypeFlt.make(0,64,3.3));
    test("x:int = 1", TypeInt.TRUE);
    test("x:flt = 1", TypeInt.TRUE); // casts for free to a float
    testerr("x:flt32 = 123456789", "123456789 is not a flt32",19);
    testerr("1:","Syntax error; trailing junk",1); // missing type
    testerr("2:x", "Syntax error; trailing junk", 1);
    testerr("(2:)", "Syntax error; trailing junk", 2);

    test   (" -1 :int1", TypeInt.con(-1));
    testerr("(-1):int1", "-1 is not a int1",9);
    testerr("\"abc\":int", "*[$]\"abc\" is not a int64",9);
    testerr("1:str", "1 is not a *[$]str",5);

    test   ("{x:int -> x*2}(1)", TypeInt.con(2)); // Types on parms
    testerr("{x:str -> x}(1)", "1 is not a *[$]str", 15);

    // Type annotations on dead args are ignored
    test   ("fun:{int str -> int}={x y -> x+2}; fun(2,3)", TypeInt.con(4));
    testerr("fun:{int str -> int}={x y -> x+y}; fun(2,3)", "3 is not a *[$]str",43);
    // Test that the type-check is on the variable and not the function.
    test_ptr("fun={x y -> x*2}; bar:{int str -> int} = fun; baz:{int @{x,y} -> int} = fun; (fun(2,3),bar(2,\"abc\"))",
            (alias -> TypeMemPtr.make(alias,TypeStruct.make_tuple(alias,TypeInt.con(4),TypeInt.con(4)))) );
    testerr("fun={x y -> x+y}; baz:{int @{x,y} -> int} = fun; (fun(2,3), baz(2,3))",
            "3 is not a *[$]@{x=,y=}", 68);

    testerr("x=3; fun:{int->int}={x -> x*2}; fun(2.1)+fun(x)", "2.1 is not a int64",40);
    test("x=3; fun:{real->real}={x -> x*2}; fun(2.1)+fun(x)", TypeFlt.con(2.1*2+3*2)); // Mix of types to fun()
    test("fun:{real->flt32}={x -> x}; fun(123 )", TypeInt.con(123 ));
    test("fun:{real->flt32}={x -> x}; fun(0.125)", TypeFlt.con(0.125));
    testerr("fun:{real->flt32}={x -> x}; fun(123456789)", "123456789 is not a flt32",26);

    // Tuple types
    test_name("A= :(       )" ); // Zero-length tuple
    test_name("A= :(   ,   )", Type.SCALAR); // One-length tuple
    test_name("A= :(   ,  ,)", Type.SCALAR  ,Type.SCALAR  );
    test_name("A= :(flt,   )", TypeFlt.FLT64 );
    test_name("A= :(flt,int)", TypeFlt.FLT64,TypeInt.INT64);
    test_name("A= :(   ,int)", Type.SCALAR  ,TypeInt.INT64);

    test_ptr("A= :(str?, int); A( \"abc\",2 )","A:(*[$],2)");
    testerr("A= :(str?, int)?","Named types are never nil",16);
  }

  @Test public void testParse04() {
    // simple anon struct tests
    test_ptr("@{x,y}", (alias -> TypeMemPtr.make(alias,TypeStruct.make(new String[]{"x","y"},TypeStruct.ts(2),TypeStruct.finals(2),alias)))); // simple anon struct decl
    testerr("a=@{x=1.2,y}; x", "Unknown ref 'x'",15);
    testerr("a=@{x=1,x=2}", "Cannot define field '.x' twice",11);
    test   ("a=@{x=1.2,y,}; a.x", TypeFlt.con(1.2)); // standard "." field naming; trailing comma optional
    testerr("(a=@{x,y}; a.)", "Missing field name after '.'",13);
    testerr("a=@{x,y}; a.x=1","Cannot re-assign final field '.x'",15);
    test   ("a=@{x=0,y=1}; b=@{x=2}  ; c=math_rand(1)?a:b; c.x", TypeInt.INT8); // either 0 or 2; structs can be partially merged
    testerr("a=@{x=0,y=1}; b=@{x=2}; c=math_rand(1)?a:b; c.y",  "Unknown field '.y'",47);
    testerr("dist={p->p.x*p.x+p.y*p.y}; dist(@{x=1})", "Unknown field '.y'",20);
    test   ("dist={p->p.x*p.x+p.y*p.y}; dist(@{x=1,y=2})", TypeInt.con(5));     // passed in to func
    test   ("dist={p->p.x*p.x+p.y*p.y}; dist(@{x=1,y=2,z=3})", TypeInt.con(5)); // extra fields OK
    test   ("dist={p:@{x,y} -> p.x*p.x+p.y*p.y}; dist(@{x=1,y=2})", TypeInt.con(5)); // Typed func arg
    test   ("a=@{x=(b=1.2)*b,y=b}; a.y", TypeFlt.con(1.2 )); // ok to use temp defs
    test   ("a=@{x=(b=1.2)*b,y=x}; a.y", TypeFlt.con(1.44)); // ok to use early fields in later defs
    testerr("a=@{x=(b=1.2)*b,y=b}; b", "Unknown ref 'b'",23);
    test   ("t=@{n=0,val=1.2}; u=math_rand(1) ? t : @{n=t,val=2.3}; u.val", TypeFlt.NFLT64); // structs merge field-by-field
    // Comments in the middle of a struct decl
    test   ("dist={p->p//qqq\n.//qqq\nx*p.x+p.y*p.y}; dist(//qqq\n@{x//qqq\n=1,y=2})", TypeInt.con(5));

    // Tuple
    test_ptr("(0,\"abc\")", (alias -> TypeMemPtr.make(alias,TypeStruct.make_tuple(alias,Type.NIL,TypeMemPtr.ABCPTR))));
    test("(1,\"abc\").0", TypeInt.TRUE);
    test("(1,\"abc\").1", TypeMemPtr.ABCPTR);

    // Named type variables
    test("gal=:flt"     , (tmap -> TypeFunPtr.make(BitsFun.make0(35),TypeTuple.make(TypeFlt.FLT64), TypeName.make0("gal",tmap,TypeFlt.FLT64,(short)0))));
    test("gal=:flt; gal", (tmap -> TypeFunPtr.make(BitsFun.make0(35),TypeTuple.make(TypeFlt.FLT64), TypeName.make0("gal",tmap,TypeFlt.FLT64,(short)0))));
    test    ("gal=:flt; 3==gal(2)+1", TypeInt.TRUE);
    test    ("gal=:flt; tank:gal = gal(2)", (tmap -> TypeName.make0("gal",tmap,TypeInt.con(2),(short)0)));
    // test    ("gal=:flt; tank:gal = 2.0", TypeName.make("gal",TypeFlt.con(2))); // TODO: figure out if free cast for bare constants?
    testerr ("gal=:flt; tank:gal = gal(2)+1", "3 is not a gal:flt64",29);

    test    ("Point=:@{x,y}; dist={p:Point -> p.x*p.x+p.y*p.y}; dist(Point(1,2))", TypeInt.con(5));
    test    ("Point=:@{x,y}; dist={p       -> p.x*p.x+p.y*p.y}; dist(Point(1,2))", TypeInt.con(5));
    testerr ("Point=:@{x,y}; dist={p:Point -> p.x*p.x+p.y*p.y}; dist((@{x=1,y=2}))", "*[$]@{x==1,y==2} is not a *[$]Point:@{x=,y=}",68);
    testerr ("Point=:@{x,y}; Point((0,1))", "*[$](nil,1) is not a *[$]@{x=,y=}",27);
    testerr("x=@{n:,}","Missing type after ':'",6);
    testerr("x=@{n=,}","Missing ifex after assignment of 'n'",6);
  }

  @Test public void testParse05() {
    // nullable and not-null pointers
    test   ("x:str? = 0", Type.NIL); // question-type allows null or not; zero digit is null
    test   ("x:str? = \"abc\"", TypeMemPtr.ABCPTR); // question-type allows null or not
    testerr("x:str  = 0", "nil is not a *[$]str", 10);
    test   ("math_rand(1)?0:\"abc\"", TypeMemPtr.ABC0);
    testerr("(math_rand(1)?0 : @{x=1}).x", "Struct might be nil when reading field '.x'", 27);
    test   ("p=math_rand(1)?0:@{x=1}; p ? p.x : 0", TypeInt.BOOL); // not-null-ness after a null-check
    test   ("x:int = y:str? = z:flt = 0", Type.NIL); // null/0 freely recasts
    test   ("\"abc\"==0", TypeInt.FALSE ); // No type error, just not null
    test   ("\"abc\"!=0", TypeInt.TRUE  ); // No type error, just not null
    test   ("nil=0; \"abc\"!=nil", TypeInt.TRUE); // Another way to name null
    test   ("a = math_rand(1) ? 0 : @{x=1}; // a is null or a struct\n"+
            "b = math_rand(1) ? 0 : @{c=a}; // b is null or a struct\n"+
            "b ? (b.c ? b.c.x : 0) : 0      // Null-safe field load", TypeInt.BOOL); // Nested null-safe field load
  }

  @Test public void testParse06() {
    test_ptr("A= :(A?, int); A(0,2)","A:(nil,2)");
    test_ptr("A= :(A?, int); A(A(0,2),3)","A:(*[$],3)");

    // Building recursive types
    test_isa("A= :int; A(1)", (tmap -> TypeName.make("A",tmap,TypeInt.INT64)));
    test_ptr("A= :(str?, int); A(0,2)","A:(nil,2)");
    // Named recursive types
    test_isa("A= :(A?, int); A(0,2)",Type.SCALAR);// No error casting (0,2) to an A
    test    ("A= :@{n=A?, v=flt}; A(@{n=0,v=1.2}).v;", TypeFlt.con(1.2));

    // TODO: Needs a way to easily test simple recursive types
    TypeEnv te3 = Exec.go(Env.top(),"args","A= :@{n=A?, v=int}");
    if( te3._errs != null ) System.err.println(te3._errs.toString());
    Assert.assertNull(te3._errs);
    TypeFunPtr tfp = (TypeFunPtr)te3._t;
    TypeMemPtr ptr = (TypeMemPtr)tfp._ret;
    TypeName tname3 = (TypeName)ptr._obj;
    assertEquals("A", tname3._name);
    TypeStruct tt3 = (TypeStruct)tname3._t;
    TypeMemPtr tnil3 = (TypeMemPtr)tt3.at(0);
    assertSame(tnil3._obj , tname3);
    assertSame(tt3.at(1), TypeInt.INT64);
    assertEquals("n",tt3._flds[0]);
    assertEquals("v",tt3._flds[1]);

    // Missing type B is also never worked on.
    test_isa("A= :@{n=B?, v=int}", TypeFunPtr.GENERIC_FUNPTR);
    test_isa("A= :@{n=B?, v=int}; a = A(0,2)", TypeMemPtr.OOP);
    test_isa("A= :@{n=B?, v=int}; a = A(0,2); a.n", Type.NIL);
    // Mutually recursive type
    test_isa("A= :@{n=B, v=int}; B= :@{n=A, v=flt}", TypeFunPtr.GENERIC_FUNPTR);
  }

  @Test public void testParse07() {
    // Passing a function recursively
    test("f0 = { f x -> x ? f(f0(f,x-1),1) : 0 }; f0({&},2)", TypeInt.FALSE);
    test("f0 = { f x -> x ? f(f0(f,x-1),1) : 0 }; f0({+},2)", TypeInt.con(2));
    test_isa("A= :@{n=A?, v=int}; f={x:A? -> x ? A(f(x.n),x.v*x.v) : 0}", TypeFunPtr.GENERIC_FUNPTR);
    test    ("A= :@{n=A?, v=flt}; f={x:A? -> x ? A(f(x.n),x.v*x.v) : 0}; f(A(0,1.2)).v;", TypeFlt.con(1.2*1.2));

    // User-defined linked list
    String ll_def = "List=:@{next,val};";
    String ll_con = "tmp=List(List(0,1.2),2.3);";
    String ll_map = "map = {fun list -> list ? List(map(fun,list.next),fun(list.val)) : 0};";
    String ll_fun = "sq = {x -> x*x};";
    String ll_apl = "map(sq,tmp);";

    test_isa(ll_def, TypeFunPtr.GENERIC_FUNPTR);
    test(ll_def+ll_con+"; tmp.next.val", TypeFlt.con(1.2));
    test_isa(ll_def+ll_con+ll_map, TypeFunPtr.GENERIC_FUNPTR);
    test_isa(ll_def+ll_con+ll_map+ll_fun, TypeFunPtr.GENERIC_FUNPTR);

    // TODO: Needs a way to easily test simple recursive types
    TypeEnv te4 = Exec.go(Env.top(),"args",ll_def+ll_con+ll_map+ll_fun+ll_apl);
    if( te4._errs != null ) System.err.println(te4._errs.toString());
    Assert.assertNull(te4._errs);
    TypeMemPtr tmp4 = (TypeMemPtr)te4._t;
    TypeObj tobj4 = tmp4._obj;
    TypeName tname4 = (TypeName)tobj4;
    assertEquals("List", tname4._name);
    TypeStruct tt4 = (TypeStruct)tname4._t;
    TypeMemPtr tmp5 = (TypeMemPtr)tt4.at(0);
    TypeName tname5 = (TypeName)tmp5._obj;
    assertEquals(2.3*2.3,tt4.at(1).getd(),1e-6);
    assertEquals("next",tt4._flds[0]);
    assertEquals("val",tt4._flds[1]);

    assertEquals("List", tname5._name);
    TypeStruct tt5 = (TypeStruct)tname5._t;
    assertEquals(1.2*1.2,tt5.at(1).getd(),1e-6);
    assertEquals(Type.NIL,tt5.at(0));

    // Test inferring a recursive struct type, with a little help
    Type[] ts0 = new Type[]{Type.NIL,TypeFlt.con(1.2*1.2)};
    test_ptr("map={x:@{n,v=flt}? -> x ? @{n=map(x.n),v=x.v*x.v} : 0}; map(@{n=0,v=1.2})",
             (alias) -> TypeMemPtr.make(alias,TypeStruct.make(FLDS,ts0,TypeStruct.finals(2),alias)));

    // Test inferring a recursive struct type, with less help.  This one
    // inlines so doesn't actually test inferring a recursive type.
    test_ptr("map={x -> x ? @{n=map(x.n),v=x.v*x.v} : 0}; map(@{n=0,v=1.2})",
             (alias) -> TypeMemPtr.make(alias,TypeStruct.make(FLDS,ts0,TypeStruct.finals(2),alias)));

    // Test inferring a recursive struct type, with less help. Too complex to
    // inline, so actual inference happens
    test_ptr_isa("map={x -> x ? @{n=map(x.n),v=x.v*x.v} : 0};"+
                 "map(@{n=math_rand(1)?0:@{n=math_rand(1)?0:@{n=math_rand(1)?0:@{n=0,v=1.2},v=2.3},v=3.4},v=4.5})",
                 (alias) -> TypeMemPtr.make(alias,TypeStruct.make(FLDS,TypeMemPtr.STRUCT0,TypeFlt.con(20.25))));

    // Test inferring a recursive tuple type, with less help.  This one
    // inlines so doesn't actually test inferring a recursive type.
    test_ptr("map={x -> x ? (map(x.0),x.1*x.1) : 0}; map((0,1.2))",
             (alias) -> TypeMemPtr.make(alias,TypeStruct.make_tuple(alias,Type.NIL,TypeFlt.con(1.2*1.2))));

    test_ptr_isa("map={x -> x ? (map(x.0),x.1*x.1) : 0};"+
                 "map((math_rand(1)?0: (math_rand(1)?0: (math_rand(1)?0: (0,1.2), 2.3), 3.4), 4.5))",
                 (alias) -> TypeMemPtr.make(alias,TypeStruct.make(TypeMemPtr.STRUCT0,TypeFlt.con(20.25))));

    // TODO: Need real TypeVars for these
    //test("id:{A->A}"    , Env.lookup_valtype("id"));
    //test("id:{A:int->A}", Env.lookup_valtype("id"));
    //test("id:{int->int}", Env.lookup_valtype("id"));
  }


  @Test public void testParse08() {
    // A linked-list mixing ints and strings, always in pairs
    String ll_cona = "a=0; ";
    String ll_conb = "b=math_rand(1) ? ((a,1),\"abc\") : a; ";
    String ll_conc = "c=math_rand(1) ? ((b,2),\"def\") : b; ";
    String ll_cond = "d=math_rand(1) ? ((c,3),\"ghi\") : c; ";
    String ll_cone = "e=math_rand(1) ? ((d,4),\"jkl\") : d; ";
    String ll_cont = "tmp=e; ";
    // Standard pair-UN-aware map call
    String ll_map2 = "map = {fun list -> list ? (map(fun,list.0),fun(list.1)) : 0};";
    String ll_fun2 = "plus = {x -> x+x};";
    String ll_apl2 = "map(plus,tmp);";
    // End type: ((((*?,scalar)?,str)?,int64),str)?

    // After inlining once, we become pair-aware.
    test_isa(ll_cona+ll_conb+ll_conc+ll_cond+ll_cone+ll_cont+ll_map2+ll_fun2+ll_apl2,
             TypeMemPtr.make(BitsAlias.RECBITS0,TypeStruct.make(TypeMemPtr.make(BitsAlias.RECBITS0,TypeStruct.make(TypeMemPtr.STRUCT0,TypeInt.INT64)),TypeMemPtr.STRPTR)));

    // Failed attempt at a Tree-structure inference test.  Triggered all sorts
    // of bugs and error reporting issues, so keeping it as a regression test.
    testerr("tmp=@{"+
         "  l=@{"+
         "    l=@{ l=0, r=0, v=3 },"+
         "    l=@{ l=0, r=0, v=7 },"+
         "    v=5"+
         "  },"+
         "  r=@{"+
         "    l=@{ l=0, r=0, v=15 },"+
         "    l=@{ l=0, r=0, v=22 },"+
         "    v=20"+
         "  },"+
         "  v=12 "+
         "};"+
         "map={tree fun -> tree"+
         "     ? @{l=map(tree.l,fun),r=map(tree.r,fun),v=fun(tree.v)}"+
         "     : 0};"+
         "map(tmp,{x->x+x})",
            "Cannot define field '.l' twice",61);

    // Good tree-structure inference test
    test_ptr("tmp=@{"+
         "  l=@{"+
         "    l=@{ l=0, r=0, v=3 },"+
         "    r=@{ l=0, r=0, v=7 },"+
         "    v=5"+
         "  },"+
         "  r=@{"+
         "    l=@{ l=0, r=0, v=15 },"+
         "    r=@{ l=0, r=0, v=22 },"+
         "    v=20"+
         "  },"+
         "  v=12 "+
         "};"+
         "map={tree fun -> tree"+
         "     ? @{l=map(tree.l,fun),r=map(tree.r,fun),v=fun(tree.v)}"+
         "     : 0};"+
         "map(tmp,{x->x+x})",
         "@{l==*[$],r==*[$],v==int64}");
  }

  @Test public void testParse09() {
    // Test re-assignment
    test("x=1", TypeInt.TRUE);
    test("x=y=1", TypeInt.TRUE);
    testerr("x=y=", "Missing ifex after assignment of 'y'",4);
    testerr("x=z" , "Unknown ref 'z'",3);
    testerr("x=1+y","Unknown ref 'y'",5);

    test("x:=1", TypeInt.TRUE);
    test_ptr("x:=0; a=x; x:=1; b=x; x:=2; (a,b,x)", (alias) -> TypeMemPtr.make(alias,TypeStruct.make_tuple(alias,Type.NIL,TypeInt.con(1),TypeInt.con(2))));

    testerr("x=1; x:=2", "Cannot re-assign final val 'x'", 9);
    testerr("x=1; x=2", "Cannot re-assign final val 'x'", 8);

    test("math_rand(1)?(x=4):(x=3);x", TypeInt.NINT8); // x defined on both arms, so available after
    test("math_rand(1)?(x:=4):(x:=3);x", TypeInt.NINT8); // x defined on both arms, so available after
    test("math_rand(1)?(x:=4):(x:=3);x:=x+1", TypeInt.INT64); // x mutable on both arms, so mutable after
    test   ("x:=0; 1 ? (x:=4):; x:=x+1", TypeInt.con(5)); // x mutable ahead; ok to mutate on 1 arm and later
    test   ("x:=0; 1 ? (x =4):; x", TypeInt.con(4)); // x final on 1 arm, dead on other arm
    // TODO: Allow? because just flag x as read-only past trinary
    testerr("x:=0; math_rand(1) ? (x =4):3; x", "'x' not final on false arm of trinary",29); // x mutable ahead; ok to mutate on 1 arm and later
  }


  // Finals are declared with an assignment.  This is to avoid the C++/Java
  // problem of making final-field cycles.  Java requires final fields to be
  // only assigned in constructors before the value escapes, which prevents any
  // final-cyclic structures.  Final assignments have to be unambiguous - they
  // fold into a 'New' at some point, same as casting to a 'Name', but they can
  // interleave with other operations (such as other News) as long as the store
  // is unambiguous.
  //                                                   unknown
  // Field mod status makes a small lattice:      final       read/write
  //                                                  read-only
  // Type-error if a final assignment does not fold into a New.
  // Cannot cast final to r/w, nor r/w to final.
  // Can cast both to r/o.

  @Test public void testParse10() {
    // Test re-assignment in struct
    Type[] ts = TypeStruct.ts(TypeInt.con(1), TypeInt.con(2));
    test_ptr("x=@{n:=1,v:=2}", (alias) -> TypeMemPtr.make(alias,TypeStruct.make(FLDS, ts,TypeStruct.frws(2),alias)));
    testerr ("x=@{n =1,v:=2}; x.n  = 3; ", "Cannot re-assign final field '.n'",24);
    test    ("x=@{n:=1,v:=2}; x.n  = 3", TypeInt.con(3));
    test_ptr("x=@{n:=1,v:=2}; x.n := 3; x", "@{n:=3,v:=2}");
    testerr ("x=@{n:=1,v:=2}; x.n  = 3; x.v = 1; x.n = 4", "Cannot re-assign final field '.n'",42);
    test    ("x=@{n:=1,v:=2}; y=@{n=3,v:=4}; tmp = math_rand(1) ? x : y; tmp.n", TypeInt.NINT8);
    testerr ("x=@{n:=1,v:=2}; y=@{n=3,v:=4}; tmp = math_rand(1) ? x : y; tmp.n = 5", "Cannot re-assign final field '.n'",68);
    test    ("x=@{n:=1,v:=2}; foo={q -> q.n=3}; foo(x); x.n",TypeInt.con(3)); // Side effects persist out of functions
    // Tuple assignment
    testerr ("x=(1,2); x.0=3; x", "Cannot re-assign final field '.0'",14);
    // Final-only type syntax.
    testerr ("ptr2rw = @{f:=1}; ptr2final:@{f==} = ptr2rw; ptr2final", "*[$]@{f:=1} is not a *[$]@{f==}",43); // Cannot cast-to-final
    test_ptr("ptr2   = @{f =1}; ptr2final:@{f==} = ptr2  ; ptr2final", // Good cast
             (alias) -> TypeMemPtr.make(alias,TypeStruct.make(new String[]{"f"},new Type[]{TypeInt.con(1)},TypeStruct.finals(1),alias)));
    testerr ("ptr=@{f=1}; ptr2rw:@{f:=} = ptr; ptr2rw", "*[$]@{f==1} is not a *[$]@{f:=}", 31); // Cannot cast-away final

    test    ("@{x:=1,y =2}:@{x,y==}.y", TypeInt.con(2)); // Allowed reading final field
    testerr ("f={ptr2final:@{x,y==} -> ptr2final.y  }; f(@{x:=1,y:=2})", "*[$]@{x:=1,y:=2} is not a *[$]@{x=,y==}",56); // Another version of casting-to-final
    testerr ("f={ptr2final:@{x,y==} -> ptr2final.y=3}; f(@{x =1,y =2})", "Cannot re-assign final field '.y'",38);
    test    ("f={ptr:@{x=,y:=} -> ptr.y=3; ptr}; f(@{x:=1,y:=2}).y", TypeInt.con(3)); // On field x, cast-away r/w for r/o
    test    ("f={ptr:@{x==,y:=} -> ptr.y=3; ptr}; f(@{x=1,y:=2}).y", TypeInt.con(3)); // On field x, cast-up r/o for final but did not read
    test    ("f={ptr:@{x,y} -> ptr.y }; f(@{x:=1,y:=2}:@{x,y=})", TypeInt.con(2));

    // TODO: Open Question: is this legit?  Clearly a store against a read-
    // only; it is locally INCORRECT.  Turns out that only r/w memory is
    // involved.  Globally correct.  Since R/O is bottom of the access lattice,
    // all FINAL and R/W are also R/O... and having passed that check, the cast
    // to R/O can be forgotten.
    //
    //testerr ("ptr=@{f:=1}; ptr:@{f=}.f=2","Cannot re-assign read-only field '.f'",20);
    //testerr ("f={ptr:@{x,y} -> ptr.y=3}; f(@{x:=1,y:=2});"       , "Cannot re-assign read-only field '.y'",38);
    //testerr ("f={ptr:@{x,y} -> ptr.y=3}; f(@{x:=1,y:=2}:@{x,y=})", "Cannot re-assign read-only field '.y'",38);
    //
    // Need to ponder lexical scoping of access constraints; read-only is NOT a
    // final store.  Thus means access on PTRs and final on MEMs.
    //
    // ACTION: Add a MeetNode which does a Meet with a constant (very close to
    // a Phi).  Goal of MeetNode is to keep a *downcast* in order to keep the
    // following checks.  Can be removed when no following checks on downcast
    // value, or no downcast happens during iter().  Dunno how to check for "no
    // following checks"?  Drop the default value on phi/parm?  Add TypeNodes
    // whenever a Parm declares a type (and MeetNode?).  Note relation between
    // default on parm vs function type, and the fun()._tf value.  Use MeetNode
    // is enforce read-only casts.
    //
    // ACTION: Move read-only/read-write into TMP.  Goal: constraint on
    // read-only is lexically scoped and not e.g. memory threaded.  Goal: keep
    // final/mutable on TypeMem and memory threaded.  Goal: can declare parms
    // as read-only (equiv: cast to read-only), and honor the constraint, while
    // leaving the original ptr able to Store.
  }


  /*

"Final store" ==> memory words can become "final"; unchangable by any thread.
Which means the memory value holds the truth about writability.  Also means
cannot flip to final, if ptr to memory has "escaped".

Can cast that a ptr ptrs-to only final memory.  Type-error if memory is not
final.  Cannot cast-away "finalness"; type-error if memory is final.
  ptr2f = @{f=1};  ptr2rw:@{f:=} = ptr2f;  ptr2rw.f=2;  // type error, casting away final
  ptr2f = @{f=1};  ptr2rw:@{!f} = ptr2f;           2;  // Ok, ptr2rw is dead
  ptr2f = @{f=1};  ptr2ro:@{~f} = ptr2f;  ptr2ro.f  ;  // OK, casting away final to R/O
  ptr2f = @{f=1};  ptr2ro:@{~f} = ptr2f;  ptr2ro.f=2;  // MIGHT be ok, as store is dead
  ptr2f = @{f=1};  ptr2ro:@{~f} = ptr2f;  ptr2ro.f=2; ptr2ro.f // ERROR, store not dead and not correct

Cannot make a final on mixed memory!!!
Just like 'Naming' memory.
Final Store MUST fold into 'New' or its an error!
  ptr0 = @{f:=1}; ptr1 = @{f:=2};  ptr = (rand ? ptr0 : ptr1);  ptr.f=2;  ptr; // ERROR, final stores only into unaliased memory
  ptr0 = @{f:=1}; ptr1 = @{f:=2};  ptr = (rand ? ptr0 : ptr1);  ptr.f=2;  // MIGHT be ok, as store is dead
  ptr0 = @{f:=1}; ptr1 = @{f =2};  ptr = (rand ? ptr0 : ptr1);  ptr.f;  // OK, ptr is typed 'read-only' not final



Want to enable easy final "cycles":
  ptr0 = @{a}; ptr1 = @{a=ptr0}; ptr0.a = ptr1; // This is OK; both stores can fold into New
Basically stretching out the final assignment to interleave the constructors.
Gonna see 2 parallel News in the graph, with crossing ptr-dep edges.

Not ok if we "escape" a non-final version?
  ptr0 = @{a};
  ptr1 = @{a=ptr0};
  ...  foo=ptr0 ...   // still OK as foo will get from the 'New' which eventually gets tagged as 'final field a'
  ptr0.a = ptr1;

Can see pre-final-store variants or not?  And still safely declare 'final'?
Might work, if foo.a collapses to a '1', still requires final store into NEW.
Might type-err if cannot collapse final-store
  ptr0 = @{a := 1 };  // Field a is non-final 1
  vala = ptr.a;       // Load before final store, sees 1 not 2
  ptr0.a = 2;         // anti-dep edge prevents sliding foo.a after ptr0.a=2
  vala

ERROR, value escaped, cannot be final
  ptr0 = @{a := 1 };  // Field a is non-final 1
  ...complex(ptr0) ...  // Saves ptr0 (as r/w) somewhere deep
  ptr0.a = 2;    // anti-dep edge prevents sliding above complex.




// No ambiguity:
 { x } // no-arg-function returning external variable x; same as { -> x }
 { x,} // 1-elem struct    wrapping external variable x, without using '@{}'
@{ x } // 1-elem struct type with field named x

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

list = @{ next:nil, val:1.2 }

List = :@{ next, val }
head = { list -> list.val  } // fails to compile if list is nil
tail = { list -> list.next } // fails to compile if list is nil

map = { f list -> list ? List(@{map(f,list.next),f(list.val)}) : 0 }

// Type A can allow nulls, or not
strs:List(0)    = ... // List of nulls
strs:List(str)  = ... // List of not-null strings
strs:List(str?) = ... // List of null-or-strings

   */

  // Caller must close TypeEnv
  static private TypeEnv run( String program ) {
    TypeEnv te = Exec.open(Env.top(),"args",program);
    if( te._errs != null ) System.err.println(te._errs.toString());
    Assert.assertNull(te._errs);
    return te;
  }

  static private void test( String program, Type expected ) {
    try( TypeEnv te = run(program) ) {
      assertEquals(expected,te._t);
    }
  }
  static private void test_name( String program, Type... args ) {
    try( TypeEnv te = run(program) ) {
      assertTrue(te._t instanceof TypeFunPtr);
      TypeFunPtr actual = (TypeFunPtr)te._t;
      TypeStruct from = TypeStruct.make_tuple(args);
      TypeName to = TypeName.make0("A",te._env._scope.types(),from,(short)0);
      TypeMemPtr  inptr = TypeMemPtr.make(BitsAlias.REC,from);
      TypeMemPtr outptr = TypeMemPtr.make(BitsAlias.REC,to);
      TypeFunPtr expected = TypeFunPtr.make(actual.fidxs(),TypeTuple.make(inptr),outptr);
      assertEquals(expected,actual);
    }
  }
  static private void test_ptr( String program, Function<Integer,Type> expected ) {
    try( TypeEnv te = run(program) ) {
      assertTrue(te._t instanceof TypeMemPtr);
      int alias = ((TypeMemPtr)te._t).getbit(); // internally asserts only 1 bit set
      Type t_expected = expected.apply(alias);
      assertEquals(t_expected,te._t);
    }
  }
  // Slightly weaker than test_ptr
  static private void test_ptr_isa( String program, Function<Integer,Type> expected ) {
    try( TypeEnv te = run(program) ) {
      assertTrue(te._t instanceof TypeMemPtr);
      int alias = ((TypeMemPtr)te._t).getbit(); // internally asserts only 1 bit set
      Type t_expected = expected.apply(alias);
      assertTrue(te._t.isa(t_expected));
    }
  }
  static private void test_ptr( String program, String expected ) {
    try( TypeEnv te = run(program) ) {
      assertTrue(te._t instanceof TypeMemPtr);
      TypeObj to = te._tmem.ld((TypeMemPtr)te._t);
      assertEquals(expected,strip_alias_numbers(to.toString()));
    }
  }
  static private void test( String program, Function<HashMap<String,Type>,Type> expected ) {
    try( TypeEnv te = run(program) ) {
      Type t_expected = expected.apply(te._env._scope.types());
      assertEquals(t_expected,te._t);
    }
  }
  static private void test_isa( String program, Type expected ) {
    try( TypeEnv te = run(program) ) {
      assertTrue(te._t.isa(expected));
    }
  }
  static private void test_isa( String program, Function<HashMap<String,Type>,Type> expected ) {
    try( TypeEnv te = run(program) ) {
      Type t_expected = expected.apply(te._env._scope.types());
      assertTrue(te._t.isa(t_expected));
    }
  }
  static private void testerr( String program, String err, String cursor ) {
    System.out.println("fix test, cur_off="+cursor.length());
    fail();
  }
  static private void testerr( String program, String err, int cur_off ) {
    TypeEnv te = Exec.go(Env.top(),"args",program);
    assertTrue(te._errs != null && te._errs._len>=1);
    String cursor = new String(new char[cur_off]).replace('\0', ' ');
    String err2 = "\nargs:0:"+err+"\n"+program+"\n"+cursor+"^\n";
    assertEquals(err2,strip_alias_numbers(te._errs.at(0)));
  }
  private static String strip_alias_numbers( String err ) {
    // Remove alias#s from the result string: *[123]@{x=1,y=2} ==> *[$]@{x=1,y=2}
    //     \\      Must use two \\ because of String escaping for every 1 in the regex.
    // Thus replacing: \[[,0-9]*  with:  \[\$
    // Regex breakdown:
    //     \\[     prevents using '[' as the start of a regex character class
    //     [,0-9]  matches digits and commas
    //     *       matches all the digits and commas
    //     \\[     Replacement [ because the first one got matched and replaced.
    //     \\$     Prevent $ being interpreted as a regex group start
    return err.replaceAll("\\[[,0-9]*", "\\[\\$");
  }

}
