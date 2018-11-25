package com.cliffc.aa;

import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Bits;
import org.junit.Assert;
import org.junit.Test;

import java.util.HashMap;
import java.util.function.Function;

import static org.junit.Assert.*;

public class TestParse {
  // TODO: Observation: value() calls need to be monotonic, can test this.
  private static String[] FLDS = new String[]{"n","v"};
  
  // temp/junk holder for "instant" junits, when debugged moved into other tests
  @Test public void testParse() {

    // User-defined linked list
    String ll_con = "tmp=((((0,2),99),1),98);"; // intermix strings and ints
    String ll_map = "map = {fun list -> list ? (map(fun,list.0),fun(list.1)) : 0};";
    String ll_fun = "plus = {x -> x+x};";
    String ll_apl = "map(plus,tmp);";

    // TODO: Needs a way to easily test simple recursive types
    TypeEnv te4 = Exec.go("args",ll_con+ll_map+ll_fun+ll_apl);
    

    
    // Not currently inferring top-level function return very well.  Acting
    // "as-if" called by Scalar args, which pretty much guarantees a fail result.
    // Note that this is correct scenario: the returned value is reporting that
    // it might type-err on some future unknown call with Scalar args.  Would
    // like to lift the type to (i64,i64->i64) and move that future maybe-error
    // to the function args and away from the primitive call.
    //test("{x y -> x & y}", TypeFun.make(TypeFunPtr.make(TypeTuple.INT64_INT64,TypeInt.INT64,Bits.FULL,2)));

    // A collection of tests which like to fail easily
    test("f0 = { f x -> x ? f(f0(f,x-1),1) : 0 }; f0({&},2)", TypeInt.FALSE);
    testerr ("Point=:@{x,y}; Point((0,1))", "(nil,1) is not a @{x,y}","                           ");
    testerr("dist={p->p.x*p.x+p.y*p.y}; dist(@{x=1})", "Unknown field '.y'","                    ");
    testerr("{+}(1,2,3)", "Passing 3 arguments to +{flt64 flt64 -> flt64} which takes 2 arguments","          ");
    test("x=3; mul2={x -> x*2}; mul2(2.1)+mul2(x)", TypeFlt.con(2.1*2.0+3*2)); // Mix of types to mul2(), mix of {*} operators
    testerr("x=1+y","Unknown ref 'y'","     ");
    test("fact = { x -> x <= 1 ? x : x*fact(x-1) }; fact(3)",TypeInt.con(6));
    test_isa("{x y -> x+y}", TypeFun.FUN2); // {Flt,Int} x {Flt,Int} -> {Flt,Int}
    test("is_even = { n -> n ? is_odd(n-1) : 1}; is_odd = {n -> n ? is_even(n-1) : 0}; is_even(4)", TypeInt.BOOL );

  }
  
  @Test public void testParse0() {
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
    test("\"Hello, world\"", TypeStr.con("Hello, world"));
    test("str(3.14)", TypeStr.con("3.14"));
    test("str(3)", TypeStr.con("3"));
    test("str(\"abc\")", TypeStr.ABC);

    // Variable lookup
    test("math_pi", TypeFlt.PI);
    // bare function lookup; returns a union of '+' functions
    testerr("+", "Syntax error; trailing junk","");
    test("{+}", Env.lookup_valtype("+"));
    test("!", Env.lookup_valtype("!")); // uniops are just like normal functions
    // Function application, traditional paren/comma args
    test("{+}(1,2)", TypeInt.con( 3));
    test("{-}(1,2)", TypeInt.con(-1)); // binary version
    test(" - (1  )", TypeInt.con(-1)); // unary version
    // error; mismatch arg count
    testerr("!()       ", "Passing 0 arguments to !{int64 -> int1} which takes 1 arguments","   ");
    testerr("math_pi(1)", "A function is being called, but 3.141592653589793 is not a function type","          ");
    testerr("{+}(1,2,3)", "Passing 3 arguments to +{flt64 flt64 -> flt64} which takes 2 arguments","          ");

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
  
  @Test public void testParse1() {
    // Syntax for variable assignment
    test("x=1", TypeInt.TRUE);
    test("x=y=1", TypeInt.TRUE);
    testerr("x=y=", "Missing ifex after assignment of 'y'","    ");
    testerr("x=z" , "Unknown ref 'z'","   ");
    testerr("x=1+y","Unknown ref 'y'","     ");
    test("x=2; y=x+1; x*y", TypeInt.con(6));
    // Re-use ref immediately after def; parses as: x=(2*3); 1+x+x*x
    test("1+(x=2*3)+x*x", TypeInt.con(1+6+6*6));
    testerr("x=(1+(x=2)+x)", "Cannot re-assign val 'x'","             ");

    // Conditional:
    test   ("0 ?    2  : 3", TypeInt.con(3)); // false
    test   ("2 ?    2  : 3", TypeInt.con(2)); // true
    test   ("math_rand(1)?(x=4):(x=3);x", TypeInt.NINT8); // x defined on both arms, so available after
    test   ("math_rand(1)?(x=2):   3 ;4", TypeInt.con(4)); // x-defined on 1 side only, but not used thereafter
    test   ("math_rand(1)?(y=2;x=y*y):(x=3);x", TypeInt.NINT8); // x defined on both arms, so available after, while y is not
    testerr("math_rand(1)?(x=2):   3 ;x", "'x' not defined on false arm of trinary","                        ");
    testerr("math_rand(1)?(x=2):   3 ;y=x+2;y", "'x' not defined on false arm of trinary","                        ");
    testerr("0 ? (x=2) : 3;x", "'x' not defined on false arm of trinary","             ");
    test   ("2 ? (x=2) : 3;x", TypeInt.con(2)); // off-side is constant-dead, so missing x-assign is ignored
    test   ("2 ? (x=2) : y  ", TypeInt.con(2)); // off-side is constant-dead, so missing 'y'      is ignored
    testerr("x=1;2?(x=2):(x=3);x", "Cannot re-assign val 'x'","          ");
    test   ("x=1;2?   2 :(x=3);x",TypeInt.con(1)); // Re-assigned allowed & ignored in dead branch
    test   ("math_rand(1)?1:int:2:int",TypeInt.NINT8); // no ambiguity between conditionals and type annotations
    testerr("math_rand(1)?1: :2:int","missing expr after ':'","                "); // missing type
    testerr("math_rand(1)?1::2:int","missing expr after ':'","               "); // missing type
    testerr("math_rand(1)?1:\"a\"", "Cannot mix GC and non-GC types", "                  " );
  }

  @Test public void testParse2() {
    // Anonymous function definition
    test_isa("{x y -> x+y}", TypeFun.FUN2); // {SCALAR,SCALAR->SCALAR}
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
    testerr("plus2={x -> x+2}; x", "Unknown ref 'x'","                   "); // Scope exit ends lifetime
    testerr("fun={x -> }; fun(0)", "Missing function body","          ");
    testerr("fun(2)", "Unknown ref 'fun'", "      ");
    test("mul3={x -> y=3; x*y}; mul3(2)", TypeInt.con(6)); // multiple statements in func body
    // Needs overload cloning/inlining to resolve {+}
    test("x=3; addx={y -> x+y}; addx(2)", TypeInt.con(5)); // must inline to resolve overload {+}:Int
    test("x=3; mul2={x -> x*2}; mul2(2.1)", TypeFlt.con(2.1*2.0)); // must inline to resolve overload {*}:Flt with I->F conversion
    test("x=3; mul2={x -> x*2}; mul2(2.1)+mul2(x)", TypeFlt.con(2.1*2.0+3*2)); // Mix of types to mul2(), mix of {*} operators
    test("sq={x -> x*x}; sq 2.1", TypeFlt.con(4.41)); // No () required for single args
    testerr("f0 = { f x -> f0(x-1) }; f0({+},2)", "Passing 1 arguments to f0{Scalar Scalar -> Scalar} which takes 2 arguments","                     ");
    // Recursive:
    test("fact = { x -> x <= 1 ? x : x*fact(x-1) }; fact(3)",TypeInt.con(6));
    test("fib = { x -> x <= 1 ? 1 : fib(x-1)+fib(x-2) }; fib(4)",TypeInt.INT64);
    test("f0 = { x -> x ? {+}(f0(x-1),1) : 0 }; f0(2)", TypeInt.con(2));

    // Co-recursion requires parallel assignment & type inference across a lexical scope
    test("is_even = { n -> n ? is_odd(n-1) : 1}; is_odd = {n -> n ? is_even(n-1) : 0}; is_even(4)", TypeInt.BOOL );
    test("is_even = { n -> n ? is_odd(n-1) : 1}; is_odd = {n -> n ? is_even(n-1) : 0}; is_even(5)", TypeInt.BOOL);

    // Not currently inferring top-level function return very well.  Acting
    // "as-if" called by Scalar, which pretty much guarantees a fail result.
    // Note that this is correct scenario: the returned value is reporting that
    // it might type-err on some future unknown call with Scalar args.  Would
    // like to lift the type to (i64,i64->i64) and move that future maybe-error
    // to the function args and away from the primitive call.
    //test("{x y -> x & y}", TypeFun.make(TypeFunPtr.make(TypeTuple.INT64_INT64,TypeInt.INT64,Bits.FULL,2)));
  }

  @Test public void testParse3() {
    // Type annotations
    test("-1:int", TypeInt.con( -1));
    test("(1+2.3):flt", TypeFlt.make(0,64,3.3));
    test("x:int = 1", TypeInt.TRUE);
    test("x:flt = 1", TypeInt.TRUE); // casts for free to a float
    testerr("x:flt32 = 123456789", "123456789 is not a flt32","                   ");
    testerr("1:","Syntax error; trailing junk"," "); // missing type
    testerr("2:x", "Syntax error; trailing junk", " ");
    testerr("(2:)", "Syntax error; trailing junk", "  ");

    test   (" -1 :int1", TypeInt.con(-1));
    testerr("(-1):int1", "-1 is not a int1","         ");
    testerr("\"abc\":int", "\"abc\" is not a int64","         ");
    testerr("1:str", "1 is not a str","     ");

    testerr("x=3; fun:{int->int}={x -> x*2}; fun(2.1)+fun(x)", "2.1 is not a int64","                              ");
    test("x=3; fun:{real->real}={x -> x*2}; fun(2.1)+fun(x)", TypeFlt.con(2.1*2+3*2)); // Mix of types to fun()
    test("fun:{real->flt32}={x -> x}; fun(123 )", TypeInt.con(123 ));
    test("fun:{real->flt32}={x -> x}; fun(0.125)", TypeFlt.con(0.125));
    testerr("fun:{real->flt32}={x -> x}; fun(123456789)", "123456789 is not a flt32","                          ");

    test   ("{x:int -> x*2}(1)", TypeInt.con(2)); // Types on parms
    testerr("{x:str -> x}(1)", "1 is not a str", "               ");

    // Tuple types
    test_isa("A= :(         )", name_tuple_constructor()); // Zero-length tuple
    test_isa("A= :(    ,    )", name_tuple_constructor(Type.SCALAR)); // One-length tuple
    test_isa("A= :(    ,   ,)", name_tuple_constructor(Type.SCALAR  ,Type.SCALAR  ));
    test_isa("A= :(:flt,    )", name_tuple_constructor(TypeFlt.FLT64 ));
    test_isa("A= :(:flt,:int)", name_tuple_constructor(TypeFlt.FLT64,TypeInt.INT64));
    test_isa("A= :(    ,:int)", name_tuple_constructor(Type.SCALAR  ,TypeInt.INT64));

    test   ("A= :(:str?, :int); A((\"abc\",2))",(tmap -> TypeName.make("A",tmap,TypeStruct.make(TypeStr.ABC,TypeInt.con(2)))));
    test   ("A= :(:str?, :int); A( \"abc\",2 )",(tmap -> TypeName.make("A",tmap,TypeStruct.make(TypeStr.ABC,TypeInt.con(2)))));
    testerr("A= :(:str?, :int)?","Named types are never nil","                  ");
  }
  static private Function<HashMap<String,Type>,Type> name_tuple_constructor(Type... ts) {
    TypeStruct tt = TypeStruct.make(ts);
    return (tmap -> TypeFun.make(TypeFunPtr.make(TypeTuple.make(tt),TypeName.make("A",tmap,tt),Bits.FULL,1)));
  }

  @Test public void testParse4() {
    // simple anon struct tests
    test   ("  @{x,y} ", TypeStruct.make(new String[]{"x","y"},Type.SCALAR,Type.SCALAR)); // simple anon struct decl
    testerr("a=@{x=1.2,y}; x", "Unknown ref 'x'","               ");
    testerr("a=@{x=1,x=2}", "Cannot define field '.x' twice","           ");
    test   ("a=@{x=1.2,y,}; a.x", TypeFlt.con(1.2)); // standard "." field naming; trailing comma optional
    testerr("(a=@{x,y}; a.)", "Missing field name after '.'","             ");
    testerr("a=@{x,y}; a.x=1","Cannot re-assign field '.x'","               ");
    test   ("a=@{x=0,y=1}; b=@{x=2}  ; c=math_rand(1)?a:b; c.x", TypeInt.INT8); // either 0 or 2; structs can be partially merged
    testerr("a=@{x=0,y=1}; b=@{x=2}; c=math_rand(1)?a:b; c.y",  "Unknown field '.y'","                                               ");
    testerr("dist={p->p.x*p.x+p.y*p.y}; dist(@{x=1})", "Unknown field '.y'","                    ");
    test   ("dist={p->p.x*p.x+p.y*p.y}; dist(@{x=1,y=2})", TypeInt.con(5));     // passed in to func
    test   ("dist={p->p.x*p.x+p.y*p.y}; dist(@{x=1,y=2,z=3})", TypeInt.con(5)); // extra fields OK
    test   ("dist={p:@{x,y} -> p.x*p.x+p.y*p.y}; dist(@{x=1,y=2})", TypeInt.con(5)); // Typed func arg
    test   ("a=@{x=(b=1.2)*b,y=b}; a.y", TypeFlt.con(1.2 )); // ok to use temp defs
    test   ("a=@{x=(b=1.2)*b,y=x}; a.y", TypeFlt.con(1.44)); // ok to use early fields in later defs
    testerr("a=@{x=(b=1.2)*b,y=b}; b", "Unknown ref 'b'","                       ");
    test   ("t=@{n=0,val=1.2}; u=math_rand(1) ? t : @{n=t,val=2.3}; u.val", TypeFlt.NFLT64); // structs merge field-by-field
    // Comments in the middle of a struct decl
    test   ("dist={p->p//qqq\n.//qqq\nx*p.x+p.y*p.y}; dist(//qqq\n@{x//qqq\n=1,y=2})", TypeInt.con(5));

    // Tuple
    test("(0,\"abc\")", TypeStruct.make(TypeNil.NIL,TypeStr.ABC));
    test("(1,\"abc\").0", TypeInt.TRUE);
    test("(1,\"abc\").1", TypeStr.ABC);
    
    // Named type variables
    test_isa("gal=:flt"       , (tmap -> TypeFun.make(TypeFunPtr.make(TypeTuple.FLT64,TypeName.make("gal",tmap,TypeFlt.FLT64),Bits.FULL,1))));
    test_isa("gal=:flt; gal"  , (tmap -> TypeFun.make(TypeFunPtr.make(TypeTuple.FLT64,TypeName.make("gal",tmap,TypeFlt.FLT64),Bits.FULL,1))));
    test    ("gal=:flt; 3==gal(2)+1", TypeInt.TRUE);
    test    ("gal=:flt; tank:gal = gal(2)", (tmap -> TypeName.make("gal",tmap,TypeFlt.con(2))));
    // test    ("gal=:flt; tank:gal = 2.0", TypeName.make("gal",TypeFlt.con(2))); // TODO: figure out if free cast for bare constants?
    testerr ("gal=:flt; tank:gal = gal(2)+1", "3.0 is not a gal:flt64","                             ");
    
    test    ("A= :(:str?, :int); A( \"abc\",2 )",(tmap -> TypeName.make("A",tmap,TypeStruct.make(TypeStr.ABC,TypeInt.con(2)))));
    test    ("Point=:@{x,y}; dist={p:Point -> p.x*p.x+p.y*p.y}; dist(Point(1,2))", TypeInt.con(5));
    test    ("Point=:@{x,y}; dist={p       -> p.x*p.x+p.y*p.y}; dist(Point(1,2))", TypeInt.con(5));
    testerr ("Point=:@{x,y}; dist={p:Point -> p.x*p.x+p.y*p.y}; dist((@{x=1,y=2}))", "@{x:1,y:2} is not a Point:@{x,y}","                                                                    ");
    testerr ("Point=:@{x,y}; Point((0,1))", "(nil,1) is not a @{x,y}","                           ");
  }

  @Test public void testParse5() {
    // nullable and not-null pointers
    test   ("x:str? = 0", TypeNil.NIL); // question-type allows null or not; zero digit is null
    test   ("x:str? = \"abc\"", TypeStr.ABC); // question-type allows null or not
    testerr("x:str  = 0", "nil is not a str", "          ");
    test   ("math_rand(1)?0:\"abc\"", TypeNil.ABC);
    testerr("(math_rand(1)?0 : @{x=1}).x", "Struct might be nil when reading field '.x'", "                           ");
    test   ("p=math_rand(1)?0:@{x=1}; p ? p.x : 0", TypeInt.BOOL); // not-null-ness after a null-check
    test   ("x:int = y:str? = z:flt = 0", TypeNil.NIL); // null/0 freely recasts
    test   ("\"abc\"==0", TypeInt.FALSE ); // No type error, just not null
    test   ("\"abc\"!=0", TypeInt.TRUE  ); // No type error, just not null
    test   ("nil=0; \"abc\"!=nil", TypeInt.TRUE); // Another way to name null
    test   ("a = math_rand(1) ? 0 : @{x=1}; // a is null or a struct\n"+
            "b = math_rand(1) ? 0 : @{c=a}; // b is null or a struct\n"+
            "b ? (b.c ? b.c.x : 0) : 0      // Null-safe field load", TypeInt.BOOL); // Nested null-safe field load
  }

  @Test public void testParse6() {
    test_isa("A= :(:A?, :int); A(0,2)",(tmap -> TypeName.make("A",tmap,TypeStruct.make(TypeNil.NIL,TypeInt.con(2)))));
    test_isa("A= :(:A?, :int); A(A(0,2),3)",(tmap -> TypeName.make("A",tmap,TypeStruct.make(TypeName.make("A",tmap,TypeStruct.make(TypeNil.NIL,TypeInt.con(2))),TypeInt.con(3)))));
    
    // Building recursive types
    test_isa("A= :int; A(1)", (tmap -> TypeName.make("A",tmap,TypeInt.INT64)));
    test("A= :(:str?, :int); A(0,2)",(tmap -> TypeName.make("A",tmap,TypeStruct.make(TypeNil.NIL,TypeInt.con(2)))));
    // Named recursive types
    test_isa("A= :(:A?, :int); A(0,2)",Type.SCALAR);// No error casting (0,2) to an A
    test_isa("A= :@{n:A?, v:flt}; A(@{n=0,v=1.2}).v;", TypeFlt.con(1.2));

    // TODO: Needs a way to easily test simple recursive types
    TypeEnv te3 = Exec.go("args","A= :@{n:A?, v:int}");
    if( te3._errs != null ) System.err.println(te3._errs.toString());
    Assert.assertNull(te3._errs);
    TypeName tname3 = (TypeName)((TypeFun)te3._t).val();
    assertEquals("A", tname3._name);
    TypeStruct tt3 = (TypeStruct)tname3._t;
    TypeNil tnil3 = (TypeNil)tt3.at(0);
    assertSame(tnil3._t , tname3);
    assertSame(tt3.at(1), TypeInt.INT64);
    assertEquals("n",tt3._flds[0]);
    assertEquals("v",tt3._flds[1]);

    // Missing type B is also never worked on.
    test_isa("A= :@{n:B?, v:int}", Type.SCALAR);
    test_isa("A= :@{n:B?, v:int}; a = A(0,2)", Type.SCALAR);
    test_isa("A= :@{n:B?, v:int}; a = A(0,2); a.n", TypeNil.NIL);
    // Mutually recursive type
    test_isa("A= :@{n:B, v:int}; B= :@{n:A, v:flt}", Type.SCALAR);
  }

  @Test public void testParse7() {
    // Passing a function recursively
    test("f0 = { f x -> x ? f(f0(f,x-1),1) : 0 }; f0({&},2)", TypeInt.FALSE);
    test("f0 = { f x -> x ? f(f0(f,x-1),1) : 0 }; f0({+},2)", TypeInt.con(2));
    test_isa("A= :@{n:A?, v:int}; f={x:A? -> x ? A(f(x.n),x.v*x.v) : 0}", TypeFun.GENERIC_FUN);
    test_isa("A= :@{n:A?, v:flt}; f={x:A? -> x ? A(f(x.n),x.v*x.v) : 0}; f(A(0,1.2)).v;", TypeFlt.con(1.2*1.2));

    // User-defined linked list
    String ll_def = "List=:@{next,val};";
    String ll_con = "tmp=List(List(0,1.2),2.3);";
    String ll_map = "map = {fun list -> list ? List(map(fun,list.next),fun(list.val)) : 0};";
    String ll_fun = "sq = {x -> x*x};";
    String ll_apl = "map(sq,tmp);";

    test_isa(ll_def, TypeFun.GENERIC_FUN);
    test(ll_def+ll_con+"; tmp.next.val", TypeFlt.con(1.2));
    //test(ll_def+ll_con+ll_map, TypeFun.GENERIC_FUN);
    test_isa(ll_def+ll_con+ll_map+ll_fun, TypeFun.GENERIC_FUN);

    // TODO: Needs a way to easily test simple recursive types
    TypeEnv te4 = Exec.go("args",ll_def+ll_con+ll_map+ll_fun+ll_apl);
    if( te4._errs != null ) System.err.println(te4._errs.toString());
    Assert.assertNull(te4._errs);
    TypeName tname4 = (TypeName)te4._t;
    assertEquals("List", tname4._name);
    TypeStruct tt4 = (TypeStruct)tname4._t;
    TypeName tname5 = (TypeName)tt4.at(0);
    assertEquals(2.3*2.3,tt4.at(1).getd(),1e-6);
    assertEquals("next",tt4._flds[0]);
    assertEquals("val",tt4._flds[1]);
    
    assertEquals("List", tname5._name);
    TypeStruct tt5 = (TypeStruct)tname5._t;
    assertEquals(TypeNil.NIL,tt5.at(0));
    assertEquals(1.2*1.2,tt5.at(1).getd(),1e-6);
    
    // Test inferring a recursive struct type, with a little help
    test("map={x:@{n,v:flt}? -> x ? @{n=map(x.n),v=x.v*x.v} : 0}; map(@{n=0,v=1.2})",
         TypeStruct.make(FLDS,TypeNil.NIL,TypeFlt.con(1.2*1.2)));

    // Test inferring a recursive struct type, with less help.  This one
    // inlines so doesn't actually test inferring a recursive type.
    test("map={x -> x ? @{n=map(x.n),v=x.v*x.v} : 0}; map(@{n=0,v=1.2})",
         TypeStruct.make(FLDS,TypeNil.NIL,TypeFlt.con(1.2*1.2)));

    // Test inferring a recursive struct type, with less help. Too complex to
    // inline, so actual inference happens
    TypeStruct.init1();
    test_isa("map={x -> x ? @{n=map(x.n),v=x.v*x.v} : 0};"+
         "map(@{n=math_rand(1)?0:@{n=math_rand(1)?0:@{n=math_rand(1)?0:@{n=0,v=1.2},v=2.3},v=3.4},v=4.5})",
         TypeStruct.make(FLDS,TypeNil.make(TypeStruct.RECURS_NIL_FLT),TypeFlt.con(4.5*4.5)));
    
    // Test inferring a recursive tuple type, with less help.  This one
    // inlines so doesn't actually test inferring a recursive type.
    test("map={x -> x ? (map(x.0),x.1*x.1) : 0}; map((0,1.2))",
         TypeStruct.make(TypeNil.NIL,TypeFlt.con(1.2*1.2)));

    test_isa("map={x -> x ? (map(x.0),x.1*x.1) : 0};"+
         "map((math_rand(1)?0: (math_rand(1)?0: (math_rand(1)?0: (0,1.2), 2.3), 3.4), 4.5))",
         TypeStruct.make(TypeNil.make(TypeStruct.RECURT_NIL_FLT),TypeFlt.con(4.5*4.5)));
    
    // TODO: Need real TypeVars for these
    //test("id:{A->A}"    , Env.lookup_valtype("id"));
    //test("id:{A:int->A}", Env.lookup_valtype("id"));
    //test("id:{int->int}", Env.lookup_valtype("id"));
  }

  /*

// No ambiguity:
 { x } // no-arg-function returning external variable x; same as { -> x }
 { x,} // 1-elem tuple     wrapping external variable x
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

// TODO: Re-assignment; ':=' allows more ':=' or exactly 1 final assignment '='
x := 1; x:= 2; x = 3; x // 3
x  = 1; x = 2; // cannot reassign
x  = 1; x:= 2; // cannot reassign
x := 1; rand ? x =2 :  3; x; // cannot partially final-assign
x := 1; rand ? x:=2 :  3; x; // 2; x is still assignable
x := 1; rand ? x =2 :x=3; x; // 2or3; x is final
x := 1; x = x; // 1; make x final

// With re-assignment, more excitement around LHS!
// So fields in a tuple type have a init-value, a final-value, an
// un-init-value, a mixed-init-value, and a name
make_point={{x,y}} // returns {x,y} with both un-init
a=make_point(); a.x=1; // a.x init; a.y uninit
b=make_point(); b.y=2; // a.x uninit; b.y init
c = rand ? a : b;      // c: worse-case x & y mixed init & uninit
c.x = 1; // Error; might be    init
c.x;     // Error; might be un-init
// reflection read/write of fields.
// '[' binary operator returns a LHS value (really a 2-tuple).
// ']' postfix operator takes a LHS, returns value
// ']=' binary operator takes a LHS and a value, and returns same value... and SIDE-EFFECTS
c[x];
c[x]=1;

   */
  
  static private TypeEnv run( String program ) {
    TypeEnv te = Exec.go("args",program);
    if( te._errs != null ) System.err.println(te._errs.toString());
    Assert.assertNull(te._errs);
    return te;
  }
  
  static private void test( String program, Type expected ) {
    assertEquals(expected,run(program)._t);
  }
  static private void test( String program, Function<HashMap<String,Type>,Type> expected ) {
    TypeEnv te = run(program);
    Type t_expected = expected.apply(te._env._scope.types());
    assertEquals(t_expected,te._t);
  }
  static private void test_isa( String program, Type expected ) {
    TypeEnv te = run(program);
    assertTrue(te._t.isa(expected));
  }
  static private void test_isa( String program, Function<HashMap<String,Type>,Type> expected ) {
    TypeEnv te = run(program);
    Type t_expected = expected.apply(te._env._scope.types());
    assertTrue(te._t.isa(t_expected));
  }
  static private void testerr( String program, String err, String cursor ) {
    String err2 = "\nargs:0:"+err+"\n"+program+"\n"+cursor+"^\n";
    TypeEnv te = Exec.go("args",program);
    assertTrue(te._errs != null && te._errs._len>=1);
    assertEquals(err2,te._errs.at(0));
  }

}
