package com.cliffc.aa;

import org.junit.Assert;
import org.junit.Test;

public class TestType {
  @Test public void testType0() {
    // Simple int
    test("1",   TypeInt.TRUE);
    // Unary operator
    test("-1",  TypeInt.con( -1));
    test("!1",  TypeInt.con(  0));
    // Binary operators
    test("1+2", TypeInt.con(  3));
    test("1-2", TypeInt.con( -1));
    test("1+2*3", TypeInt.con(  7));
    // Binary with precedence check
    test(" 1+2 * 3+4 *5", TypeInt.con( 27));
    test("(1+2)*(3+4)*5", TypeInt.con(105));

    // Float
    test("1.2+3.4", TypeFlt.make(0,64,4.6));
    // Mixed int/float with conversion
    test("1+2.3",   TypeFlt.make(0,64,3.3));
  
    // Simple strings
    test("\"Hello, world\"", TypeStr.make(0,"Hello, world"));
    test("str(3.14)", TypeStr.make(0,"3.14"));
    test("str(3)", TypeStr.make(0,"3"));
    test("str(\"abc\")", TypeStr.make(0,"abc"));
      
    // Variable lookup
    test("math_pi", TypeFlt.PI);
    // bare function lookup; returns a union of '+' functions
    testerr("+", "Syntax error; trailing junk","");
    test("{+}", Env.lookup_valtype("+"));
    test("{!}", Env.lookup_valtype("!"));
    // Function application, traditional paren/comma args
    test("{+}(1,2)", TypeInt.con( 3));
    test("{-}(1,2)", TypeInt.con(-1)); // binary version
    test("{-}(1  )", TypeInt.con(-1)); // unary version
    // error; mismatch arg count
    testerr("!()"       , "Call to unary function '!', but missing the one required argument"," ");
    testerr("math_pi(1)", "A function is being called, but 3.141592653589793 is not a function type","          ");
    testerr("{+}(1,2,3)", "Argument mismatch in call to +:[{flt64 flt64 -> flt64},{int64 int64 -> int64},]","          ");

    // Parsed as +(1,(2*3))
    test("{+}(1, 2 * 3) ", TypeInt.con(7));
    // Parsed as +( (1+2*3) , (4*5+6) )
    test("{+}(1 + 2 * 3, 4 * 5 + 6) ", TypeInt.con(33));

    // Syntax for variable assignment
    test("x=1", TypeInt.TRUE);
    test("x=y=1", TypeInt.TRUE);
    testerr("x=y=", "Missing ifex after assignment of 'y'","    ");
    testerr("x=y" , "Unknown ref 'y'","   ");
    testerr("x=1+y","Unknown ref 'y'","     ");
    test("x=2; y=x+1; x*y", TypeInt.con(6));
    // Re-use ref immediately after def; parses as: x=(2*3); 1+x+x*x
    test("1+(x=2*3)+x*x", TypeInt.con(1+6+6*6));
    testerr("x=(1+(x=2)+x)", "Cannot re-assign ref 'x'","             ");

    // Conditional:
    test   ("0 ?    2  : 3", TypeInt.con(3)); // false
    test   ("2 ?    2  : 3", TypeInt.con(2)); // true
    test   ("math_rand(1)?(x=4):(x=3);x", TypeInt.INT8); // x defined on both arms, so available after
    test   ("math_rand(1)?(x=2):   3 ;4", TypeInt.con(4)); // x-defined on 1 side only, but not used thereafter
    test   ("math_rand(1)?(y=2;x=y*y):(x=3);x", TypeInt.INT8); // x defined on both arms, so available after, while y is not
    testerr("math_rand(1)?(x=2):   3 ;x", "'x' not defined on false arm of trinary","                        ");
    testerr("math_rand(1)?(x=2):   3 ;y=x+2;y", "'x' not defined on false arm of trinary","                        ");
    testerr("0 ? (x=2) : 3;x", "'x' not defined on false arm of trinary","             ");
    test   ("2 ? (x=2) : 3;x", TypeInt.con(2)); // off-side is constant-dead, so missing x-assign is ignored
    test   ("2 ? (x=2) : y  ", TypeInt.con(2)); // off-side is constant-dead, so missing 'y'      is ignored
    testerr("x=1;2?(x=2):(x=3);x", "Cannot re-assign ref 'x'","          ");
    test   ("x=1;2?   2 :(x=3);x",TypeInt.con(1)); // Re-assigned allowed & ignored in dead branch
    
    // Anonymous function definition
    test_isa("{x y -> x+y}", TypeFun.any(2,-1)); // actually {Flt,Int} x {FltxInt} -> {FltxInt} but currently types {SCALAR,SCALAR->SCALAR}
    test("{5}()", TypeInt.con(5)); // No args nor -> required; this is simply a function returning 5, being executed

    // ID in different contexts; in general requires a new TypeVar per use; for
    // such a small function it is always inlined completely, has the same effect.
    test("id", Env.lookup_valtype("id"));
    test("id(1)",TypeInt.con(1));
    test("id(3.14)",TypeFlt.con(3.14));
    test("id({+})",Env.lookup_valtype("+")); // 
    test("id({+})(id(1),id(math_pi))",TypeFlt.make(0,64,Math.PI+1));

    // Function execution and result typing
    test("x=3; fun={y -> x & y}; fun(2)", TypeInt.con(2)); // trivially inlined; capture external variable
    test("x=3; fun={x -> x & 2}; fun(2)", TypeInt.con(2)); // trivially inlined; shadow  external variable
    testerr("fun={x -> x+2}; x", "Unknown ref 'x'","                 "); // Scope exit ends lifetime
    // Needs overload cloning/inlining to resolve {+}
    test("x=3; fun={y -> x+y}; fun(2)", TypeInt.con(5)); // must inline to resolve overload {+}:Int
    test("x=3; fun={x -> x*2}; fun(2.1)", TypeFlt.con(2.1*2.0)); // must inline to resolve overload {+}:Flt with I->F conversion
    test("x=3; fun={y -> x*x+y*y}; fun(2)", TypeInt.con(13)); // 
    test("x=3; fun={x -> x*2}; fun(2.1)+fun(x)", TypeFlt.con(2.1*2.0+3*2)); // Mix of types to fun()

    // Type annotations
    test("-1@int", TypeInt.con( -1));
    test("(1+2.3)@flt", TypeFlt.make(0,64,3.3));
    test("x@int = 1", TypeInt.TRUE);
    test("x@flt = 1", TypeInt.TRUE); // casts for free to a float
    testerr("x@flt32 = 123456789", "123456789 is not a flt32","                   ");
    
    testerr("-1@int1", "-1 is not a int1","       ");
    testerr("\"abc\"@int", "\"abc\" is not a int64","         ");
    testerr("1@str", "1 is not a str","     ");
    
    testerr("x=3; fun@{int->int}={x -> x*2}; fun(2.1)+fun(x)", "2.1 is not a int64","                              ");
    test("x=3; fun@{real->real}={x -> x*2}; fun(2.1)+fun(x)", TypeFlt.con(2.1*2.0+3*2)); // Mix of types to fun()
    test("fun@{real->flt32}={x -> x}; fun(123 )", TypeInt.con(123 ));
    test("fun@{real->flt32}={x -> x}; fun(0.125)", TypeFlt.con(0.125));
    testerr("fun@{real->flt32}={x -> x}; fun(123456789)", "123456789 is not a flt32","                          ");
    
    // TODO: Need real TypeVars for these
    //test("id@{A->A}"    , Env.lookup_valtype("id"));
    //test("id@{A@int->A}", Env.lookup_valtype("id"));
    //test("id@{int->int}", Env.lookup_valtype("id"));

    // Recursive:
    //test("fib = { x -> x <= 1 ? 1 : fib(x-1)+fib(x-2) }; fib(4)",TypeInt.con(5));

    // Co-recursion will require parallel assignment & type inference across a lexical scope
    //test("is_even = { n -> n ? is_odd(n-1) : true}; is_odd = {n -> n ? is_even(n-1) : false}; is_even(4)", TypeInt.TRUE );
    //test("is_even = { n -> n ? is_odd(n-1) : true}; is_odd = {n -> n ? is_even(n-1) : false}; is_even(5)", TypeInt.FALSE);
  }

  static private void test( String program, Type expected ) {
    TypeEnv te = Exec.go("args",program);
    if( te._errs != null ) System.err.println(te._errs.toString());
    Assert.assertNull(te._errs);
    Assert.assertEquals(expected,te._t);
  }
  static private void test_isa( String program, Type expected ) {
    TypeEnv te = Exec.go("args",program);
    if( te._errs != null ) System.err.println(te._errs.toString());
    Assert.assertNull(te._errs);
    Assert.assertTrue(te._t.isa(expected));
  }
  static private void testerr( String program, String err, String cursor ) {
    String err2 = "\nargs:0:"+err+"\n"+program+"\n"+cursor+"^\n";
    TypeEnv te = Exec.go("args",program);
    Assert.assertTrue(te._errs != null && te._errs._len>=1);
    Assert.assertEquals(err2,te._errs.at(0));
  }

  // TODO: Observation: value() calls need to be monotonic, can test this.
  @Test public void testCommuteSymmetricAssociative() {
    // Uncomment to insert a single test to focus on
    Type t0 = TypeFun.any(0,-1);
    Type t1 = TypeFun.any(1,-1);
    Type t2 = t0.meet(t1);
    Type t3 = Type.NUM.meet(t2);
    Assert.assertEquals(Type.SCALAR,t3);
    Assert.assertTrue(Type.check_startup());
  }  
}
