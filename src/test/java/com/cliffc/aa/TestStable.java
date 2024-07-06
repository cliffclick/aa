package com.cliffc.aa;

import org.junit.Test;

import static com.cliffc.aa.TestParse.test;

public class TestStable {

  // Basic tests not requiring overloads - which avoids all operators.
  @Test public void testBasic() {
    // Simple number parsing
    test("1", "1", "int:1");
    // Simple field create
    test("x=1;x","1","int:1");
    test("x=1;y=2; x","1","int:1");
    // Struct define and field lookup
    test("a=@{x=1.2;y;}; a.x", "1.2", "flt:1.2"); // standard "." field naming; trailing semicolon optional
    // Function call without parens
    test("math.rand 2","int64","int:int64");
    // Function call with parens
    test("math.rand(2)","int64","int:int64");
  }

  @Test public void testNil() {
    test("0", "nil", "nil:nil");
    test("!0", "1", "int:1");
    test("0+3.3","3.3f","flt:3.3");
    // Mixing nil and float
    test("{ x y -> x.sin() * !y }(3.3,0)","-0.1577456941432482","flt:-0.1577456941432482");
  }

  @Test public void testStatements() {
    // Statements
    test("(1;2 )", "2", "int:2");
    test("(1;2;)", "2", "int:2"); // final semicolon is optional
    test("1._+_._(2;3)", "4", "int:4"); // statements in arguments
  }

  // Test primitive math, and loading overloads from primitives.
  @Test public void testOverPrim() {
    // Unary operator
    test("!1", "nil", "nil:nil");

    // Binary with precedence check
    test(" 1+2 * 3+4 *5", "27", "int:27");

    // Mixed int/float with conversion
    test("1+2.3", "3.3", "flt:3.3");

    // Function application, traditional paren/comma args
    test("1._+_._(2)", "3", "int:3" );

    // Parsed as +(1,(2*3))
    test("1._+_._(2 * 3) ", "7", "int:7");

    // Simpler overload tests
    test("!(2,3.14)._","nil","nil:nil", null, null, null, null);
    test("(2,3.14)._.sin()","0.0015926529164868282","flt:0.0015926529164868282", null, null, null, null);
    // Two DynLoads, no Fresh
    test("q=(2,3.14); (!q._,q._.sin())","*[21](_, int1, flt64)","*[21](_,int:int64,flt:flt64)", null, null, "[4,21]", null);
  }

  // More complex overload tests
  @Test public void testOver() {
    // testOver5.aa, One DynLoad, fcn needs DynTable
    // Returning choice of structs and field selecting from it.
    test("fcn = {(@{a=1;},@{b=2;})._}; (fcn().a, fcn().b)", "*[24]( _, %[2,24][2]?, %[2,24][2]?)", "*[24](_, int:1,int:2)", null, null, "[2,24]", null);

    // testOver6.aa, One DynLoad, fcn needs DynTable
    // Passing choice of structs and field selecting from it.
    test(
"""
fcn = { x ->
  @{ qi = { x -> x.a };
     qf = { x -> x.b };
  }._ x
};
(fcn @{a=2;}, fcn @{b=3.3;})
""",
         "*[26]( _, %[2,26][2]?, %[2,26][2]?)", "*[26](_,int:2,flt:3.3)",null,null,"[4,26]",null);

    // Same using primitive math
    test(
"""
( { x y -> !x      * !y },
  { x y -> x.sin() * !y }
)._(3.3,0)
""",
         "-0.1577456941432482","flt:-0.1577456941432482");

    // Multi-arg function selection from a set.  Note the really weak GCP
    // result: argument "x" is passed as both an int and a flt, and HMT makes
    // sure the correct arg is passed to the correct function.
    test(
"""
noinline_foo = { x y ->
        ( { x y -> !x      * !y },
          { x y -> x.sin() * !y }
          )._(x,y)  // The single call site; "x" is either int or flt
};
(noinline_foo(3,5), noinline_foo(3.3,5))
""",
         "*[24]( _, %[2,24][2]?, %[2,24][2]?)","*[24]( _, int:int64, flt:flt64)", null, null, "[4,24]", null);
  }


  @Test public void testMutLetRec() {
    // A,B,C are mutually recursive identity functions.
    // D calls B or C with ints.
    // final struct calls C with floats.
    test(
"""
A = { x -> math.rand(2) ? B(x) : x };
D = {   -> math.rand(2) ? B(1) : C(2) };
C = { x -> A(x) };
B = { x -> C(x) };
( D(), C(3.14) )

""",
         "*[24]( _, %[6,7][], %[6,7][])","*[24]( _, int:nint8, flt:3.14)",null,null,"[4,24]",null);
  }
}
