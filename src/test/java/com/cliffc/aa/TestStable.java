package com.cliffc.aa;

import org.junit.Test;

import static com.cliffc.aa.TestParse.test;

public class TestStable {

  // Basic tests not requiring overloads - which avoids all operators.
  @Test public void testBasic() {
    // Simple number parsing
    test("1", "int:1", "int:1");
    // Struct define and field lookup
    test("a=@{x=1.2;y;}; a.x", "flt:1.2", "flt:1.2"); // standard "." field naming; trailing semicolon optional
    // Function call without parens
    test("math.rand 2","int:int64","int:int64");
    // Function call with parens
    test("math.rand(2)","int:int64","int:int64");
  }

  /*@Test*/ public void testStatements() {
    // Statements
    test("(1;2 )", "2", "2");
    test("(1;2;)", "2", "2"); // final semicolon is optional
    test("1._+_._(2;3)", "4", "4"); // statements in arguments
  }

  // Test primitive math, and loading overloads from primitives.
  @Test public void testOverPrim() {
    // Unary operator
    test("!1", "nil", "nil");

    // Binary with precedence check
    test(" 1+2 * 3+4 *5", "int:27", "int:27");

    // Mixed int/float with conversion
    test("1+2.3", "flt:3.3", "flt:3.3");

    // Function application, traditional paren/comma args
    test("1._+_._(2)", "int:3", "int:3" );

    // Parsed as +(1,(2*3))
    test("1._+_._(2 * 3) ", "int:7", "int:7");
  }

  // More complex overload tests
  @Test public void testOver() {
    // testOver5.aa, One DynLoad, fcn needs DynTable
    // Returning choice of structs and field selecting from it.
    test("fcn = {(@{a=1;},@{b=2;})._}; (fcn().a, fcn().b)", "*[21]( _, %[2,4,21][2]?, %[2,4,21][2]?, ...)", "*[21](_, int:1,int:2)", null, null, "[4,21]", null);

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
         "*[23]( _, %[2,4,23][2]?, %[2,4,23][2]?, ...)", "*[23](_,int:2,flt:3.3)",null,null,"[4,23]",null);
  }

}
