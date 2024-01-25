package com.cliffc.aa;

import org.junit.BeforeClass;
import org.junit.Test;

import static com.cliffc.aa.TestParse.test;

public class TestStable {

  // Basic tests not requiring overloads - which avoids all operators.
  @Test public void testBasic() {
    test("1", "int:1", "int:1");
    test("a=@{x=1.2;y;}; a.x", "flt:1.2", "flt:1.2"); // standard "." field naming; trailing semicolon optional
  }

  // Test primitive math, and loading overloads from primitives.
  @Test public void testOverPrim() {
    // Unary operator
    test("!1", "nil", "nil");
    
    // Binary with precedence check
    test(" 1+2 * 3+4 *5", "int:27", "int:27");

    // Float
    test("1.2+3.4", "flt:4.6", "flt:4.6");
    // Mixed int/float with conversion
    test("1+2.3", "flt:3.3", "flt:3.3");

    // Function application, traditional paren/comma args
    test("1._+_._(2)", "int:3", "int:3" );

  }

  // More complex overload tests
  @Test public void testOver() {
    
    // testOver5.aa, One DynLoad, fcn needs DynTable
    test("fcn = {(@{a=1},@{b=2})._}; (fcn().a, fcn().b)", "*[37](_, int:1,int:2)", "*[37](_, int:1,int:2)", null, null, "[37]", null);
  }

}
