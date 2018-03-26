package com.cliffc.aa;

import org.junit.Assert;
import org.junit.Test;

public class TestType {
  @Test public void testType0() {
    test("id(1)",Env.top().lookup("+",Type.ANY));

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
  
    // Variable lookup
    test("pi", TypeFlt.Pi);
    // bare function lookup; returns a union of '+' functions
    test("+",  Env.top().lookup("+",Type.ANY));
    test("!",  Env.top().lookup("!",Type.ANY));
    // Function application, lispy-style WS-delimited args
    test   ("+ 1 2", TypeInt.con( 3));
    testerr("- 1 2", "\nargs:0:A function is being called, but -1 is not a function\n- 1 2\n     ^\n");
    // Function application, traditional paren/comma args
    test   ("+(1,2)", TypeInt.con( 3));
    testerr("-(1,2)", "\nargs:0:Expected ')' but found ',' instead\n-(1,2)\n   ^\n"); // binary version
    test   ("-(1  )", TypeInt.con(-1)); // unary version
    // error; mismatch arg count
    testerr("!()"     , "\nargs:0:!::Int1 expects 1 arguments but called with 0\n!()\n   ^\n");
    testerr("pi(1)"   , "\nargs:0:A function is being called, but 3.141592653589793 is not a function\npi(1)\n     ^\n");
    testerr("+(1,2,3)", "\nargs:0:+::Int64 expects 2 arguments but called with 3\n+(1,2,3)\n        ^\n");
    // Parsed as +(1,(2*3))
    test("+ 1 2 * 3 ", TypeInt.con(7));
    // Parsed as +( (1+2*3) , (4*5+6) )
    test("+ 1 + 2 * 3 4 * 5 + 6 ", TypeInt.con(33));

    // Ok, need serious type-prop for these
    test("id"   ,Env.top().lookup("id",Type.ANY));
    test("id(1)",TypeInt.con(1));
    test("id(+)",Env.top().lookup("+",Type.ANY));
    test("id(+)(id(1),id(pi))",TypeFlt.make(0,64,Math.PI+1));
  
  }

  static private void test( String program, Type expected ) {
    Assert.assertEquals(expected,Exec.go("args",program)._t);
  }
  static private void testerr( String program, String err ) {
    try {
      Exec.go("args",program);  // Expect to throw
      Assert.assertTrue(false); // Did not throw
    } catch( IllegalArgumentException iae ) {
      Assert.assertEquals(err,iae.getMessage());
    }
  }

  @Test public void testCommuteSymmetricAssociative() {
    // Uncomment to insert a single test to focus on
    //Assert.assertEquals(Type.SCALAR,TypePrim.ID.meet(TypeUnion.ALL_NUM));
    Assert.assertTrue(Type.check_startup());
  }  
}
