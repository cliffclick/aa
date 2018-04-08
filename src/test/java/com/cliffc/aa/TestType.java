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
  
    // Variable lookup
    test("pi", TypeFlt.Pi);
    // bare function lookup; returns a union of '+' functions
    testerr("+", "Syntax error; trailing junk","");
    test("{+}", Env._gvn.type(Env.top().lookup("+")));
    test("{!}", TypeFun.make(TypeTuple.INT64,TypeInt.BOOL));
    // Function application, traditional paren/comma args
    test("{+}(1,2)", TypeInt.con( 3));
    test("{-}(1,2)", TypeInt.con(-1)); // binary version
    test("{-}(1  )", TypeInt.con(-1)); // unary version
    // error; mismatch arg count
    testerr("!()"       , "Call to unary function '!', but missing the one required argument"," ");
    testerr("pi(1)"     , "A function is being called, but 3.141592653589793 is not a function type","   ");
    testerr("{+}(1,2,3)", "Argument mismatch in call to ANY(+::Flt64 +::Int64)","          ");
    // Parsed as +(1,(2*3))
    test("{+}(1, 2 * 3) ", TypeInt.con(7));
    // Parsed as +( (1+2*3) , (4*5+6) )
    test("{+}(1 + 2 * 3, 4 * 5 + 6) ", TypeInt.con(33));

    // Syntax for variable assignment
    test("x=1", TypeInt.TRUE);
    test("x=y=1", TypeInt.TRUE);
    testerr("x=y=", "Missing expr after assignment of 'y'","    ");
    testerr("x=y" , "Unknown ref 'y'","   ");
    testerr("x=1+y","Unknown ref 'y'","     ");
    test("x=2; y=x+1; x*y", TypeInt.con(6));
    // Re-use ref immediately after def; parses as: x=(2*3); 1+x+x*x
    test("1+(x=2*3)+x*x", TypeInt.con(43));
    testerr("x=(1+(x=2)+x)", "Cannot re-assign ref 'x'","             ");

    // Anonymous function definition
    test("{x y -> x+y}", TypeFun.any(2)); // actually {Flt,Int} x {FltxInt} -> {FltxInt} but currently types {SCALAR,SCALAR->SCALAR}
    test("{5}()", TypeInt.con(5)); // No args nor -> required
    test("x=3; fun={y -> x+y}; fun(2)", TypeInt.con(5)); // capture external variable
    test("x=3; fun={x -> x+2}; fun(2)", TypeInt.con(4)); // shadow  external variable
    testerr("fun={x -> x+2}; x", "Missing ref 'x'","                 "); // Scope exit ends lifetime

    // TODO: Need real TypeVars for these
    //test("id"   ,Env.top().lookup("id").types());
    //test("id(1)",TypeInt.con(1));
    //test("id((+))",Env.top().lookup("+",Type.ANY));
    //test("id(+)(id(1),id(pi))",TypeFlt.make(0,64,Math.PI+1));
  
  }

  static private void test( String program, Type expected ) {
    Assert.assertEquals(expected,Exec.go("args",program)._t);
  }
  static private void testerr( String program, String err, String cursor ) {
    String err2 = "\nargs:0:"+err+"\n"+program+"\n"+cursor+"^\n";
    try {
      TypeEnv te = Exec.go("args",program);  // Expect to throw
      Assert.assertTrue(false); // Did not throw
    } catch( IllegalArgumentException iae ) {
      Assert.assertEquals(err2,iae.getMessage());
    }
  }

  @Test public void testCommuteSymmetricAssociative() {
    // Uncomment to insert a single test to focus on
    //Assert.assertEquals(Type.SCALAR,TypePrim.ID.meet(TypeUnion.ALL_NUM));
    Assert.assertTrue(Type.check_startup());
  }  
}
