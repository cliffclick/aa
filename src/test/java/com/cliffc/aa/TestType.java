package com.cliffc.aa;

import com.cliffc.aa.type.*;
import org.junit.Assert;
import org.junit.Test;

public class TestType {
  @Test public void testType0() {
    // simple anon struct tests
    //test   ("  .{x,y}", TypeTuple.make(TypeInt.FALSE,TypeInt.FALSE)); // simple anon struct decl
    //test   ("a=.{x=1.2,y}; a.x", TypeFlt.con(1.2)); // standard "." field naming
    //testerr("a=.{x,y}; a.x=1","Cannot re-assign _.x","");
    //test   ("a=.{x=0,y=1}; b=.{x=2}; c=math_rand(1)?a:b; c.x", TypeInt.INT8); // either 0 or 2
    //testerr("a=.{x=0,y=1}; b=.{x=2}; c=math_rand(1)?a:b; c.y",  "Unknown ref _.y","");
    //testerr("dist={p->p.x*p.x+p.y+p.y}; dist(.{x=1})", "Unknown ref _.y","");   // missing field
    //test   ("dist={p->p.x*p.x+p.y+p.y}; dist(.{x=1,y=2})", TypeInt.con(5));     // passed in to func
    //test   ("dist={p->p.x*p.x+p.y+p.y}; dist(.{x=1,y=2,z=3})", TypeInt.con(5)); // extra fields OK

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
    testerr("{+}(1,2,3)", "Passing 3 arguments to +{flt64 flt64 -> flt64} which takes 2 arguments","   ");

    // Parsed as +(1,(2*3))
    test("{+}(1, 2 * 3) ", TypeInt.con(7));
    // Parsed as +( (1+2*3) , (4*5+6) )
    test("{+}(1 + 2 * 3, 4 * 5 + 6) ", TypeInt.con(33));
    // Statements
    test("(1;2 )", TypeInt.con(2));
    test("(1;2;)", TypeInt.con(2)); // final semicolon is optional
    test("{+}(1;2 ,3)", TypeInt.con(5)); // statements in arguments
    test("{+}(1;2;,3)", TypeInt.con(5)); // statements in arguments

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
    testerr("1:","Syntax error; trailing junk"," "); // missing type
    test   ("math_rand(1)?1:int:2:int",TypeInt.INT8); // no ambiguity between conditionals and type annotations
    testerr("math_rand(1)?1: :2:int","missing expr after ':'","                "); // missing type
    testerr("math_rand(1)?1::2:int","missing expr after ':'","               "); // missing type

    test   ("1  < 2", TypeInt.TRUE );
    test   ("1  <=2", TypeInt.TRUE );
    test   ("1  > 2", TypeInt.FALSE);
    test   ("1  >=2", TypeInt.FALSE);
    test   ("1  ==2", TypeInt.FALSE);
    test   ("1  !=2", TypeInt.TRUE );
    test   ("1.2< 2", TypeInt.TRUE );
    test   ("1.2<=2", TypeInt.TRUE );
    test   ("1.2> 2", TypeInt.FALSE);
    test   ("1.2>=2", TypeInt.FALSE);
    test   ("1.2==2", TypeInt.FALSE);
    test   ("1.2!=2", TypeInt.TRUE );

    // Anonymous function definition
    test_isa("{x y -> x+y}", TypeTuple.FUNPTR2); // actually {Flt,Int} x {FltxInt} -> {FltxInt} but currently types {SCALAR,SCALAR->SCALAR}
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
    test("fun={x -> y=3; x*y}; fun(2)", TypeInt.con(6)); // multi statements in func body
    // Needs overload cloning/inlining to resolve {+}
    test("x=3; fun={y -> x+y}; fun(2)", TypeInt.con(5)); // must inline to resolve overload {+}:Int
    test("x=3; fun={x -> x*2}; fun(2.1)", TypeFlt.con(2.1*2.0)); // must inline to resolve overload {+}:Flt with I->F conversion
    test("x=3; fun={x -> x*2}; fun(2.1)+fun(x)", TypeFlt.con(2.1*2.0+3*2)); // Mix of types to fun()

    // Type annotations
    test("-1:int", TypeInt.con( -1));
    test("(1+2.3):flt", TypeFlt.make(0,64,3.3));
    test("x:int = 1", TypeInt.TRUE);
    test("x:flt = 1", TypeInt.TRUE); // casts for free to a float
    testerr("x:flt32 = 123456789", "123456789 is not a flt32","                   ");

    testerr("-1:int1", "-1 is not a int1","       ");
    testerr("\"abc\":int", "\"abc\" is not a int64","         ");
    testerr("1:str", "1 is not a str","     ");

    testerr("x=3; fun:{int->int}={x -> x*2}; fun(2.1)+fun(x)", "2.1 is not a int64","                              ");
    test("x=3; fun:{real->real}={x -> x*2}; fun(2.1)+fun(x)", TypeFlt.con(2.1*2+3*2)); // Mix of types to fun()
    test("fun:{real->flt32}={x -> x}; fun(123 )", TypeInt.con(123 ));
    test("fun:{real->flt32}={x -> x}; fun(0.125)", TypeFlt.con(0.125));
    testerr("fun:{real->flt32}={x -> x}; fun(123456789)", "123456789 is not a flt32","                          ");

    // Recursive:
    test("fact = { x -> x <= 1 ? x : x*fact(x-1) }; fact(3)",TypeInt.con(6));
    test("fib = { x -> x <= 1 ? 1 : fib(x-1)+fib(x-2) }; fib(4)",TypeInt.INT64);

    // Co-recursion requires parallel assignment & type inference across a lexical scope
    test("is_even = { n -> n ? is_odd(n-1) : 1}; is_odd = {n -> n ? is_even(n-1) : 0}; is_even(4)", TypeInt.TRUE );
    test("is_even = { n -> n ? is_odd(n-1) : 1}; is_odd = {n -> n ? is_even(n-1) : 0}; is_even(5)", TypeInt.FALSE );

    // TODO: Need real TypeVars for these
    //test("id:{A->A}"    , Env.lookup_valtype("id"));
    //test("id:{A:int->A}", Env.lookup_valtype("id"));
    //test("id:{int->int}", Env.lookup_valtype("id"));
  }

  /*

// 0:int is the uniform initial value, counts as null; free cast to null

// anon struct decls
// no un-init values; always take a default init
// no re-assignment YET, so default is also final
.{ x, y } // no initial value and no reassignment semantics yet; "feels like" C
.{ x=1.1, y=2.2, } // with initial values
a = {x,y}; a.x=1; // Cannot re-assign, so x,y are stuck at zero
// a.x is a LHS value; makes it a parser-aware thing
a=.{x=0  ,y=2.2}
b=.{x=1.2,y=2.3}
c=rand?a:b; 
c.x=1; // cannot re-assign
c.x;   // return either 0 or 1.2 or flt
dist={p->p.x*p.x+p.y*p.y}; dist(a); // valid

b={x="hello", y=2.2}
c=rand?a:b; 
c.x; // either 0/null or "hello"

x=0; y=1.2; z="abc"; c=rand?x:y; d=rand?x:z; str(c)+d; // "0 or 1.2"+"null or hello"



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



// Adding named types to primitives, because its the natural extension 
// when adding them to tuples.

// 'gal' is a type name for a flt.  'gal' is a type, never a concrete value.
gal = :flt

// tank is being assigned a concrete value, not a type, so tank is not a type.
tank:gal = 5:gal // tank has 5 gallons

tank:gal = 10 // free cast for bare constants

x = 1.23          // x has type flt 1.23
tank:gal =     x  // ERR: x is not gallons; no free cast
tank:gal = gal(x) // OK : called 'gal' constructor

// Since comma, its a struct not a function type.
// Trailing comma is optional.
// A tuple of null and a string
list_of_hello = { 0, "hello", }

// No ambiguity:
 { x  } // no-arg-function returning external variable x; same as { -> x }
 { x, } // 1-elem struct   returning external variable x
:{ x  } // 1-elem struct type with field named x

// Adding named types to structs

// Point is a struct with 2 untyped named variables
Point = :{ x,     y, }
Point = :{ x:flt, y:flt, } // Same Point, vars forced to flt

here = Point(1,2) // Point constructor
// "." field name lookup
print(here.x)

// Null
x:str   = "hello" // x takes a not-null str
x:0|str = 0       // x takes a null or str

x := 0       // x is untyped; assigned null right now
x := "hello" // x is re-assigned and has type 0|str

// Unnamed types use Duck typing; Named types are restricted (nomative)
// 'dist2' takes any record with fields x,y
dist2 = { p -> p.x*p.x+p.y*p.y }
// Restrict argument to just Points
dist2 = { p:Point -> p.x*p.x+p.y*p.y }





// type variables are free in : type expressions

// Define a pair as 2 fields "a" and "b" both with the same type T.
// Note that 'a' and 'b' and 'T' are all free, but the comma parses this as a
// collection, so 'a' and 'b' become field names and 'T' becomes a type-var.
Pair = :{ a:T, b:T }

// Since no comma, its a function type not a struct type.
// Since 'A' and 'B' are free and not field names, they become type-vars.
MapType = :{ {A->B} List(A) -> List(B) }

// map: no leading ':' so a function definition, not a type def
map:{ {A->B} List(A) -> List(B) }  = { f list -> ... }

// A List type.  Named types are not 'null', so not valid to use "List = :0|...".
// Type List takes a type-variable 'A' (which is free in the type expr).
// List is a self-recursive type.
// Field 'next' can be null or List(A).
// Field 'val' is type A.
List = :{ next:0|List(A) val:A }

// Type A can allow nulls, or not
strs:List(0)     = ... // List of nulls
strs:List(str)   = ... // List of not-null strings
strs:List(0|str) = ... // List of null-or-strings

// TODO: Re-assignment; ':=' allows more ':=' or exactly 1 final assignment '='
x := 1; x:= 2; x = 3; x // 3
x  = 1; x = 2; // cannot reassign
x  = 1; x:= 2; // cannot reassign
x := 1; rand ? x =2 :  3; x; // cannot partially final-assign
x := 1; rand ? x:=2 :  3; x; // 2; x is still assignable
x := 1; rand ? x =2 :x=3; x; // 2or3; x is final
x := 1; x = x; // 1; make x final
   */
  
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
    Type prim = TypeFun.make(TypeTuple.INT64_INT64,TypeInt.INT64,17);
    Type gen = TypeFun.make_generic();
    Type mt = gen.meet(prim);
    Assert.assertSame(mt, gen);
    Assert.assertTrue(prim.isa(gen));
    Assert.assertTrue(Type.check_startup());
  }  
}
