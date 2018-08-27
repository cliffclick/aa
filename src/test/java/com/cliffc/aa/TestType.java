package com.cliffc.aa;

import com.cliffc.aa.type.*;
import org.junit.Test;

import java.util.HashMap;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class TestType {
  // temp/junk holder for "instant" junits, when debugged moved into other tests
  @Test public void testType() {
    Type.init0(new HashMap<>());
    Type ignore = TypeTuple.NIL; // Break class-loader cycle; load Tuple before Fun.

  }
  
  @Test public void testNamesInts() {
    Type.init0(new HashMap<>());

    // Lattice around int8 and 0 is well formed; exactly 3 edges, 3 nodes
    // Confirm lattice: {~i16 -> ~i8 -> 0 -> i8 -> i16 }
    // Confirm lattice: {        ~i8 -> 1 -> i8        }
    Type  i16= TypeInt.INT16;
    Type  i8 = TypeInt.INT8;
    Type xi8 = i8.dual();
    Type xi16= i16.dual();
    Type z   = TypeInt.FALSE;
    Type o   = TypeInt.TRUE;
    assertEquals(xi8,xi8.meet(xi16)); // ~i16-> ~i8
    assertEquals( z ,z  .meet(xi8 )); // ~i8 ->  0
    assertEquals(i8 ,i8 .meet(z   )); //  0  -> i8
    assertEquals(i16,i16.meet(xi8 )); //  i8 -> i16
    assertEquals( o ,o  .meet(xi8 )); // ~i8 ->  1
    assertEquals(i8 ,i8 .meet(o   )); //  1  -> i8

    // Lattice around n:int8 and n:0 is well formed; exactly 2 edges, 3 nodes
    // Confirm lattice: {N:~i8 -> N:1 -> N:i8}
    // Confirm lattice: {N:~i8 ->   0 -> N:i8}
    Type ni8 = TypeName.TEST_ENUM;
    Type xni8= ni8.dual(); // dual name:int8
    Type no  = TypeName.make("__test_enum",o);
    Type nz  = TypeName.make("__test_enum",z);
    assertEquals(no ,no .meet(xni8)); // N:~i8 -> N: 1
    assertEquals(ni8,ni8.meet(no  )); // N:  1 -> N:i8
    assertEquals(ni8,ni8.meet(nz  )); //   N:0 -> N:i8
    assertEquals(nz ,nz .meet(xni8)); // N:~i8 -> N:0
    assertEquals(no ,no .meet(xni8)); // 1 & n:~i8 -> mixing 0 and 1

    // Crossing lattice between named and unnamed ints
    //      Confirm lattice: {~i8 -> N:~i8 -> 0 -> N:i8 -> i8; N:0 -> 0 }
    // NOT: Confirm lattice: {N:~i8 -> ~i8; N:i8 -> i8 }
    assertEquals(xni8,xni8.meet( xi8));//   ~i8 -> N:~i8
    assertEquals(TypeInt.BOOL, z  .meet(xni8));// N:~i8 -> {0,1}??? When falling off from a Named Int, must fall below ANY constant to keep a true lattice
    assertEquals(  i8, ni8.meet(   z));//     0 -> N:i8
    assertEquals(  i8,  i8.meet( ni8));// N: i8 ->   i8

    assertEquals(xni8,xi8.meet(xni8));
    assertEquals(TypeInt.BOOL, o .meet(xni8));
  }
  
  // oop? -> {str?,tup?} -> { null, string constants, tuple constants } -> {~str+?,~tup+?} -> ~oop+?
  // Notice multiple NILs; can be many for each type.
  @Test public void testOOPsNulls() {
    Type.init0(new HashMap<>());
    Type bot  = TypeErr  .ALL;
    Type oop0 = TypeOop  .OOP0; // OOP? (OOP and null)
    Type str0 = TypeStr  .STR0; // str? (str AND null)
    Type str  = TypeStr  .STR;  // str no null
    Type tup0 = TypeTuple.ALL0; // tup? (tup AND null); infinite repeat of ALL fields
    Type tup  = TypeTuple.ALL;  // tup       no  null ; infinite repeat of ALL fields
    Type nilo = TypeOop  .NIL;
    Type nils = TypeStr  .NIL;
    Type nilt = TypeTuple.NIL;
    Type abc  = TypeStr  .ABC;
    Type fld  = TypeTuple.INT64;  // 1 field of int64
    
    Type tupx = tup .dual();      // ~tup   (choice tup, no NULL)
    Type tup_ = tup0.dual();      // ~tup+? (choice tup  OR NULL)
    Type strx = str .dual();      // ~str   (choice str, no NULL)
    Type str_ = str0.dual();      // ~str+? (choice str  OR NULL)
    Type oop_ = oop0.dual();      // ~OOP+? (choice OOP  OR null)
    Type top  = Type.ANY;

    assertTrue(top .isa(oop_));

    assertTrue(oop_.isa(str_));
    assertTrue(oop_.isa(tup_));

    assertTrue(str_.isa(strx));
    assertTrue(tup_.isa(tupx));
    assertTrue(str_.isa(nilo));
    assertTrue(str_.isa(nils));
    assertTrue(tup_.isa(nilo));
    assertTrue(tup_.isa(nilt));

    assertTrue(strx.isa(abc ));
    assertTrue(tupx.isa(fld ));
    
    assertTrue(abc .isa(str ));
    assertTrue(fld .isa(tup ));
    assertTrue(nils.isa(str0));
    assertTrue(nilt.isa(tup0));

    assertTrue(str .isa(str0));
    assertTrue(tup .isa(tup0));

    assertTrue(str0.isa(oop0));
    assertTrue(tup0.isa(oop0));
    
    assertTrue(oop0.isa(bot ));
    
    // Crossing named:ints or named:null and OOP
    Type  i8 = TypeInt.INT8;
    Type xi8 = i8.dual();
    assertEquals( Type.SCALAR, xi8.meet(oop_)); // ~OOP+0 &   ~i8 -> 0
  }
  
  @Test public void testStructTuple() {
    Type.init0(new HashMap<>());
    Type nil  = TypeOop.NIL;
    // Tuple is more general that Struct
    Type tf = TypeTuple.FLT64; //  [  flt64,~Scalar...]; choice leading field name
    Type tsx= TypeStruct.X;    // @{x:flt64,~Scalar...}; fixed  leading field name
    Type tff = tsx.meet(tf);   //
    assertEquals(tf,tff);      // tsx.isa(tf)
    TypeTuple t0 = TypeTuple.make_args(nil); //  [  0,~Scalar...]
    Type      ts0= TypeStruct.makeX(new String[]{"x"},nil);  // @{x:0,~Scalar...}
    Type tss = ts0.meet(t0);
    assertEquals(t0,tss);      // t0.isa(ts0)

    // Union meets & joins same-class types
    Type uany = TypeUnion.make(true ,TypeInt.con(2),TypeInt.INT8);
    Type uall = TypeUnion.make(false,TypeInt.con(2),TypeInt.INT8);
    assertEquals(uany,TypeInt.con(2));
    assertEquals(uall,TypeInt.INT8  );
    
    // meet @{c:0}? and @{c:@{x:1}?,}
    TypeNullable nc0 = TypeStruct.make(TypeStruct.AND_NIL,new Type[]{nil},Type.ALL,new String[]{"c"}); // @{c:0}?
    TypeNullable nx1 = TypeStruct.make(TypeStruct.AND_NIL,new Type[]{TypeInt.TRUE},Type.ALL,new String[]{"x"}); // @{x:1}?
    TypeNullable cx  = TypeStruct.makeA(new String[]{"c"},nx1); // @{c:@{x:1}?}
    // JOIN tosses the top-level null choice, and the inside struct choice
    Type cj  = nc0.join(cx);
    Type c0  = TypeStruct.makeA(new String[]{"c"},nx1.make_nil((byte)0)); // @{c:0}
    assertEquals(c0,cj);

    TypeFun gf = TypeFun.make_generic();
    TypeFun f2 = TypeFun.any(2,23); // Some generic function (happens to be #23, '&')
    assertTrue(f2.isa(gf));
  }

  @Test public void testUnion() {
    Type.init0(new HashMap<>());

    Type a = TypeUnion.make(false,TypeInt.FALSE,TypeFlt.FLT32);
    assertEquals(TypeFlt.FLT32,a); // 0 isa FLT32, so collapses
    Type b = TypeUnion.make(false,TypeInt.con(123456789),TypeFlt.FLT32);
    assertEquals(Type.REAL,b); // Does not collapse
    Type c = TypeUnion.make(false,TypeInt.FALSE,TypeInt.TRUE);
    assertEquals(TypeInt.BOOL,c); // {0*1} combines to bool
    Type d = TypeUnion.make(false,TypeInt.FALSE,TypeOop.NIL);
    assertTrue(d instanceof TypeUnion); // Does not collapse

    Type nil = TypeUnion.NIL;
    Type e = TypeOop.NIL.meet(TypeUnion.NIL);
    assertEquals(TypeOop.NIL,e);
  }

  // TODO: Observation: value() calls need to be monotonic, can test this.
  @Test public void testCommuteSymmetricAssociative() {
    Type.init0(new HashMap<>());

    Type  n  = Type.NUM;
    Type xn  = Type.NUM.dual();
    Type onil= TypeOop.NIL;
    Type oop_= TypeOop.OOP_;
    Type  nil= TypeUnion.NIL;
    Type dnil= nil.dual();

    Type hi0 = xn.meet(dnil);
    assertEquals(dnil,hi0);
    Type mt2 = oop_.meet(n);
    assertEquals(Type.SCALAR,mt2);
    Type mt0 = xn.meet(onil);
    //assertEquals(nil,mt0);
    Type mt1 = onil.meet(nil);
    assertEquals(onil,mt1);
    
    assertTrue(Type.check_startup());
  }  
}
