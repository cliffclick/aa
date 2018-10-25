package com.cliffc.aa;

import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.Bits;
import org.junit.Ignore;
import org.junit.Test;

import java.util.HashMap;
import java.util.function.Consumer;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class TestType {
  // temp/junk holder for "instant" junits, when debugged moved into other tests
  @Test public void testType() {
    Type.init0(new HashMap<>());
    Type ignore = TypeTuple.ALL; // Break class-loader cycle; load Tuple before Fun.

    Type foo = TypeStruct.POINT.meet(TypeStruct.C0);
    assertTrue(foo!=foo.dual());

    
    Type def = TypeStr.con("def");
    Type mto5 = def.meet(TypeStr.ABC);
    assertEquals(TypeStr.STR,mto5);
    Type mto4 = TypeOop.XOOP.meet(TypeNil.ABC);
    assertEquals(TypeNil.ABC,mto4);
    Type mto3 = TypeOop.XOOP.meet(TypeNil.STR);
    assertEquals(TypeNil.STR,mto3);
    Type mto2 = TypeNil.XOOP.meet(TypeNil.make(TypeStr.XSTR));
    assertEquals(TypeNil.make(TypeStr.XSTR),mto2);
    Type mto1 = TypeOop.XOOP.meet(TypeStr.XSTR);
    assertEquals(TypeStr.XSTR,mto1);
    
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
    // Confirm lattice: {N:~i8 -> N:0 -> N:i8}
    Type ni8 = TypeName.TEST_ENUM;
    Type xni8= ni8.dual(); // dual name:int8
    Type no  = TypeName.make("__test_enum",TypeName.TEST_SCOPE,o);
    Type nz  = TypeName.make("__test_enum",TypeName.TEST_SCOPE,z);
    assertEquals(no ,no .meet(xni8)); // N:~i8 -> N: 1
    assertEquals(ni8,ni8.meet(no  )); // N:  1 -> N:i8
    assertEquals(nz ,nz .meet(xni8)); // N:~i8 -> N:0
    assertEquals(ni8,ni8.meet(nz  )); //   N:0 -> N:i8
    assertEquals(no ,no .meet(xni8)); // n:1 & n:~i8 -> mixing 0 and 1

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
    Type bot  = Type     .ALL;
    Type oop0 = TypeNil  .OOP;  // OOP? (OOP and null)
    Type str0 = TypeNil  .STR;  // str? (str AND null)
    Type str  = TypeStr  .STR;  // str no null
    Type tup0 = TypeNil.make(TypeTuple.SCALAR0); // tup? (tup AND null); infinite repeat of SCALAR fields
    Type tup  = TypeTuple.SCALAR0; // tup no null ; infinite repeat of SCALAR fields
    Type i0   = TypeInt.FALSE;
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
    assertTrue(!str_.isa(i0 ));
    assertTrue(!tup_.isa(i0 ));
    assertTrue(str_.isa(TypeNil.ABC));

    assertTrue(strx.isa(abc ));
    assertTrue(tupx.isa(fld ));
    
    assertTrue(abc .isa(str ));
    assertTrue(fld .isa(tup ));
    assertTrue(!i0 .isa(str0));
    assertTrue(!i0 .isa(tup0));

    assertTrue(str .isa(str0));
    assertTrue(tup .isa(tup0));

    assertTrue(str0.isa(oop0));
    assertTrue(tup0.isa(oop0));
    
    assertTrue(oop0.isa(bot ));
    
    // Crossing ints and OOP+null
    Type  i8 = TypeInt.INT8;
    Type xi8 = i8.dual();
    assertEquals( Type.SCALAR, xi8.meet(oop_)); // ~OOP+0 &   ~i8 -> 0
  }
  
  @Test public void testStructTuple() {
    Type.init0(new HashMap<>());
    Type nil  = TypeNil.NIL;
    // Tuple is more general that Struct
    Type tf = TypeStruct.TFLT64; //  (  flt64); choice leading field name
    Type tsx= TypeStruct.X;      // @{x:flt64}; fixed  leading field name
    Type tff = tsx.meet(tf);     //
    assertEquals(tf,tff);        // tsx.isa(tf)
    TypeStruct t0 = TypeStruct.make(nil); //  (nil)
    TypeStruct ts0= TypeStruct.make(new String[]{"x"},nil);  // @{x:nil}
    Type tss = ts0.meet(t0);
    assertEquals(t0,tss);      // t0.isa(ts0)

    // meet @{c:0}? and @{c:@{x:1}?,}
    Type    nc0 = TypeNil.make(TypeStruct.make(new String[]{"c"},TypeNil.NIL )); // @{c:nil}?
    Type    nx1 = TypeNil.make(TypeStruct.make(new String[]{"x"},TypeInt.TRUE)); // @{x:1}?
    TypeOop cx  = TypeStruct.make(new String[]{"c"},nx1); // @{c:@{x:1}?}
    // JOIN tosses the top-level null choice, and the inside struct choice
    Type cj  = nc0.join(cx);
    Type c0  = TypeStruct.make(new String[]{"c"},TypeNil.NIL); // @{c:0}
    assertEquals(c0,cj);
  }

  @Ignore @Test public void testUnion() {
    Type.init0(new HashMap<>());

    Type a = TypeUnion.make(false,TypeInt.FALSE,TypeFlt.FLT32);
    assertEquals(TypeFlt.FLT32,a); // 0 isa FLT32, so collapses
    Type b = TypeUnion.make(false,TypeInt.con(123456789),TypeFlt.FLT32);
    assertEquals(Type.REAL,b); // Does not collapse
    Type c = TypeUnion.make(false,TypeInt.FALSE,TypeInt.TRUE);
    assertEquals(TypeInt.BOOL,c); // {0*1} combines to bool
    Type d = TypeUnion.make(false,TypeInt.FALSE,TypeInt.FALSE);
    assertTrue(d instanceof TypeUnion); // Does not collapse

    //Type e = TypeInt.FALSE.meet(TypeUnion.NIL);
    //assertEquals(TypeInt.FALSE,e);
  }


  // meet of functions: arguments *join*, fidxes union (meet), and return types
  // meet.  Inverse of all of this for functions join'ing, and UnresolvedNode
  // is a function join.
  @Test public void testFunction() {
    Type.init0(new HashMap<>());
    Type ignore = TypeTuple.ANY; // Break class-loader cycle; load Tuple before Fun.

    TypeFunPtr gf = TypeFunPtr.GENERIC_FUNPTR;

    TypeFunPtr f1i2i = TypeFunPtr.make(TypeTuple.INT64,TypeInt.INT64,1/*fidx*/,1/*nargs*/);
    assertTrue(f1i2i.isa(gf));
    TypeFunPtr f1f2f = TypeFunPtr.make(TypeTuple.FLT64,TypeFlt.FLT64,2/*fidx*/,1/*nargs*/);
    assertTrue(f1f2f.isa(gf));
    TypeFunPtr mt = (TypeFunPtr)f1i2i.meet(f1f2f);
    TypeFunPtr f3i2r = TypeFunPtr.make(TypeTuple.INT32,Type.REAL    ,Bits.make0(-2,new long[]{(1<<1)|(1<<2)}),1/*nargs*/);
    assertEquals(f3i2r,mt);
    assertTrue(f3i2r.isa(gf));
    assertTrue(f1i2i.isa(f3i2r));
    assertTrue(f1f2f.isa(f3i2r));
    
    TypeFunPtr f2 = TypeFunPtr.any(2,23); // Some generic function (happens to be #23, '&')
    assertTrue(f2.isa(gf));
  }

  // Test limits on recursive type structures; recursively building nested
  // structures caps out in the type system at some reasonable limit.
  @Test public void testRecursive() {
    Type.init0(new HashMap<>());

    // Nest a linked-list style tuple 10 deep; verify actual depth is capped at
    // less than 5.
    Type told = Type.SCALAR;
    Type t0 = TypeNil.NIL;
    for( int i=0; i<10; i++ ) {
      told = TypeStruct.make(TypeStruct.FLDS(2),t0,TypeInt.con(i));
      t0 = told.meet(t0);    // Must be a phi-meet in any data loop
    }
    int max_depth = type_depth(t0,new HashMap<>());
    assertTrue(max_depth<5);
  }

  // Classic breadth-first-search algo
  private int type_depth( Type init, HashMap<Type,Integer> ds ) {
    int d = 0;
    Ary<Type> work0 = new Ary<>(new Type[0]);
    Ary<Type> work1 = new Ary<>(new Type[0]);
    ds.put(work0.push(init),d);
    
    while( !work0.isEmpty() ) {
      final int fd = ++d;
      assert work1.isEmpty();
      final Ary<Type> fwork1 = work1;
      for( Type t : work0 )
        t.iter((Consumer<Type>) tc ->
               { if( tc !=null && ds.get(tc)==null ) ds.put(fwork1.push(tc),fd); }  );
      work0.clear();  work1 = work0;  work0 = fwork1; // Swap worklists
    }
    return d;                   // Max depth
  }
  
  
  // TODO: Observation: value() calls need to be monotonic, can test this.
  @Test public void testCommuteSymmetricAssociative() {
    Type.init0(new HashMap<>());

    assertTrue(Type.check_startup());
  }  
}
