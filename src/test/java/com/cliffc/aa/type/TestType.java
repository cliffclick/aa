package com.cliffc.aa;

import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Bits;
import org.junit.Ignore;
import org.junit.Test;

import java.util.HashMap;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;


public class TestType {
  // temp/junk holder for "instant" junits, when debugged moved into other tests
  @Test public void testType() {
    Type.init0(new HashMap<>());
    Type ignore = TypeTuple.ALL; // Break class-loader cycle; load Tuple before Fun.

    Type rez = TypeStruct.POINT.join(TypeStruct.A);

    Type rbq = Type.NSCALR.join(TypeName.TEST_E2);
    Type rbz = Type.NSCALR.join(TypeName.TEST_ENUM);
    assertEquals(TypeName.make("__test_enum",TypeName.TEST_SCOPE,TypeInt.make(-1,8,0)),rbz);
    Type rbp = TypeOop.OOP.join(TypeName.TEST_ENUM);
    assertEquals(Type.XSCALAR,rbp);
    Type rby = Type.NNUM  .join(TypeName.TEST_ENUM);
    assertEquals(TypeName.make("__test_enum",TypeName.TEST_SCOPE,TypeInt.make(-1,8,0)),rby);
    Type ra = Type.XNSCALR.join(TypeName.TEST_ENUM);
    assertEquals(Type.XSCALAR,ra);
    Type xo1 = TypeOop.XOOP.join(TypeName.TEST_ENUM);
    assertEquals(Type.XSCALAR,xo1);
    Type rx = Type.NNUM.meet(TypeName.TEST_ENUM.dual()).dual();
    assertEquals(Type.XNUM,rx);
    Type tb4 = Type.NNUM.meet(TypeName.TEST_ENUM.dual());
    assertEquals(Type.NUM,tb4);
    Type rb = Type.XNNUM.join(TypeName.TEST_ENUM);
    assertEquals(Type.XNUM,rb);

    Type r32 = Type.XSCALAR.join(TypeName.TEST_ENUM);
    assertEquals(Type.XSCALAR,r32);
    Type r02 = Type.XNUM.join(TypeName.TEST_ENUM);
    assertEquals(Type.XNUM,r02);
    Type rmt = r02.meet(TypeName.TEST_ENUM);
    assertEquals(TypeName.TEST_ENUM,rmt);
    
    assertEquals(TypeFlt.FLT32,Type.XNSCALR.meet(TypeFlt.FLT32)); // ~nScalar isa flt32
    Type tf02 = Type.XNSCALR .join(TypeFlt.PI); // Type.XNSCALR; PI is a member directly of ~nScalar
    Type tf12 = TypeFlt.FLT32.join(TypeFlt.PI); // TypeFlt.XFLT64; ugly lift
    Type tfmt = tf02.meet(tf12); // Drops nil?  TypeFlt.XNFLT64
    assertEquals(tf12,tfmt); // Expect A.join(C) isa B.join(C)
    Type nflt64 = TypeFlt.make(-1,64,0);
    Type nint32 = TypeInt.make(-1,32,0);
    Type tfx = nint32.meet(nflt64);
    assertEquals(nflt64,tfx);
    // int64 isa all
    // int64.join(__test_flt:flt32) isa all.join(__test_flt:flt32)
    // ~int64.meet(__test_flt:~flt32).~ isa __test_flt:flt32
    // ==>> ~int64 .meet(__test_flt:~flt32).~
    // ==>> __test_flt:~int64 .meet(__test_flt:~flt32).~
    // ==>> __test_flt:~int16 .meet(__test_flt:~flt32).~
    // ==>> __test_flt:meet(~int16,~flt32).~
    // ==>> __test_flt:~int16.~
    // ==>> __test_flt:int16
    Type  xint64 = TypeInt.make(2,64,0);
    Type  xflt32 = TypeFlt.make(2,32,0);
    Type nxflt32 = TypeName.make("__test_enum",TypeName.TEST_SCOPE,xflt32);
    Type nxint16 = TypeName.make("__test_enum",TypeName.TEST_SCOPE,TypeInt.INT16);
    Type  xfimt  = xint64.meet(nxflt32).dual();
    assertEquals(nxint16,xfimt);
    Type nxx = TypeInt.FALSE.join(nflt64);
    assertEquals(TypeInt.BOOL.dual(),nxx);

    Type q02 = Type.XNSCALR.meet(TypeName.TEST_ENUM);
    assertEquals(TypeInt.INT8,q02);
    Type q02j= Type.XNSCALR.join(TypeName.TEST_ENUM);
    assertEquals(Type.XSCALAR,q02j);
    Type q12 = Type.XNNUM  .meet(TypeName.TEST_ENUM);
    assertEquals(TypeInt.INT8,q12);
    Type q12j= Type.XNNUM  .join(TypeName.TEST_ENUM);
    assertEquals(Type.XNUM,q12j);

    Type tb5 = Type.XNSCALR.meet(TypeFun.FUN1.dual());
    assertEquals(TypeFun.FUN1.dual(),tb5);
    Type tb3 = Type.XNSCALR.meet(TypeInt.FALSE);
    assertEquals(TypeInt.BOOL,tb3);
    Type tb2 = Type.XNSCALR.meet(Type.XNUM);
    assertEquals(Type.XNNUM,tb2);
    Type tb1 = TypeNil.XOOP.meet(Type.NSCALR);
    assertEquals(Type.NSCALR,tb1);
    
    Type that= Type.XNSCALR;
    Type dual= Type. NSCALR;
    Type t   = TypeNil.OOP;
    Type mt  = t.meet(that);
    Type tb  = mt.dual().meet(dual);
    assertEquals(dual,tb);
    
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
    Type tup  = TypeStruct.make(); // tup no null ; infinite repeat of SCALAR fields
    Type tup0 = TypeNil.make(tup); // tup? (tup AND null); infinite repeat of SCALAR fields
    Type i0   = TypeInt.FALSE;
    Type abc  = TypeStr  .ABC;
    Type fld  = TypeStruct.make(TypeInt.INT64);  // 1 field of int64
    
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
    assertEquals( Type.NSCALR, xi8.meet(oop_)); // ~OOP+0 &   ~i8 -> 0
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
    String[] flds = new String[]{"n","v"};

    // Anonymous recursive structs
    TypeStruct ts0 = TypeStruct.malloc(false,flds,new Type[2]);
    ts0._ts[0] = ts0;    ts0._cyclic = true;
    ts0._ts[1] = TypeInt.INT64;
    ts0 = ts0.install_cyclic();

    TypeStruct ts1 = TypeStruct.malloc(false,flds,new Type[2]);
    Type.RECURSIVE_MEET++;
    Type tsn = TypeNil.make(ts1);  tsn._cyclic = true;
    ts1._ts[0] = tsn;    ts1._cyclic = true;
    ts1._ts[1] = TypeInt.INT64;
    Type.RECURSIVE_MEET--;
    ts1 = ts1.install_cyclic();

    Type tsmt = ts0.meet(ts1);
    assertEquals(ts1,tsmt);
    
    // Cyclic named struct: "A:@{n:A?,v:int64}"
    // If we unrolled this (and used S for Struct and 0 for Nil) we'd get:
    // AS0AS0AS0AS0AS0AS0...
    TypeName tfa = TypeName.make_forward_def_type("A",TypeName.TEST_SCOPE);
    Type tna = TypeNil.make(tfa);
    TypeStruct tsna = TypeStruct.make(flds,tna,TypeInt.INT64);
    TypeName ta = tfa.merge_recursive_type(tsna);
    // Peel A once without a nil: "A:@{n:A:@{n:A?,v:int64},v:int64}"
    // ASAS0AS0AS0AS0AS0AS0...
    TypeStruct taa = TypeStruct.make(flds,ta,TypeInt.INT64);
    TypeName tan = TypeName.make("A",TypeName.TEST_SCOPE,taa);
    // Peel A twice without a nil: "A:@{n:A:@{n:A:@{n:A?,v:int64},v:int64},v:int64}"
    // ASASAS0AS0AS0AS0AS0AS0...
    TypeStruct taaa = TypeStruct.make(flds,tan,TypeInt.INT64);
    // Starting with the Struct not the A we get:
    // Once:  SAS0AS0AS0AS0AS0AS0...
    // Twice: SAS AS0AS0AS0AS0AS0...
    // Meet:  SAS0AS0AS0AS0AS0AS0...
    // which is the Once yet again
    Type mta = taaa.meet(taa);
    assertEquals(taa,mta);

    // Mismatched Names in a cycle; force a new cyclic type to appear
    TypeName tfb = TypeName.make_forward_def_type("B",TypeName.TEST_SCOPE);
    Type tnb = TypeNil.make(tfb);
    TypeStruct tsnb = TypeStruct.make(flds,tnb,TypeFlt.FLT64);
    TypeName tb = tfb.merge_recursive_type(tsnb);
    
    Type mtab = tfa.meet(tfb);
    // TODO: Needs a way to easily test simple recursive types
    TypeStruct mtab0 = (TypeStruct)mtab;
    assertEquals("n",mtab0._flds[0]);
    assertEquals("v",mtab0._flds[1]);
    TypeNil mtab1 = (TypeNil)mtab0.at(0);
    assertEquals(mtab,mtab1._t);
    assertEquals(Type.REAL,mtab0.at(1));
    

    // Nest a linked-list style tuple 10 deep; verify actual depth is capped at
    // less than 5.
    Type told, t0 = TypeNil.NIL;
    for( int i=0; i<20; i++ ) {
      told = TypeStruct.make(TypeStruct.FLDS(2),t0,TypeInt.con(i));
      t0 = told.meet(t0);    // Must be a phi-meet in any data loop
    }
    assertTrue(t0.depth()<10);

  }

  // TODO: Observation: value() calls need to be monotonic, can test this.
  @Test public void testCommuteSymmetricAssociative() {
    Type.init0(new HashMap<>());

    assertTrue(Type.check_startup());
  }  
}
