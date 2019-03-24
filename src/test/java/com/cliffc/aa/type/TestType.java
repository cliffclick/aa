package com.cliffc.aa.type;

import com.cliffc.aa.util.Bits;
import org.junit.Ignore;
import org.junit.Test;

import java.util.HashMap;

import static org.junit.Assert.*;


public class TestType {
  // temp/junk holder for "instant" junits, when debugged moved into other tests
  @Test public void testType() {
    Type.init0(new HashMap<>());
    Type t0 = Type.XNSCALR; // ~nScalar ; high any scalar not nil
    Type t1 = TypeNil.STR;  // Low String-ptr-and-nil.
    Type t2 = t0.meet(t1);
    assertEquals(t2,TypeNil.STR);
    Type t02 = t2._dual.meet(t0._dual);// ptr-to-choice-str-or-nil meet scalar-not-nil
    assertEquals(t02,t0._dual);
    Type t12 = t2._dual.meet(t1._dual);
    assertEquals(t12,t1._dual);
    
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

  // Memory is on a different line than pointers.
  // Memory canNOT be nil, but ptrs to memory can be nil.
  // Memory contents can be any/all, vs ptrs being any/all.
  // A any-ptr-alias#6 means *any* of the alias#6 choices; same for all.
  // all ->  mem  -> { str,tup} -> { string constants, tuple constants} -> {~str,~tup} -> ~mem    -> any
  // all -> *mem? -> {*mem,nil} -> {*str,*tup,nil} -> {~*str,~*tup,nil} -> {~*mem,nil} -> ~*mem+? -> any
  
  @Test public void testOOPsNulls() {
    Type.init0(new HashMap<>());
    Type bot = Type      .ALL;

    Type mem = TypeMem   .MEM;  // All memory
    Type str = TypeStr   .STR;  // All Strings
    Type tup = TypeStruct.ALLSTRUCT; // All Structs
    
    Type abc = TypeStr  .ABC;   // String constant
    Type zer = TypeInt  .FALSE;
    Type tp0 = TypeStruct.make(zer);  // tuple of a '0'
    
    Type tupX= tup.dual();
    Type strX= str.dual();
    Type memX= mem.dual();

    Type top = Type.ANY;

    assertTrue( top.isa(memX));

    //assertTrue(memX.isa(strX)); // mem is a CONTAINER for memory objects, e.g. Struct,Str
    //assertTrue(memX.isa(tupX));

    assertTrue( strX.isa(abc));
    assertTrue( tupX.isa(tp0));
    assertTrue(!strX.isa(zer));
    assertTrue(!tupX.isa(zer));

    assertTrue( abc .isa(str));
    assertTrue( tp0 .isa(tup));
    assertTrue(!zer .isa(str));
    assertTrue(!zer .isa(tup));

    //assertTrue( str .isa(mem)); // mem is a CONTAINER for memory objects, e.g. Struct,Str
    //assertTrue( tup .isa(mem));
    
    assertTrue( mem .isa(bot));

    // ---
    Type pmem0= TypeNil   .OOP;    // *[ALL]?
    Type pmem = TypeMemPtr.MEMPTR; // *[ALL]
    Type pstr0= TypeNil   .STR;    // *[str]?
    TypeMemPtr pstr = TypeMemPtr.STRPTR; // *[str]
    Type ptup0= TypeNil   .TUP;    // *[tup]?
    Type ptup = TypeMemPtr.TUPPTR; // *[tup]
    
    Type pabc0= TypeNil   .ABC;    // *["abc"]?
    TypeMemPtr pabc = TypeMemPtr.ABCPTR; // *["abc"]
    Type pzer = TypeMemPtr.make(TypeMem.new_alias());// *[(0)]
    Type pzer0= TypeNil.make(pzer);// *[(0)]?
    Type nil  = TypeNil.NIL;

    Type xtup = ptup .dual();
    Type xtup0= ptup0.dual();
    TypeMemPtr xstr = pstr.dual();
    Type xstr0= pstr0.dual();
    Type xmem = pmem .dual();
    Type xmem0= pmem0.dual();

    assertTrue( top .isa(xmem0));
    assertTrue(xmem0.isa(xmem ));
    
    assertTrue(xmem0.isa(xstr0));
    assertTrue(xmem .isa(xstr ));
    assertTrue(xmem0.isa(xtup0));
    assertTrue(xmem .isa(xtup ));

    assertTrue(xstr0.isa( nil ));
    
    // This is a choice ptr-to-alias#1, vs a nil-able ptr-to-alias#2.  Since
    // they are from different alias classes, they are NEVER equal (unless both
    // nil).  We cannot tell what they point-to, so we do not know if the
    // memory pointed-at is compatible or not.
    assertFalse(xstr0.isa(pabc0)); // ~*[1]+0 vs ~*[2]?
    assertFalse(xstr .isa(pabc ));
    // We can instead assert that values loaded are compatible:
    assertTrue (TypeMem.MEM_STR.dual().ld(xstr).isa(TypeMem.MEM_ABC.ld(pabc)));
    
    assertTrue (xtup0.isa( nil ));
    assertFalse(xtup0.isa(pzer0));
    assertFalse(xtup .isa(pzer ));
    //assertTrue(TypeMem.MEM_TUP.dual().ld(xstr).isa(TypeMem.MEM_ZER.ld(pabc)));
    
    assertTrue ( nil .isa(pabc0));
    assertTrue ( nil .isa(pzer0));
    
    assertTrue ( nil .isa(pstr0));
    assertFalse(pabc0.isa(pstr0));
    assertFalse(pabc .isa(pstr ));
    assertTrue (TypeMem.MEM_ABC.ld(pabc).isa(TypeMem.MEM_STR.ld(pstr)));
    assertTrue ( nil .isa(ptup0));
    assertFalse(pzer0.isa(ptup0));
    assertFalse(pzer .isa(ptup ));
    //assertTrue(TypeMem.MEM_TUP.dual().ld(xstr).isa(TypeMem.MEM_ZER.ld(pabc)));
    assertTrue (ptup0.isa(pmem0));
    assertTrue (ptup .isa(pmem ));
    
    assertTrue (pmem .isa(pmem0));
    assertTrue (pmem0.isa( bot ));
    
    
    // Crossing ints and *[ALL]+null
    Type  i8 = TypeInt.INT8;
    Type xi8 = i8.dual();
    assertEquals( Type.NSCALR, xi8.meet(xmem0)); // ~OOP+0 & ~i8 -> 0
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

    //// meet @{c:0}? and @{c:@{x:1}?,}
    //Type    nc0 = TypeNil.make(TypeStruct.make(new String[]{"c"},TypeNil.NIL )); // @{c:nil}?
    //Type    nx1 = TypeNil.make(TypeStruct.make(new String[]{"x"},TypeInt.TRUE)); // @{x:1}?
    //TypeOop cx  = TypeStruct.make(new String[]{"c"},nx1); // @{c:@{x:1}?}
    //// JOIN tosses the top-level null choice, and the inside struct choice
    //Type cj  = nc0.join(cx);
    //Type c0  = TypeStruct.make(new String[]{"c"},TypeNil.NIL); // @{c:0}
    //assertEquals(c0,cj);
    throw com.cliffc.aa.AA.unimpl();
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
    TypeStruct ts0 = TypeStruct.malloc(false,flds,new Type[2],new byte[]{1,1});
    ts0._ts[0] = ts0;    ts0._cyclic = true;
    ts0._ts[1] = TypeInt.INT64;
    ts0 = ts0.install_cyclic();

    TypeStruct ts1 = TypeStruct.malloc(false,flds,new Type[2],new byte[]{1,1});
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
    tfb.merge_recursive_type(tsnb);
    
    Type mtab = tfa.meet(tfb);
    // TODO: Needs a way to easily test simple recursive types
    TypeStruct mtab0 = (TypeStruct)mtab;
    assertEquals("n",mtab0._flds[0]);
    assertEquals("v",mtab0._flds[1]);
    TypeNil mtab1 = (TypeNil)mtab0.at(0);
    assertEquals(mtab,mtab1._t);
    assertEquals(Type.REAL,mtab0.at(1));
    

    // Nest a linked-list style tuple 10 deep; verify actual depth is capped at
    // less than 5.  Any data loop must contain a Phi; if structures are
    // nesting infinitely deep, then it must contain a NewNode also.
    Type phi = TypeNil.NIL;
    for( int i=0; i<20; i++ ) {
      TypeStruct newt = TypeStruct.make(TypeStruct.FLDS(2),phi,TypeInt.con(i));
      phi=com.cliffc.aa.node.NewNode.approx(newt,phi);
    }
    int d = phi.depth()-9999; // added +9999 for cycle
    assertTrue(0 <= d && d <10);
  }


  // For any cyclic type with the cycle larger than 1, the other members of the
  // cycle can be produced by appropriate meets... but all are equivalent.
  // Example: T = :(T?,Scalar).  A simple linked-list-or-nil situation.
  // Unrolled:   TypeStruct ==> TypeNil ==> ...
  // Unrolled:   S?S?S?S?S?S?....
  //
  // Adding a nil to T gives T back, except rotated around the cycle:
  // Unrolled:   TypeNil ==> TypeStruct ==> TypeNil ==> ...
  // Unrolled:  ?S?S?S?S?S?S?....
  // Note: Leading '?' but otherwise infinitely equal to the prior unroll
  // 
  @Test public void testCycles() {
    Type.init0(new HashMap<>());
    Type ignore0 = TypeTuple.ALL; // Break class-loader cycle; load Tuple before Fun.
    Type ignore1 = TypeNil.OOP; // Break class-loader cycle; load Tuple before Fun.
    String[] flds = TypeStruct.FLDS(2);

    // T = :(T?,i64)
    TypeStruct T = TypeStruct.malloc(false,flds,new Type[2],new byte[]{1,1});
    Type.RECURSIVE_MEET++;
    Type TN = TypeNil.make(T);  TN._cyclic = true;
    T._ts[0] = TN;    T._cyclic = true;
    T._ts[1] = TypeInt.INT64;
    Type.RECURSIVE_MEET--;
    T = T.install_cyclic();
    TN = T._ts[0]; // Reload after interning

    // Adding a Nil to T brings to another spot in the cycle
    Type tn2 = TypeNil.make(T);
    assertSame(TN, tn2);

    // Meet of 2 elements of the cycle yields the cycle back.
    Type mt = T.meet(TN);
    assertTrue(mt==T || mt==TN);

    // Test from an unrolled map() call, during GCP one of the guarding IF tests
    // is still showing false, so we alternate having NILs or not.

    // ((T,i64)?,i64) .isa( ((((T,i64)?,i64),i64)?,i64) ) ==>
    //  (T,i64)       .isa(  (((T,i64)?,i64),i64)       ) ==>
    //   T            .isa(   ((T,i64)?,i64)            ) ==>
    //   T      .meet(((T,i64)?,i64)) == ((T,i64)?,i64) ==>
    //  (T?,i64).meet(((T,i64)?,i64)) == ((T,i64)?,i64) ==>
    //  (T?.meet((T,i64)?),i64) == ((T,i64)?,i64) ==>
    //   T?.meet((T,i64)?)      ==  (T,i64)?      ==>
    //   T.meet((T,i64))?       ==  (T,i64)?      ==>
    //   T.meet((T,i64))        ==  (T,i64)       ==>
    //  (T?,i64).meet((T,i64)) ==   (T,i64)       ==>
    //   T?     .meet( T     ) ==    T            ==>
    // T? is a T that is rotated around the cycle 1 nil notch.
    // So T?==T
    //   T         .meet( T        ) ==   T
    // T == T.  QED

    Type Ts      = TypeStruct.make(T     ,TypeInt.INT64); //    (T,i64)

    // Ugh: backwards from QED above; in fact Ts isa T since adding a Nil to a
    // Ts is strictly lower in the lattice... and immediately makes it a T.
    Type mt3 = T.meet(Ts);
    assertEquals(T,mt3);

    Type Ts0     = TypeNil   .make(Ts);                   //    (T,i64)?
    Type Ts0s    = TypeStruct.make(Ts0   ,TypeInt.INT64); //   ((T,i64)?,i64)

    // Ugh: backwards from QED above, same as above: adding any counts of
    // TypeNil clearly makes an unrolled T which rolls back up to a T.
    Type mt2 = T.meet(Ts0s);
    assertEquals(T,mt2);

    Type Ts0ss   = TypeStruct.make(Ts0s  ,TypeInt.INT64); //  (((T,i64)?,i64),i64)
    Type Ts0ss0  = TypeNil   .make(Ts0ss);                //  (((T,i64)?,i64),i64)?
    Type Ts0ss0s = TypeStruct.make(Ts0ss0,TypeInt.INT64); // ((((T,i64)?,i64),i64)?,i64)

    Type mt1 = Ts0s.meet(Ts0ss0s); // Ts0s.isa(Ts0ss0s) ==> Ts0s.meet(Ts0ss0s) == Ts0ss0s
    assertEquals(Ts0s,mt1);

    Type mt0 = T.meet(Ts0ss0s); // Ts0s.isa(Ts0ss0s) ==> Ts0s.meet(Ts0ss0s) == Ts0ss0s
    assertEquals(T,mt0);
  }
  
  @Test public void testCommuteSymmetricAssociative() {
    Type.init0(new HashMap<>());

    assertTrue(Type.check_startup());
  }  
}
