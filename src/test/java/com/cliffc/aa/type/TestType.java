package com.cliffc.aa.type;

import org.junit.Ignore;
import org.junit.Test;

import java.util.HashMap;

import static org.junit.Assert.*;


public class TestType {
  // temp/junk holder for "instant" junits, when debugged moved into other tests
  @Test public void testType() {
    Type.init0(new HashMap<>());
    Type t0 = TypeFunPtr.GENERIC_FUNPTR; // includes nil
    Type t1 = Type.NSCALR;
    Type t2 = t0.join(t1);
    assertFalse(t2.must_nil());
    //assertEquals(ALL_FUN,t2);

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
    Type pmem0= TypeMemPtr.OOP0;    // *[ALL]?
    Type pmem = TypeMemPtr.OOP ;    // *[ALL]
    Type pstr0= TypeMemPtr.STR0;    // *[str]?
    TypeMemPtr pstr = TypeMemPtr.STRPTR; // *[str]
    Type ptup0= TypeMemPtr.STRUCT0; // *[tup]?
    Type ptup = TypeMemPtr.STRUCT;  // *[tup]
    
    Type pabc0= TypeMemPtr.ABC0;    // *["abc"]?
    TypeMemPtr pabc = TypeMemPtr.ABCPTR; // *["abc"]
    Type pzer = TypeMemPtr.make    (BitsAlias.new_alias(BitsAlias.REC)._idx);// *[(0)]
    Type pzer0= TypeMemPtr.make_nil(BitsAlias.new_alias(BitsAlias.REC)._idx);// *[(0)]?
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
    assertTrue (xstr0.isa(pabc0)); // ~*[1]+0 vs ~*[2]?
    assertFalse(xstr .isa(pabc ));
    // We can instead assert that values loaded are compatible:
    assertTrue (TypeMem.MEM_STR.dual().ld(xstr).isa(TypeMem.MEM_ABC.ld(pabc)));
    
    assertTrue (xtup0.isa( nil ));
    assertTrue (xtup0.isa(pzer0));
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

    // meet @{c:0}? and @{c:@{x:1}?,}
    TypeObj a1 = TypeStruct.make(new String[]{"c"},TypeNil.NIL ); // @{c:nil}
    TypeObj a2 = TypeStruct.make(new String[]{"c"},TypeMemPtr.make_nil(3)); // @{c:*{3#}?}
    TypeObj a3 = TypeStruct.make(new String[]{"x"},TypeInt.TRUE); // @{x: 1 }
    TypeMem mem = TypeMem.make0(new TypeObj[]{null,TypeObj.OBJ,a1,a2,a3});
    // *[1]? join *[2] ==> *[1+2]
    Type ptr12 = TypeMemPtr.make_nil(1).join( TypeMemPtr.make(2));
    // mem.ld(*[1+2]) ==> @{c:0}
    Type ld = mem.ld((TypeMemPtr)ptr12);
    assertEquals(a1,ld);
  }

  // meet of functions: arguments *join*, fidxes union (meet), and return types
  // meet.  Inverse of all of this for functions join'ing, and UnresolvedNode
  // is a function join.
  @Test public void testFunction() {
    Type.init0(new HashMap<>());
    Type ignore = TypeTuple.ANY; // Break class-loader cycle; load Tuple before Fun.

    TypeFunPtr gf = TypeFunPtr.GENERIC_FUNPTR;
    TypeMem nomem = TypeMem.MEM.dual();

    TypeFunPtr f1i2i = TypeFunPtr.make_new(TypeTuple.INT64,nomem,TypeInt.INT64,nomem,1/*nargs*/);
    assertTrue(f1i2i.isa(gf));
    TypeFunPtr f1f2f = TypeFunPtr.make_new(TypeTuple.FLT64,nomem,TypeFlt.FLT64,nomem,1/*nargs*/);
    assertTrue(f1f2f.isa(gf));
    TypeFunPtr mt = (TypeFunPtr)f1i2i.meet(f1f2f);
    TypeFunPtr f3i2r = TypeFunPtr.make(TypeTuple.INT32,nomem,Type.REAL    ,nomem,BitsFun.make0(-2,new long[]{(1<<1)|(1<<2)}),1/*nargs*/);
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

    // Recursive types no longer cyclic in the concrete definition?  Because
    // TypeObj can contain TypeMemPtrs but not another nested TypeObj...
    final int alias1 = 1;
    final TypeMemPtr ts0ptr = TypeMemPtr.make    (alias1);
    final TypeMemPtr ts0ptr0= TypeMemPtr.make_nil(alias1);
    
    // Anonymous recursive structs -
    // - struct with pointer to self
    TypeStruct ts0 = TypeStruct.malloc(false,flds,new Type[2],new byte[]{1,1});
    ts0._ts[0] = ts0ptr;    ts0._cyclic = true;
    ts0._ts[1] = TypeInt.INT64;
    ts0 = ts0.install_cyclic();
    TypeMem ts0mem = TypeMem.make(alias1,ts0); // {1:@{n:*[1],v:int} }
    
    // - struct with pointer to self or nil
    TypeStruct ts1 = TypeStruct.malloc(false,flds,new Type[2],new byte[]{1,1});
    ts1._ts[0] = ts0ptr0;  ts1._cyclic = true;
    ts1._ts[1] = TypeInt.INT64;
    ts1 = ts1.install_cyclic();
    TypeMem ts1mem = TypeMem.make(alias1,ts1); // {1:@{n:*[0,1],v:int} }
    
    Type tsmt = ts0.meet(ts1);
    assertEquals(ts1,tsmt);
    Type tsmemmt = ts0mem.meet(ts1mem);
    assertEquals(ts1mem,tsmemmt);

    // Cyclic named struct: Memory#2 :A:@{n:*[0,2],v:int}
    // If we unrolled this (and used S for Struct and 0 for Nil) we'd get:
    // AS0AS0AS0AS0AS0AS0...
    final int alias2 = 2;
    TypeMemPtr tptr2= TypeMemPtr.make_nil(alias2); // *[0,2]
    TypeStruct ts2 = TypeStruct.make(flds,tptr2,TypeInt.INT64); // @{n:*[0,2],v:int}
    TypeName ta2 = TypeName.make("A",TypeName.TEST_SCOPE,ts2);

    // Peel A once without the nil: Memory#3: A:@{n:*[2],v:int}
    // ASAS0AS0AS0AS0AS0AS0...
    final int alias3 = 3;
    TypeMemPtr tptr3= TypeMemPtr.make(alias3); // *[3]
    TypeStruct ts3 = TypeStruct.make(flds,tptr2,TypeInt.INT64); // @{n:*[2],v:int}
    TypeName ta3 = TypeName.make("A",TypeName.TEST_SCOPE,ts3);

    // Peel A twice without the nil: Memory#4: A:@{n:*[3],v:int}
    // ASASAS0AS0AS0AS0AS0AS0...
    final int alias4 = 4;
    TypeStruct ts4 = TypeStruct.make(flds,tptr3,TypeInt.INT64); // @{n:*[3],v:int}
    TypeName ta4 = TypeName.make("A",TypeName.TEST_SCOPE,ts4);

    // Then make a MemPtr{3,4}, and ld - should be a PeelOnce
    // Starting with the Struct not the A we get:
    // Once:  SAS0AS0AS0AS0AS0AS0...
    // Twice: SAS AS0AS0AS0AS0AS0...
    // Meet:  SAS0AS0AS0AS0AS0AS0...
    // which is the Once yet again
    TypeMem mem234 = TypeMem.make0(new TypeObj[]{null,TypeObj.OBJ,ta2,ta3,ta4});
    TypeMemPtr ptr34 = TypeMemPtr.make(alias3,alias4);

    // Since hacking ptrs about from mem values, no cycles so instead...
    Type mta = mem234.ld(ptr34);
    //assertEquals(ta3,mta);
    Type xta = TypeName.make("A",TypeName.TEST_SCOPE,TypeStruct.make(flds,TypeMemPtr.make(0,2,3),TypeInt.INT64));
    assertEquals(xta,mta);


    
    // Mismatched Names in a cycle; force a new cyclic type to appear
    final int alias5 = 5;
    TypeStruct tsnb = TypeStruct.make(flds,TypeMemPtr.make(0,alias5),TypeFlt.FLT64);
    TypeName tfb = TypeName.make("B",TypeName.TEST_SCOPE,tsnb);
    Type mtab = ta2.meet(tfb);
    
    // TODO: Needs a way to easily test simple recursive types
    TypeStruct mtab0 = (TypeStruct)mtab;
    assertEquals("n",mtab0._flds[0]);
    assertEquals("v",mtab0._flds[1]);
    TypeMemPtr mtab1 = (TypeMemPtr)mtab0.at(0);
    assertTrue(mtab1._aliases.test(alias2)&& mtab1._aliases.test(alias5));
    assertEquals(Type.REAL,mtab0.at(1));
    

    // In the ptr/mem model, all Objs from the same NewNode are immediately
    // approximated by a single Alias#.  This stops any looping type growth.
    // The only way to get precision back is to inline the NewNode and get new
    // Alias#s.
    
    // Nest a linked-list style tuple 10 deep; verify actual depth is capped at
    // less than 5.  Any data loop must contain a Phi; if structures are
    // nesting infinitely deep, then it must contain a NewNode also.
    //Type phi = TypeNil.NIL;
    //for( int i=0; i<20; i++ ) {
    //  TypeStruct newt = TypeStruct.make(TypeStruct.FLDS(2),phi,TypeInt.con(i));
    //  phi=com.cliffc.aa.node.NewNode.approx(newt,phi);
    //}
    //int d = phi.depth()-9999; // added +9999 for cycle
    //assertTrue(0 <= d && d <10);
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
  @Ignore
  @Test public void testCycles() {
    Type.init0(new HashMap<>());
    Type ignore0 = TypeTuple.ALL; // Break class-loader cycle; load Tuple before Fun.
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
