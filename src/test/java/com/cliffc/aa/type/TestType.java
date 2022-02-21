package com.cliffc.aa.type;

import com.cliffc.aa.node.PrimNode;
import com.cliffc.aa.util.Ary;
import org.junit.Test;

import java.util.HashMap;

import static com.cliffc.aa.type.TypeMemPtr.NO_DISP;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;


public class TestType {
  // temp/junk holder for "instant" junits, when debugged moved into other tests
  @Test public void testType() {
  }

  @Test public void testTFPChain() {
    // Problem is that a Lambda Transfer Function wants to simply wrap its return in a TFP.
    // In recursive cases we might get:
    //  INPUT                   WRAP WITH [2]{->}               APPROX
    // ~scalar          ==>> [2]{-> ~scalar         } ==>> $[2  ]{->~scalar}
    // $[2  ]{->$[2  ]} ==>> [2]{-> $[2  ]{->$[2  ]}} ==>> $[2  ]{->$[2]   }
    // $[2,3]{->$[2,3]} ==>> [2]{-> $[2,3]{->$[2,3]}} ==>> $[2,3]{->$[2,3] } \___ NOT MONOTONIC
    // scalar           ==>> [2]{-> scalar          } ==>> $[2  ]{->scalar } /

    // And fails monotonicity for the last row.
    int a2 = BitsFun.new_fidx();
    int a3 = BitsFun.new_fidx();
    BitsFun b2  = BitsFun.make0(a2);
    BitsFun b3  = BitsFun.make0(a3);
    BitsFun b23 = BitsFun.make0(a2,a3);
    Type       x0 = Type.XSCALAR;
    TypeFunPtr x1 = make(b2 ,x0);
    TypeFunPtr x2 = make(b23,x1);
    Type       x3 = Type. SCALAR;

    assertTrue(x0.isa(x1));
    assertTrue(x1.isa(x2));
    assertTrue(x2.isa(x3));

    // Wrapping:
    TypeFunPtr wx0 = make(b2,x0);
    TypeFunPtr wx1 = make(b2,x1);
    TypeFunPtr wx2 = make(b2,x2);
    TypeFunPtr wx3 = make(b2,x3);

    assertTrue(wx0.isa(wx1));
    assertTrue(wx1.isa(wx2));
    assertTrue(wx2.isa(wx3));  // CHECK MONOTONIC
  }
  static TypeFunPtr make( BitsFun fidxs, Type ret) { return TypeFunPtr.makex(fidxs,1,TypeMemPtr.NO_DISP,ret); }

  @Test public void testBits0() {

    // This looks like a crossing-nil bug, but it is not quite.
    // What is "nil join *[4]->str"?
    // Inverting, what is "nil meet *[~4]->str"?
    // The issue is that 'nil' says nothing about what to do with the '->str'
    // part of the structural meet breakdown.  See testLattice14 & 15.
    //
    // Tested as Lattice: [0]-> obj  ==>  NIL  ==>  [~0]->~obj
    //
    // If NIL is 'signed', and effectively either '[0]->obj' or '[~0]->~obj'
    // then this test works.  Either [0]->obj:
    //   If "[0]-> obj is [0,2]->rec" Then A^C isa B^C.  Fails, !A->B
    //   If "[0]->~obj is [0,2]->rec" Then A^C isa B^C.  Works:
    //       [0  ]->~obj ^ [4]->str => [~0+4]->~obj
    //       [0,2]-> rec ^ [4]->str => [~0+4]->~obj
    //
    // nil.isa(*rec?) so nil.join(*str) isa (*rec?).join(*str)
    Type t0 = Type.NIL;          // [0  ] -> obj
    Type t1 = TypeMemPtr.ISUSED0;// [0,2] -> rec
    assertTrue(t0.isa(t1));      // [0,2] -> obj -- meet is not t1
  }

  // Want Bits to support meet/join of fidxs for Unresolved:
  //     4.join.5.join.6 == {+4+5+6}
  //     4.meet.5.meet.6 == { 4&5&6}
  // Need to support 'splitting' bits for inlining, so all these bits are
  // *classes* not *constants.  Hence there is no '4' bit, only '+4' and '&4'.
  // Need the basic invariants: complete, distributed, commutative, associative.
  @Test public void testBits() {
    // 1 - obj
    //   2 - tuples & structs
    //   3 - arrays
    //     4 - strings
    //       5 - "abc"

    // Distributivity
    // t0 = *[5] -> "abc"
    // t1 = *[4] -> str
    // t2 = *[2] -> ()
    // Since t0.isa(t1) then   t0.join(t2) .isa(   t1.join(t2) )

    int alias0 = BitsAlias.ALLX;
    int alias1 = BitsAlias.new_alias(alias0);
    int alias2 = BitsAlias.new_alias(alias1);

    TypeMemPtr t0 = TypeMemPtr.make(alias2,TypeStruct.NAMEPT);
    TypeMemPtr t1 = TypeMemPtr.make(alias1,TypeStruct.POINT );
    TypeMemPtr t2 = TypeMemPtr.make(alias0,TypeStruct.ISUSED);
    assertTrue(t0.isa(t1));
    Type t02,t12,mt;

    t02 = t0.join(t2);          // join of unrelated bits2&5 []
    t12 = t1.join(t2);          // join of unrelated bits2&4 []
    mt  = t02.meet(t12);
    assertEquals(t12,mt);
    // also: (t0.meet(t1)).join(t2) == mt
    // but since t0 isa t1,
    // also:  t1.join(t2) ==  mt
    //       [4] join [2] ==> [~2 + ~4]

    t1 = TypeMemPtr.make_nil(alias1,TypeStruct.POINT);  // Same with nil
    t02 = t0.join(t2);        // join of unrelated bits2&5 []
    t12 = t1.join(t2);        // join of unrelated bits2&4 []
    mt  = t02.meet(t12);
    assertEquals(t12,mt);
  }

  @Test public void testNamesInts() {

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
    Type ni8 = TypeInt.INT8.set_name("__test_enum:");
    Type xni8= ni8.dual();      // dual name:int8
    Type no  = o.set_name("__test_enum:");
    Type nz  = z.set_name("__test_enum:");
    assertEquals(no ,no .meet(xni8)); // N:~i8 -> N: 1
    assertEquals(ni8,ni8.meet(no  )); // N:  1 -> N:i8
    assertEquals(nz ,nz .meet(xni8)); // N:~i8 -> N:0
    assertEquals(ni8,ni8.meet(nz  )); //   N:0 -> N:i8
    assertEquals(no ,no .meet(xni8)); // n:1 & n:~i8 -> mixing 0 and 1

    // Crossing lattice between named and unnamed ints
    //      Confirm lattice: {~i8 -> N:~i8 -> 0 -> N:i8 -> i8; N:0 -> 0 }
    // NOT: Confirm lattice: {N:~i8 -> ~i8; N:i8 -> i8 }
    assertEquals(xni8,xni8.meet( xi8));//   ~i8 -> N:~i8
    assertEquals(   z, z  .meet(xni8));// N:~i8 -> {0,1}??? When falling off from a Named Int, must fall below ANY constant to keep a true lattice
    assertEquals(  i8, ni8.meet(   z));//     0 -> N:i8
    assertEquals(  i8,  i8.meet( ni8));// N: i8 ->   i8
    assertEquals(   z,   z.meet(  nz));// N:  0 ->    0

    assertEquals(xni8,xi8.meet(xni8)); // N:~i8 <- ~i8
    assertEquals(o, o .meet(xni8)); // 1 & N:~i8
  }

  // Memory is on a different line than pointers.
  // Memory canNOT be nil, but ptrs to memory can be nil.
  // Memory contents can be any/all, vs ptrs being any/all.
  // A any-ptr-alias#6 means *any* of the alias#6 choices; same for all.
  // all ->  mem  -> { str,tup} -> { string constants, tuple constants} -> {~str,~tup} -> ~mem    -> any
  // all -> *mem? -> {*mem,nil} -> {*str,*tup,nil} -> {~*str,~*tup,nil} -> {~*mem,nil} -> ~*mem+? -> any
  @Test public void testOOPsNulls() {
    Type bot = Type      .ALL;

    Type mem = TypeMem   .ALLMEM; // All memory
    Type str = TypeStruct.POINT;  // All Strings
    Type tup = TypeStruct.ISUSED; // All Structs

    Type abc = TypeStruct.NAMEPT; // String constant
    Type zer = TypeInt  .FALSE;
    Type tp0 = TypeStruct.make_test(zer);  // tuple of a '0'

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
    int alias0 = BitsAlias.ALLX;
    int alias1 = BitsAlias.new_alias(alias0); // For STR
    int alias2 = BitsAlias.new_alias(alias1); // For ABC
    Type pmem0= TypeMemPtr.ISUSED0;    // *[ALL]?
    Type pmem = TypeMemPtr.ISUSED ;    // *[ALL]

    Type pstr0 = TypeMemPtr.make_nil(alias1,TypeStruct.POINT ); // STRPTR
    TypeMemPtr pstr = TypeMemPtr.make(alias1,TypeStruct.POINT ); // *[str]
    Type ptup0= TypeMemPtr.ISUSED0; // *[tup]?
    Type ptup = TypeMemPtr.ISUSED;  // *[tup]

    TypeMemPtr pabc0= TypeMemPtr.make_nil(alias2,TypeStruct.NAMEPT); // *["abc"]?
    TypeMemPtr pabc = TypeMemPtr.make    (alias2,TypeStruct.NAMEPT); // *["abc"]?
    TypeMemPtr pzer = TypeMemPtr.make(BitsAlias.new_alias(BitsAlias.ALLX),TypeStruct.ISUSED);// *[(0)]
    TypeMemPtr pzer0= TypeMemPtr.make(pzer._aliases.meet_nil(),TypeStruct.ISUSED);  // *[(0)]?
    Type nil  = Type.NIL, xnil=Type.XNIL;

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

    TypeStruct[] tos = new TypeStruct[alias2+1];
    tos[alias0] = TypeStruct.ISUSED;
    tos[alias1] = TypeStruct.POINT;
    tos[alias2] = TypeStruct.NAMEPT;
    TypeMem MEM = TypeMem.make0(tos);
    TypeMem ABC = TypeMem.make(alias2,TypeStruct.NAMEPT.dual());

    // "~str?" or "*[~0+4+]~str?" includes a nil, but nothing can fall to a nil
    // (breaks lattice)... instead they fall to their appropriate nil-type.
    assertEquals(Type.XNIL,xstr0.meet( xnil ));

    // This is a choice ptr-to-alias#1, vs a nil-able ptr-to-alias#2.  Since
    // they are from different alias classes, they are NEVER equal (unless both
    // nil).  We cannot tell what they point-to, so we do not know if the
    // memory pointed-at is compatible or not.
    assertTrue (xstr0.isa(pabc0)); // ~*[1]+0 vs ~*[2]?
    assertTrue (xstr .isa(pabc ));
    // We can instead assert that values loaded are compatible:
    assertTrue (MEM.dual().ld(xstr).isa(ABC.ld(pabc)));

    // "~@{}?" or "*[~0+2+]~@{}?" includes a nil, but nothing can fall to a nil
    // (breaks lattice)... instead they fall to their appropriate nil-type.
    assertEquals(Type.XNIL,xtup0.meet( xnil ));
    assertTrue (xtup0.isa(pzer0));
    assertTrue (xtup .isa(pzer ));
    //assertTrue(TypeMem.MEM_TUP.dual().ld(xstr).isa(TypeMem.MEM_ZER.ld(pabc)));

    assertTrue(nil .isa(pabc0)); // nil expands as [0]->obj so !isa [2]->"abc"
    assertTrue(nil .isa(pstr0)); // nil expands as [0]->obj so !isa [4]->str
    assertTrue(nil .isa(ptup0)); // nil expands as [0]->obj so !isa [2]->()
    assertTrue(nil .isa(pzer0)); // nil expands as [0]->obj so !isa [2]->@{}

    assertTrue (pabc0.isa(pstr0));
    assertTrue (pabc .isa(pstr ));
    assertTrue (ABC.ld(pabc).isa(MEM.ld(pstr)));
    assertTrue (pzer0.isa(ptup0));
    assertTrue (pzer .isa(ptup ));
    assertTrue (ptup0.isa(pmem0));
    assertTrue (ptup .isa(pmem ));

    assertTrue (pmem .isa(pmem0));
    assertTrue (pmem0.isa( bot ));


    // Crossing ints and *[ALL]+null
    Type  i8 = TypeInt.INT8;
    Type xi8 = i8.dual();
    assertEquals( Type.XNIL, xi8.meet(xmem0)); // ~OOP+0 & ~i8 -> 0
  }

  // Old model: fields are ordered, and are MEETd in order.  If fields at the
  // same index have different names, the names are MEET with a lattice.  If
  // one struct has more fields than the other, the extras are included or not
  // according if the other struct is up or down.  Tuple field names are NOT
  // interesting, and only the order is used.  Meeting tuples and structs uses
  // field orders, and will wipe out the field names and ends up as a tuple.

  // New model: fields are UNordered, and are MEETd by matching name.  If
  // fields have no match, they are included (or not) according to if the other
  // struct is up or down.  Tuple field names are interesting and are digits
  // according to the field order.  Meeting tuples and structs uses field
  // names, and will commonly have no names in common.
  @Test public void testStructTuple() {
    // meet @{c:0}? and @{c:@{x:1}?,}
    int alias0 = BitsAlias.new_alias(BitsAlias.ALLX);
    int alias1 = BitsAlias.new_alias(alias0);
    int alias2 = BitsAlias.new_alias(BitsAlias.ALLX);
    int alias3 = BitsAlias.new_alias(alias0);
    TypeStruct a1 = TypeStruct.make_test("c",Type.NIL, TypeFld.Access.Final); // @{c:nil}
    TypeStruct a3 = TypeStruct.make_test("x",TypeInt.TRUE, TypeFld.Access.Final); // @{x: 1 }
    TypeStruct a2 = TypeStruct.make_test("c",TypeMemPtr.make_nil(alias3,a3), TypeFld.Access.Final); // @{c:*{3#}?}
    Ary<TypeStruct> tos = new Ary<>(TypeStruct.class);
    tos.setX(BitsAlias.ALLX,TypeStruct.ISUSED);
    tos.setX(alias1,a1);
    tos.setX(alias2,a2);
    tos.setX(alias3,a3);
    TypeMem mem = TypeMem.make0(tos.asAry()); // [7:@{c==nil},8:{c=*[0,9]},9:@{x==1}]
    // *[1]? join *[2] ==> *[1+2]?
    // {~0+7+8} -> @{ c== [~0] -> @{x==1}} // Retain precision after nil
    Type ptr12 = Type.XNIL.join(TypeMemPtr.make(-alias1,a1.dual())).join( TypeMemPtr.make(-alias2,a2.dual()));
    // mem.ld(*[1+2]?) ==> @{c:0}
    // Currently retaining precision after nil: [~0] -> @{ x==1}
    Type ld = mem.ld((TypeMemPtr)ptr12);
    TypeStruct ax = TypeStruct.make(TypeFld.make("c",Type.NIL)); // @{c:nil}
    assertTrue(ld.isa(ax));
  }


  @Test public void testFunction() {
    PrimNode[] ignore2 = PrimNode.PRIMS(); // Force node

    TypeFunPtr gf = TypeFunPtr.GENERIC_FUNPTR;
    // New functions fall squarely between +/- GENERIC_FUNPTR.

    // TypeTuple structure demands the shortest Tuple wins the "length
    // war" (determines the length of the result based on short's any/all flag).
    TypeFunPtr f1i2i = TypeFunPtr.make_new_fidx(BitsFun.ALLX,2,NO_DISP,TypeInt.INT64);
    // To be a GF result, GF has to be shorter and high; the isa does a meet of
    // TypeFunPtrs which does a *join* of args, which duals the GF args down
    // low.  GF is zero length and low, and wins the meet.
    assertTrue(f1i2i.isa(gf));        // To be long  result, short must be high
    // To have GF.dual() be anything else and short, GF.dual must be high and
    // thus the result is a copy of F1I2I.
    //assertTrue(gf.dual().isa(f1i2i)); // To be short result, short must be low

    assertTrue(f1i2i.isa(gf));
    TypeFunPtr f1f2f = TypeFunPtr.make_new_fidx(BitsFun.ALLX,2,NO_DISP,TypeFlt.FLT64);
    assertTrue(f1f2f.isa(gf));
    TypeFunPtr mt = (TypeFunPtr)f1i2i.meet(f1f2f);
    int fidx0 = f1i2i.fidx();
    int fidx1 = f1f2f.fidx();
    BitsFun funs = BitsFun.make0(fidx0).meet(BitsFun.make0(fidx1));
    TypeFunPtr f3i2r = TypeFunPtr.make(funs,2,NO_DISP,Type.SCALAR);
    assertEquals(f3i2r,mt);
    assertTrue(f3i2r.isa(gf));
    assertTrue(f1i2i.isa(f3i2r));
    assertTrue(f1f2f.isa(f3i2r));

    TypeFunPtr f2 = TypeFunPtr.make(BitsFun.make0(fidx1),2,NO_DISP,TypeInt.INT64); // Some generic function (happens to be #23, '&')
    assertTrue(f2.isa(gf));
  }

  // Test limits on recursive type structures; recursively building nested
  // structures caps out in the type system at some reasonable limit.
  @Test public void testRecursive() {
    Object dummy0 = TypeMemPtr.DISPLAY_PTR; // Must <clinit> out of RECURSIVE_MEET
    final int alias1 = BitsAlias.new_alias(BitsAlias.ALLX);

    // Anonymous recursive structs -
    // - struct with pointer to self
    TypeFld fldv = TypeFld.make("v",TypeInt.INT64);
    Type.RECURSIVE_MEET++;
    TypeFld fldn0 = TypeFld.malloc("n");
    TypeStruct ts0 = TypeStruct.malloc_test(fldn0,fldv);
    final TypeMemPtr ts0ptr = TypeMemPtr.make(alias1,ts0);
    fldn0.setX(ts0ptr);
    Type.RECURSIVE_MEET--;
    ts0 = Cyclic.install(ts0);
    TypeMem ts0mem = TypeMem.make(alias1,ts0); // {1:@{n:*[1],v:int} }

    // - struct with pointer to self or nil
    Type.RECURSIVE_MEET++;
    TypeFld fldn1 = TypeFld.malloc("n");
    TypeStruct ts1 = TypeStruct.malloc_test(fldn1,fldv);
    final TypeMemPtr ts1ptr0 = TypeMemPtr.make_nil(alias1,ts1);
    fldn1.setX(ts1ptr0);
    Type.RECURSIVE_MEET--;
    ts1 = Cyclic.install(ts1);
    TypeMem ts1mem = TypeMem.make(alias1,ts1); // {1:@{n:*[1],v:int} }

    Type tsmt = ts0.meet(ts1);
    assertEquals(ts1,tsmt);
    Type tsmemmt = ts0mem.meet(ts1mem);
    assertEquals(ts1mem,tsmemmt);

    // Cyclic named struct: Memory#2 :A:@{n:*[0,2],v:int}
    // If we unrolled this (and used S for Struct and 0 for Nil) we'd get:
    // AS0AS0AS0AS0AS0AS0...
    final int alias2 = BitsAlias.new_alias(BitsAlias.ALLX);
    TypeMemPtr tptr2= TypeMemPtr.make_nil(alias2,TypeStruct.ISUSED); // *[0,2]
    TypeStruct ts2 = TypeStruct.make(TypeFld.make("n",tptr2),fldv); // @{n:*[0,2],v:int}
    TypeStruct ta2 = ts2.set_name("A:");

    // Peel A once without the nil: Memory#3: A:@{n:*[2],v:int}
    // ASAS0AS0AS0AS0AS0AS0...
    final int alias3 = BitsAlias.new_alias(BitsAlias.ALLX);
    TypeMemPtr tptr3= TypeMemPtr.make(alias3,TypeStruct.ISUSED); // *[3]
    TypeStruct ts3 = TypeStruct.make(TypeFld.make("n",tptr2),fldv); // @{n:*[0,2],v:int}
    TypeStruct ta3 = ts3.set_name("A:");

    // Peel A twice without the nil: Memory#4: A:@{n:*[3],v:int}
    // ASASAS0AS0AS0AS0AS0AS0...
    final int alias4 = BitsAlias.new_alias(BitsAlias.ALLX);
    TypeStruct ts4 = TypeStruct.make(TypeFld.make("n",tptr3),fldv); // @{n:*[3],v:int}
    TypeStruct ta4 = ts4.set_name("A:");

    // Then make a MemPtr{3,4}, and ld - should be a PeelOnce
    // Starting with the Struct not the A we get:
    // Once:  SAS0AS0AS0AS0AS0AS0...
    // Twice: SAS AS0AS0AS0AS0AS0...
    // Meet:  SAS0AS0AS0AS0AS0AS0...
    // which is the Once yet again
    TypeStruct[] tos = new TypeStruct[alias4+1];
    tos[1]=TypeStruct.UNUSED;
    tos[alias2]=ta2;
    tos[alias3]=ta3;
    tos[alias4]=ta4;
    TypeMem mem234 = TypeMem.make0(tos);
    TypeMemPtr ptr34 = (TypeMemPtr)TypeMemPtr.make(alias3,TypeStruct.ISUSED).meet(TypeMemPtr.make(alias4,TypeStruct.ISUSED));

    // Since hacking ptrs about from mem values, no cycles so instead...
    Type mta = mem234.ld(ptr34);
    //assertEquals(ta3,mta);
    TypeMemPtr ptr023 = (TypeMemPtr)TypeMemPtr.make_nil(alias2,TypeStruct.ISUSED).meet(TypeMemPtr.make(alias3,TypeStruct.ISUSED));
    TypeStruct xts = TypeStruct.make(TypeFld.make("n",ptr023),fldv);
    Type xta = xts.set_name("A:");
    assertEquals(xta,mta);

    // Mismatched Names in a cycle; force a new cyclic type to appear
    final int alias5 = BitsAlias.new_alias(BitsAlias.ALLX);
    TypeStruct tsnb = TypeStruct.make(TypeFld.make("n",TypeMemPtr.make_nil(alias5,TypeStruct.ISUSED)),TypeFld.make("v",TypeFlt.FLT64));
    TypeStruct tfb = tsnb.set_name("B:");
    Type mtab = ta2.meet(tfb);

    // TODO: Needs a way to easily test simple recursive types
    TypeStruct mtab0 = (TypeStruct)mtab;
    assertEquals("n",mtab0.get("n")._fld);
    assertEquals("v",mtab0.get("v")._fld);
    TypeMemPtr mtab1 = (TypeMemPtr)mtab0.at("n");
    assertTrue(mtab1._aliases.test(alias2)&& mtab1._aliases.test(alias5));
    assertEquals(Type.SCALAR,mtab0.at("v"));

    // In the ptr/mem model, all Objs from the same NewNode are immediately
    // approximated by a single Alias#.  This stops any looping type growth.
    // The only way to get precision back is to inline the NewNode and get new
    // Alias#s.

    // Nest a linked-list style tuple 10 deep; verify actual depth is capped at
    // less than 5.  Any data loop must contain a Phi; if structures are
    // nesting infinitely deep, then it must contain a NewNode also.
    int alias = BitsAlias.new_alias(BitsAlias.ALLX);
    TypeStruct ts = TypeStruct.make(TypeFld.make("ptr",Type.NIL),TypeFld.make("cnt",TypeInt.con(0)));
    TypeMemPtr phi = TypeMemPtr.make(alias,ts);
    for( int i=1; i<20; i++ ) {
      TypeStruct newt = TypeStruct.make(TypeFld.make("ptr",phi),TypeFld.make("cnt",TypeInt.con(i)));
      TypeStruct approx = newt.approx(BitsAlias.make0(alias));
      phi = TypeMemPtr.make(alias,approx);
    }
    HashMap<Type,Integer> ds = phi.depth();
    int d = phi.max(ds);
    assertTrue(0 <= d && d <10);
  }

  // Test a cycle with two names on mismatched cycle boundaries
  @Test public void testNameCycle() {
    Object dummy0 = TypeMemPtr.DISPLAY_PTR; // Must <clinit> out of RECURSIVE_MEET
    // Make a cycle: 0_A: -> 1_(n=*,v=i64) -> 2_TMP -> 3_B: -> 4_(n=*,v=f64) -> 5_TMP ->
    // Dual; then meet ~4_() and ~0_A
    final int alias = BitsAlias.ALLX;

    TypeFld fldvi = TypeFld.make("v",TypeInt.INT64);
    TypeFld fldvf = TypeFld.make("v",TypeFlt.FLT64);
    Type.RECURSIVE_MEET++;
    TypeFld fldn1 = TypeFld.malloc("n");
    TypeFld fldn4 = TypeFld.malloc("n");
    TypeStruct as1 = TypeStruct.malloc_test("A:",fldn1,fldvi);
    TypeStruct bs4 = TypeStruct.malloc_test("B:",fldn4,fldvf);
    TypeMemPtr ap5 = TypeMemPtr.make(alias,as1);
    TypeMemPtr bp2 = TypeMemPtr.make(alias,bs4);
    fldn1.setX(bp2);
    fldn4.setX(ap5);
    Type.RECURSIVE_MEET--;
    as1 = Cyclic.install(as1);
    bp2 = (TypeMemPtr)as1.at("n");
    bs4 =             bp2._obj;
    ap5 = (TypeMemPtr)bs4.at("n");

    Type das1 = as1.dual();     // ~A:@{b,int}
    Type dbs4 = bs4.dual();     // ~B:@{a,flt}
    // Since names mismatch, but both as1 and bs4 are high... must fall hard.
    Type mt = das1.meet(dbs4);  // ~ ~@{a join b, int join flt} ==> @{a join b, int32}
    TypeStruct smt = (TypeStruct)mt;
    assertEquals(TypeInt.INT32,smt.at("v"));
    TypeMemPtr smp = (TypeMemPtr)smt.at("n");
    assertEquals(smt,smp._obj);
    assertEquals(BitsAlias.NALL,smp._aliases);

    Type mx = as1.dual().meet(dbs4);
    assertEquals(smt,mx);
  }

  @Test public void testLoad() {
    Object dummy0 = TypeStruct.TYPES;
    int alias0 = BitsAlias.ALLX;
    int alias1 = BitsAlias.new_alias(alias0);
    int alias2 = BitsAlias.new_alias(alias1);
    TypeMemPtr t2 = TypeMemPtr.make(alias2,TypeStruct.NAMEPT); // ABCPTR
    TypeMemPtr t1 = TypeMemPtr.make(alias1,TypeStruct.POINT ); // STRPTR
    TypeMemPtr t0 = TypeMemPtr.make(alias0,TypeStruct.ISUSED);
    // All are ISA
    TypeMemPtr[] tmps = new TypeMemPtr[]{
      t1.dual(),
      t2,
      t1,
    };
    TypeMemPtr[] tmps1 = new TypeMemPtr[]{
      TypeMemPtr.make(-alias1,TypeStruct.UNUSED),
      TypeMemPtr.make(-alias2,TypeStruct.UNUSED),
      TypeMemPtr.make( alias2,TypeStruct.ISUSED), // testing 5-obj & ISUSED [1....:use] vs MEM_ABC
      TypeMemPtr.make( alias1,TypeStruct.ISUSED),
    };
    for( int i=0; i<tmps.length-1; i++ )
      assertTrue(tmps[i].isa(tmps[i+1]));

    // All are ISA
    TypeStruct[] tos = new TypeStruct[alias2+1];
    tos[alias0] = TypeStruct.ISUSED;
    tos[alias1] = TypeStruct.POINT;
    tos[alias2] = TypeStruct.NAMEPT;
    TypeMem mem = TypeMem.make0(tos);
    TypeMem abc = TypeMem.make(alias2,TypeStruct.NAMEPT.dual());
    TypeMem[] tmems = new TypeMem[]{
      TypeMem.ANYMEM,             // [1:~obj,3:~obj,5:~obj ]
      abc,                        // [1:~obj,3:~obj,5:"abc"]
      mem.dual(),                 // [1:~obj,3:~str,5:"abc"]
      mem,                        // [1: obj,3: str,5:"abc"]
      abc.dual(),                 // [1: obj,3: obj,5:"abc"]
      TypeMem.ALLMEM,             // [1: obj,3: obj,5: obj ]
    };
    for( int j=0; j<tmems.length-1; j++ )
      assertTrue(tmems[j].isa(tmems[j+1]));

    TypeStruct[][] rez = new TypeStruct[tmps.length][tmems.length];
    for( int i=0; i<tmps.length; i++ )
      for( int j=0; j<tmems.length; j++ )
        rez[i][j] = tmems[j].ld(tmps[i]);

    for( int i0=0; i0<tmps.length; i0++ )
      for( int j0=0; j0<tmems.length; j0++ )
        for( int i1=i0; i1<tmps.length; i1++ )
          for( int j1=j0; j1<tmems.length; j1++ )
            assertTrue( rez[i0][j0].isa(rez[i1][j1]) );
  }

  // Validate crush is monotonic
  @Test public void testCrush() {
    TypeStruct[] objs = new TypeStruct[]{
      TypeStruct.ISUSED,
      TypeStruct.INT64_INT64,
      TypeStruct.NAMEPT,
      TypeStruct.POINT,
      TypeMemPtr.DISPLAY,
      TypeStruct.A,
      TypeStruct.ARW,
    };

    for( int i=0; i<objs.length; i++ ) {
      TypeStruct toi = objs[i];
      for( int j=i; j<objs.length; j++ ) {
        TypeStruct toj = objs[j];
        testCrush0(toi       ,toj       );
        testCrush0(toi.dual(),toj       );
        testCrush0(toi       ,toj.dual());
        testCrush0(toi.dual(),toj.dual());
      }
    }
  }

  private void testCrush0( TypeStruct ti, TypeStruct tj ) {
    if( ti.isa(tj) ) {
      TypeStruct tic = ti.crush();
      TypeStruct tjc = tj.crush();
      assertTrue(tic.isa(tjc));
    }
  }


  @Test public void testCommuteSymmetricAssociative() {
    assertTrue(Type.check_startup());
  }

}
