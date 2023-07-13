package com.cliffc.aa;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.Util;
import org.junit.Ignore;
import org.junit.Test;

import java.util.BitSet;

import static org.junit.Assert.*;

// The core Type system is a distributive, complete, bounded lattice.
// See: https://en.wikipedia.org/wiki/Lattice_(order)

// This is a series of tests to validate various structures as lattices with
// the right properties, or not.  A lot of "obvious" structures fail to be
// lattices, and that has led to a lot of failed attempts at type-inference via
// finding the stable meet over a "Sea of Nodes" graph.

// While some structures are lattices and some are not, we can envision graph
// combinators that preserve the right properties when mixing two lattices.
// Mixing a non-lattice & a lattice with a combinator generally keeps the
// non-lattice property.

// An example combinator is multiplying two lattices; if {A} and {B} are
// lattices then we can make a lattice by simple pairs of A & B elements:
// {(A,B)}.  This happens in lots of places, e.g. structure fields or mixing
// fidxs (code constants) and arguments to function pointers.
//
// If {A} is a lattice, and we clone A and rename all the elements as AA, then
// {AA} is a lattice (simple rename).  If we add edges from all the high
// elements of {A} to the high elements of {AA}, and low-{AA} to low-{A}, then
// again we have a lattice.  Notice the inside-out-edge ordering.  We can
// repeat this process to get a "chain" of lattices going however deep down the
// "AAAA...."  rabbit-hole we like.  The integers use this process for types
// int64,int32,int16,int8,int1.
//
// However! If we clone lattice {A} into two lattices {A0} and {A1}, each being
// a simple rename, and we add all the inside-out edges from {A} elements to
// the corresponding {A0} and separately to {A1} - the combination is NOT a
// lattice.  This implies, e.g. we cannot simply add "names" to a lattice and
// have the result be a lattice.
//
// Two make the simple-renamed-clones work, we can use a simple nested
// combinator: A_top >> AA_top >> AAA_top... and A_bot << AA_bot << AAA_bot but
// NO interior edges.  Basically we can "insert" a lattice "inside" another one
// via taking any two symmetric elements from the "outer" lattice as having
// edges to the top/bot of the inner lattice.  This implies that mixing
// elements from 2 different "inserted" lattices - even if they have a common
// parent insertion point - always must fall to the "bot" parent point.  There
// cannot be any interior crossing edges!  This is too weak for "names".
//
// NIL: Generally speaking we cannot have a common center constant suggestively
// called "nil" that is in the center of two multiplied lattices - this leads
// to the "crossing nil" bug referred to in the code.  We CAN inject the NIL in
// a few places - but using it typically requires losing all the structure of
// one of the two multiplied lattices.  We can "sign" a NIL and do a little
// better; the "~NIL" variant can keep structure in the "off-side" lattice.
// (and obviously for symmetry on "NIL" going "up" the lattice).

// ------------
// So here's a thought about "names": use the pair-wise (multiplicative)
// combinator, and a "name" is associated with a set of fields.  There is no
// "real" subtyping, but instead multiplicative addition of more named types
// and their matching fields - more like mixins than subtyping.
//
// Means there's names for ints & flts, like now.  And names for "chunks" of a
// struct, which could be flattened - rolling the "name" into the fields.
// E.g. java
//    class Point2D { int x,y; };  class Point3D extends Point 2D { int z; }
//
// Short hand Point2D:@{x;y} is syntactic sugar for: @{ Point2D:x; Point2D:y }
// Short hand Point3D:Point2D:@{z} is syntactic sugar for:
//      @{ Point2D:x; Point2D:y; Point3D:z; }



public class TestLattice {
  static class N {
    private static int ID=0;
    static Ary<N> NS=new Ary<>(new N[1],0);
    static void reset() { NS.clear(); ID=0; }
    final int _id;
    final String _t;
    final Ary<N> _subs;
    final Ary<N> _sups;
    final BitSet _reaches; // Who reaches this node, including self
    int _cnt;              // Reaches count
    N _dual;
    N(int id, String t, N... subs) {
      _id=id;
      _t=t;
      _subs = new Ary<>(subs);
      _sups = new Ary<>(new N[1],0); // Fill in later
      _reaches = new BitSet();
      _dual = this;
    }
    N(String t, N... subs) {
      this(ID++,t,subs);
      NS.add(this);
    }
    void set_dual( N d ) {
      assert _dual==this && d._dual==d;
      _dual=d; d._dual=this;
    }
    // Setup reverse edges for later walks
    void walk_set_sup( BitSet bs ) {
      if( bs.get(_id) ) return;
      bs.set(_id);
      for( N sub : _subs ) sub._sups.add(this);
      for( N sub : _subs ) sub.walk_set_sup(bs);
    }
    // top-down recursive print
    void walk_print( BitSet bs, int indent ) {
      if( bs.get(_id) ) return;
      bs.set(_id);
      System.out.println(new SB().i(indent) +toString());
      for( N sub : _subs ) sub.walk_print(bs,indent+1);
    }
    @Override public String toString() {
      SB sb = new SB().p(_t).p(" -> ");
      for( N sub : _subs ) sb.p(sub._t).p(" ");
      if( _dual!=this )
        sb.p(" // dual=").p(_dual._t);
      return sb.toString();
    }
    // top-down find extra edges
    boolean walk_min_edge( int[] vs, N sup ) {
      vs[_id]++;
      if( sup != null ) {
        for( int i=0; i<_sups._len; i++ ) {
          N sup0 = _sups.at(i);
          if( sup._reaches.get(sup0._id) ) {
            System.out.println("Edge " + sup0._t + " -> " + _t + " and also path " + sup0._t + " ... -> " + sup._t + " -> " + _t);
            //return false;
            _sups.del(i);
            sup0._subs.del(this);
            i--;
          }
        }
        _reaches.or(sup._reaches);
      }
      if( vs[_id]<_sups._len ) return true; // Pre-order still; return
      for( N sup0 : _sups ) _reaches.set(sup0._id); // Post-order: add all supers in
      for( N sub : _subs ) if( !sub.walk_min_edge(vs,this) ) return false;
      return true;
    }
    // Demand dual symmetry: A->B === ~B->~A
    boolean walk_dual(BitSet bs) {
      if( bs.get(_id) ) return true;
      bs.set(_id);
      boolean x=true;
      for( N sub : _subs ) {
        if( sub._dual._subs.find(_dual) == -1 ) {
          System.out.println(""+_t+" -> "+sub._t+"; expect "+sub._dual._t+" -> "+_dual._t);
          x = false;
        }
      }
      for( N sub : _subs ) if( !sub.walk_dual(bs) ) x=false;
      return x;
    }

    // Compute meet of this and that
    N meet(N b) {
      if( this==b ) return this;
      BitSet as =   _reaches;
      BitSet bs = b._reaches;
      forall_reaches:
      for( int x=as.nextSetBit(0); x>=0; x=as.nextSetBit(x+1) )
        if( bs.get(x) ) {
          N mt = N.NS.at(x);
          for( N sub : mt._subs )  // Common in both reaches sets
            if( as.get(sub._id) && bs.get(sub._id) )
              continue forall_reaches;
          return mt;  // Not inside both reaches, must be a meet
        }
      // Correct already
      throw com.cliffc.aa.AA.unimpl();
    }
    N join(N b) {
      return _dual.meet(b._dual)._dual;
    }
  }

  // Complete the lattice and test it
  static void test(N top) {
    // Fill in the reverse edges
    top.walk_set_sup(new BitSet());
    // Pretty print
    top.walk_print(new BitSet(),0);

    // Find and barf redundant edges.  Computes reachable.
    assertTrue(top.walk_min_edge(new int[N.ID],null));
    for( int i=0; i<N.ID; i++ ) {
      N n = N.NS.at(i);
      n._reaches.set(i); // Add self to reaches
      n._cnt = n._reaches.cardinality();
    }

    // Demand dual symmetry: A->B === ~B->~A
    assertTrue(top.walk_dual(new BitSet()));

    // Check for single lowest unique meet.  BAD: For all nodes, compute Reach
    // (to Bot, and already done).  For each pair of nodes compute the
    // intersection of their reach sets; this is their common reachable set
    // just following graph edges.  The LCA will be a node with a Reach set
    // equal to the intersection; it may not exist.  If it does not, the set of
    // nodes with the largest Reach sets make a good error message.
    int errs=0;
    for( N a : N.NS )
      for( N b : N.NS ) if( a._id < b._id ) { // triangle efficiency
          BitSet as = a._reaches;
          BitSet bs = b._reaches;
          N meet = null;
          forall_reaches:
          for( int x=as.nextSetBit(0); x>=0; x=as.nextSetBit(x+1) ) {
            if( bs.get(x) ) {
              N c = N.NS.at(x); // Common in both reaches sets
              for( N sub : c._subs )
                if( as.get(sub._id) && bs.get(sub._id) )
                  continue forall_reaches; // node is inside both a & b reaches sets, so is not unique meet
              if( meet == null ) meet = c; // Found a unique meet point
              else {                       // Found a 2nd meet point... so not unique
                errs++;
                System.out.println("No meet found for "+a._t+" and "+b._t+", tied candidates are: "+meet._t+" and "+c._t);
                break;
              }
            }
          }
        }
    assertEquals("Found errors", 0, errs);
  }



  // Lattice!
  // This structure is tested to be a lattice:

  //      ~scalar
  //    ~num    ~oop+?
  //  ~int        { ~str+?,     ~tup+? }   -X-~oop-X-
  //                { ~str,           ~tup }
  //  42      0       { "abc", "def", @{x}, @{x,y} }
  //                {  str,            tup }
  //   int        { str?,        tup?  }   -X-oop-X-
  //     num    oop?
  //        scalar

  // Notice NO {oop,~oop} as this makes the non-lattice issue; join of
  // {oop,null} is not well-defined, as it tops out as either ~str+? OR ~tup+?
  // instead of being unique.  Similarly, meet of {~oop,null} is not well-
  // defined, and bottoms out as either {str?} OR {tup?}.
  @Test public void testLattice0() {
    N.reset();
    N scal= new N( "scalar");
    N num = new N("num" ,scal);
    N int8= new N("int8",num );

    N oop0= new N( "oop?",scal);
    N str0= new N( "str?",oop0);
    N tup0= new N( "tup?",oop0);
    N str = new N( "str" ,str0);
    N tup = new N( "tup" ,tup0);

    N nil = new N( "0",str0,tup0,int8);

    N abc = new N( "\"abc\"",str);
    N def = new N( "\"def\"",str);
    N flx = new N( "@{x}"   ,tup);
    N fly = new N( "@{y}"   ,tup);
    N strx= new N("~str" ,abc,def);
    N tupx= new N("~tup" ,flx,fly);
    N str_= new N("~str+0",strx,nil);
    N tup_= new N("~tup+0",tupx,nil);
    N oop_= new N("~oop+0",str_,tup_);

    N i3  = new N("42",int8 );
    N xint= new N("~int8",i3,nil );
    N xnum= new N("~num",xint);

    N xscl= new N( "~scalar",oop_,xnum);
    // Mark the non-centerline duals
    scal.set_dual(xscl);
    num .set_dual(xnum);
    int8.set_dual(xint);
    oop0.set_dual(oop_);
    str0.set_dual(str_);
    tup0.set_dual(tup_);
    str .set_dual(strx);
    tup .set_dual(tupx);

    test(xscl);
  }
  // intuition: top-tuple allows all field names; prefix field names on
  // top-struct allows more post-fix names.  After falling across center,
  // reverse: extra fields are dropped & shortened until no-names - which is a
  // tuple.  Same field names are sorted by field contents.  Field contents
  // fall independently.  No center-line notion (either have a field or not)
  // but may still be constant if the tuple is a constant.
  //       /----> ~[b]+? -\  /-> [b]? -------\  []?
  // ~[]+? -----> ~[x]+? -> 0 -> [x]? --------> []?
  //   \-> ~[] -> ~[x] --------> [x]  -> [] -/

  // Fails to be a valid lattice; same fail: MEET of 0 and ~[]+?  falls to
  // either [x]? or [b]? and "invents" fields as it falls.
  @Ignore @Test public void testLattice1() {
    N.reset();
    N  ta0 = new N("[]?"   );
    N  tx0 = new N("[x]?"  ,ta0);
    N  tb0 = new N("[b]?"  ,ta0);
    N  ty0 = new N("[x,y]?",tx0);
    N  ta  = new N("[]"    ,ta0);
    N  tx  = new N("[x]"   ,ta,tx0);
    N  tb  = new N("[b]"   ,ta,tb0);
    N  ty  = new N("[x,y]" ,tx,ty0);

    N nil  = new N("0", ty0,tb0 );

    N xty  = new N("~[x,y]",ty);
    N xtx  = new N("~[x]",xty);
    N xtb  = new N("~[b]",tb);
    N xta  = new N("~[]",xtx,xtb);

    N xty0= new N("~[x,y]+?",xty,nil);
    N xtx0= new N("~[x]+?",xtx,xty0);
    N xtb0= new N("~[b]+?",xtb,nil);
    N xta0= new N("~[]+?",xta,xtx0,xtb0);

    // Mark the non-centerline duals
    xta0.set_dual(ta0);
    xtx0.set_dual(tx0);
    xtb0.set_dual(tb0);
    xty0.set_dual(ty0);
    xta .set_dual(ta );
    xtx .set_dual(tx );
    xtb .set_dual(tb );
    xty .set_dual(ty );

    test(xta0);
  }

  // Lattice!
  // This structure is tested to be a lattice:

  // back to field-by-field for structs; each tuple/struct has a {choice-null,
  // not-null, support-null, is-null}.  Each field is Top, field, Bot,
  // replicated for all fields separately.  Also, the nil choice is available
  // for all combos; so there are lots of variations of nil.  There is a lowest
  // nil and a highest nil.  Struct nil is different from int 0, and seeing a 0
  // probably means producing a union{0[_,_]0,0:int}
  @Test public void testLattice2() {
    N.reset();
    N tb0 = new N("[_,_]0"  );
    N tx0 = new N("[x,_]0" ,tb0);
    N ty0 = new N("[y,_]0" ,tb0);
    N tt0 = new N("[^,_]0" ,tx0,ty0);

    N tb  = new N("[_,_]"  ,tb0 );
    N tx  = new N("[x,_]"  ,tb,tx0);
    N ty  = new N("[y,_]"  ,tb,ty0);
    N tt  = new N("[^,_]"  ,tx,ty,tt0);

    N bb0 = new N("[_,^]0" ,tb0);
    N bx0 = new N("[x,^]0" ,bb0,tx0);
    N by0 = new N("[y,^]0" ,bb0,ty0);
    N bt0 = new N("[^,^]0" ,bx0,by0,tt0);

    // The 8 different flavors of nil...
    N nilbb = new N("0[_,_]0",tb0);
    N nilxb = new N("0[x,_]0",tx0);
    N nilyb = new N("0[y,_]0",ty0);
    N niltb = new N("0[^,_]0",tt0);
    N nilbt = new N("0[_,^]0",bb0);
    N nilxt = new N("0[x,^]0",bx0);
    N nilyt = new N("0[y,^]0",by0);
    N niltt = new N("0[^,^]0",bt0);
    // Attempt a single nil
    //N nil = new N("0",tb0,tx0,ty0,tt0,bb0,bx0,by0,bt0);
    //N nilbb=nil, nilxb=nil, nilyb=nil, niltb=nil, nilbt=nil, nilxt=nil, nilyt=nil, niltt=nil;

    N tbp = new N("[_,_]+" ,tb,nilbb);
    N txp = new N("[x,_]+" ,tbp,tx,nilxb);
    N typ = new N("[y,_]+" ,tbp,ty,nilyb);
    N ttp = new N("[^,_]+" ,txp,typ,tt,niltb);

    N bb  = new N("[_,^]"  ,tb, bb0 );
    N bx  = new N("[x,^]"  ,bb,bx0,tx);
    N by  = new N("[y,^]"  ,bb,by0,ty);
    N bt  = new N("[^,^]"  ,bx,by,bt0,tt);

    N bbp = new N("[_,^]+" ,bb,tbp,nilbt);
    N bxp = new N("[x,^]+" ,bbp,bx,txp,nilxt);
    N byp = new N("[y,^]+" ,bbp,by,typ,nilyt);
    N btp = new N("[^,^]+" ,bxp,byp,bt,ttp,niltt);

    // Mark the non-centerline duals
    btp.set_dual(tb0);
    byp.set_dual(ty0);
    bxp.set_dual(tx0);
    bbp.set_dual(tt0);

    bt .set_dual(tb );
    bx .set_dual(tx );
    by .set_dual(ty );
    bb .set_dual(tt );

    nilbb.set_dual(niltt);
    nilxb.set_dual(nilxt);
    nilyb.set_dual(nilyt);
    niltb.set_dual(nilbt);

    bb0.set_dual(ttp);
    bx0.set_dual(txp);
    by0.set_dual(typ);
    bt0.set_dual(tbp);

    test(btp);
  }


  // Lattice!
  // This structure is tested to be a lattice:

  //          ~num
  //    M:~num    N:~num
  //          ~int
  //  M:~int        N:~int
  //M:0  M:7  0  7    N:0  N:7
  //  M:int         N:int
  //           int
  //    M:num     N:num
  //           num
  @Test public void testLattice3() {
    N.reset();
    N num = new N(  "num" );
    N nnum= new N("N:num",num);
    N mnum= new N("M:num",num);
    N  i64= new N(  "int",num );
    N ni64= new N("N:int",i64,nnum );
    N mi64= new N("M:int",i64,mnum );

    N i0  = new N(  "0", i64);
    N i7  = new N(  "7", i64);
    N ni0 = new N("N:0", ni64);
    N ni7 = new N("N:7", ni64);
    N mi0 = new N("M:0", mi64);
    N mi7 = new N("M:7", mi64);

    N nx64= new N("N:~int",ni0,ni7 );
    N mx64= new N("M:~int",mi0,mi7 );
    N  x64= new N(  "~int",nx64,mx64, i0, i7 );
    N nxum= new N("N:~num",nx64 );
    N mxum= new N("M:~num",mx64 );
    N  xum= new N(  "~num",nxum,mxum,x64 );

    // Mark the non-centerline duals
     num.set_dual( xum);
    nnum.set_dual(nxum);
    mnum.set_dual(mxum);
     i64.set_dual( x64);
    ni64.set_dual(nx64);
    mi64.set_dual(mx64);

    test(xum);
  }

  // Not a lattice:  has str? and "abc"? and "def"?
  //
  //         ~scalar
  //   ~num           ~oop+?
  //             ~str+?
  //      ~str   "abc"+?  "def"+?
  //    "abc"  nil     "def"
  //       str   "abc"?  "def"?
  //              str?
  //    num           oop?
  //         scalar


  // Lattice!
  // This structure is tested to be a lattice:
  // BUT: adding "def"? makes it NOT a lattice!

  //         ~scalar
  //   ~num           ~oop+?
  //             ~str+?  ~{~int64}+?
  //                  ~{~int64}  ~{~int8}+?
  //                         ~{~int8}
  //      ~str   "abc"+?            {nil}+?
  // nil     "abc"     nil     {nil}  {7}   <<-- {nil} is a constant tuple
  //       str   "abc"?             {nil}?  <<-- Least tuple AND nil
  //                          { int8}
  //                 { int64}   { int8}?
  //              str?   { int64}?
  //    num           oop?
  //         scalar
  @Test public void testLattice4() {
    N.reset();
    N scal= new N("scalar");
    N num  =new N("num"     ,scal);
    N oop0= new N("oop?"    ,scal);
    N str0= new N("str?"    ,oop0);
    N i640= new N("{i64}?"  ,oop0);
    N i64 = new N("{i64}"   ,i640);
    N i80 = new N("{i8}?"   ,i640);
    N i8  = new N("{i8}"    ,i80,i64);
    N str = new N("str"     ,str0);
    N abc0= new N("abc?"    ,str0);
    N t00 = new N("{nil}?"  ,i80);
    N abc = new N("abc"     ,abc0,str);
    N t7  = new N("{7}"     ,i8);
    N t0  = new N("{nil}"   ,i8,t00);
    N nil = new N("nil"     ,t00,abc0,num);
    N abc_= new N("abc+?"   ,abc,nil);
    N t0_ = new N("{nil}+?" ,nil,t0);
    N xstr= new N("~str"    ,abc);
    N xi8 = new N("~{~i8}"  ,t0,t7);
    N xi8_= new N("~{~i8}+?",xi8,t0_);
    N xstr_=new N("~str+?"  ,xstr,abc_);
    N xi64= new N("~{~i64}" ,xi8);
    N xi64_=new N("~{~i64}+?",xi64,xi8_);
    N oop_ =new N("~oop+?"  ,xi64_,xstr_);
    N xnum =new N("~num"    ,nil);
    N xscal=new N("~scalar" ,oop_,xnum);

    // Mark the non-centerline duals
    scal.set_dual(xscal);
    num .set_dual(xnum );
    oop0.set_dual( oop_);
    str0.set_dual(xstr_);
    i640.set_dual(xi64_);
    i64 .set_dual(xi64 );
    str .set_dual(xstr );
    i80 .set_dual(xi8_ );
    i8  .set_dual(xi8  );
    t00 .set_dual(t0_  );
    abc0.set_dual(abc_ );

    test(xscal);
  }

  // Lattice!
  // This structure is tested to be a lattice:
  // BUT does not support "or-null" on complex tuples

  //         ~scalar
  //   ~num           ~oop+?
  //           ~str+?   ~{~int64}
  //         ~str          ~{~int8}
  // nil  "abc" "def"     {nil}  {7}   <<-- {nil} is a constant tuple
  //          str           { int8}
  //            str?     { int64}
  //    num           oop?
  //         scalar
  @Test public void testLattice5() {
    N.reset();
    N scal= new N("scalar");
    N num  =new N("num"     ,scal);
    N oop0= new N("oop?"    ,scal);
    N str0= new N("str?"    ,oop0);
    N i64 = new N("{i64}"   ,oop0); // tuple with a single int field

    N i8  = new N("{i8}"    ,i64);
    N str = new N("str"     ,str0);
    N abc = new N("abc"     ,str);
    N def = new N("def"     ,str);
    N t7  = new N("{7}"     ,i8);
    N t0  = new N("{nil}"   ,i8);       // two different flavors of nil
    N nil = new N("nil"     ,str0,num); // two different flavors of nil
    N xstr= new N("~str"    ,abc,def);
    N xi8 = new N("~{~i8}"  ,t0,t7);

    N xstr_=new N("~str+?"  ,xstr,nil);
    N xi64= new N("~{~i64}" ,xi8);
    N oop_ =new N("~oop+?"  ,xi64,xstr_);
    N xnum =new N("~num"    ,nil);
    N xscal=new N("~scalar" ,oop_,xnum);

    // Mark the non-centerline duals
    scal.set_dual(xscal);
    num .set_dual(xnum );
    oop0.set_dual( oop_);
    str0.set_dual(xstr_);
    i64 .set_dual(xi64 );
    i8  .set_dual(xi8  );
    str .set_dual(xstr );

    test(xscal);
  }

  // Lattice!
  // This structure is tested to be a lattice:

  //         ~scalar
  //          ~i64         ~oop+?
  //   N:~i64        M:~i64
  //          ~i8
  //   N:~i8          M:~i8
  // N:7 N:0  7 nil  M:7 M:0   "abc"
  //   N:i8           M:i8
  //           i8
  //   N:i64          M:i64
  //           i64          oop?
  //          scalar
  @Test public void testLattice6() {
    N.reset();
    N scal= new N("scalar");
    N oop0= new N("oop?"    ,scal);
    N i64 = new N("i64"     ,scal);
    N n64 = new N("N:i64"   ,i64);
    N m64 = new N("M:i64"   ,i64);

    N i8  = new N("i8"      ,i64);
    N n8  = new N("N:i8"    ,n64,i8);
    N m8  = new N("M:i8"    ,m64,i8);

    N nil = new N("nil"     ,i8);
    N c7  = new N("7"       ,i8);
    N m0  = new N("M:0"     ,m8);
    N m7  = new N("M:7"     ,m8);
    N n0  = new N("N:0"     ,n8);
    N n7  = new N("N:7"     ,n8);
    N abc = new N("abc"     ,oop0);

    N xn8 = new N("N:~i8"   ,n0,n7);
    N xm8 = new N("M:~i8"   ,m0,m7);
    N xi8 = new N("~i8"     ,xn8,xm8,c7,nil);

    N xm64= new N("M:~i64"  ,xm8);
    N xn64= new N("N:~i64"  ,xn8);
    N xi64= new N("~i64"    ,xn64,xm64,xi8);
    N xoop= new N("~oop+?"  ,abc);

    N xscal=new N("~scalar" ,xoop,xi64);

    // Mark the non-centerline duals
    scal.set_dual(xscal);
    oop0.set_dual(xoop );
    i64 .set_dual(xi64 );
    n64 .set_dual(xn64 );
    m64 .set_dual(xm64 );
    i8  .set_dual(xi8  );
    n8  .set_dual(xn8  );
    m8  .set_dual(xm8  );

    test(xscal);
  }

  // Lattice!
  // This structure is tested to be a lattice:

  // Same as Lattice6 but includes a not-nil notion, and i8 becomes i1.
  // not-nil of ~i1 is not-nil-choice{0,1} is just {1}.  Notice not allowed to
  // have edges ~nzi64 -> N:~nzi64 or else we lose the lattice property.  This
  // implies we can only pick up named-numbers once: at the i64 outermost level.
  //
  //         ~scalar
  //           ~nzscalar
  //          ~i64         ~oop+?
  //            ~nzi64
  //   N:~i64        M:~i64
  //     N:~nzi64      M:~nzi64
  //          ~i1
  //   N:~i1          M:~i1
  // N:1 N:0  1 nil  M:1 M:0   "abc"
  //   N:i1           M:i1
  //           i1
  //     N:nzi64        M:nzi64
  //   N:i64          M:i64
  //             nzi64
  //           i64          oop?
  //           nzscalar
  //          scalar
  @Test public void testLattice6_1() {
    N.reset();
    N scal= new N("scalar");
    N nzscal= new N("nzscalar",scal);
    N oop0= new N("oop?"    ,scal);
    N i64 = new N("i64"     ,scal);
    N nzi64 = new N("nzi64"     ,i64,nzscal);
    N n64 = new N("N:i64"   ,i64);
    N m64 = new N("M:i64"   ,i64);
    N nzn64 = new N("N:nzi64"   ,n64);
    N nzm64 = new N("M:nzi64"   ,m64);

    N i1  = new N("i1"      ,i64);
    N n8  = new N("N:i1"    ,n64,i1);
    N m8  = new N("M:i1"    ,m64,i1);

    N nil = new N("nil"     ,i1);
    N c1  = new N("1"       ,i1,nzi64);
    N m0  = new N("M:0"     ,m8);
    N m1  = new N("M:1"     ,m8,nzm64);
    N n0  = new N("N:0"     ,n8);
    N n1  = new N("N:1"     ,n8,nzn64);
    N abc = new N("abc"     ,oop0);

    N xn8 = new N("N:~i1"   ,n0,n1);
    N xm8 = new N("M:~i1"   ,m0,m1);
    N xi1 = new N("~i1"     ,xn8,xm8,c1,nil);

    N xnzm64= new N("M:~nzi64"  ,m1);
    N xnzn64= new N("N:~nzi64"  ,n1);
    N xm64= new N("M:~i64"  ,xm8,xnzm64);
    N xn64= new N("N:~i64"  ,xn8,xnzn64);
    N xnzi64= new N("~nzi64"    ,c1);
    N xi64= new N("~i64"    ,xn64,xm64,xi1,xnzi64);
    N xoop= new N("~oop+?"  ,abc);

    N xnzscal=new N("~nzscalar" ,xnzi64);
    N xscal=new N("~scalar" ,xoop,xi64,xnzscal);

    // Mark the non-centerline duals
    scal.set_dual(xscal);
    nzscal.set_dual(xnzscal);
    oop0.set_dual(xoop );
    i64 .set_dual(xi64 );
    nzi64 .set_dual(xnzi64 );
    n64 .set_dual(xn64 );
    m64 .set_dual(xm64 );
    nzn64 .set_dual(xnzn64 );
    nzm64 .set_dual(xnzm64 );
    i1  .set_dual(xi1  );
    n8  .set_dual(xn8  );
    m8  .set_dual(xm8  );

    test(xscal);
  }

  // Not a Lattice: same problem as before: meet of ~oop and nil can turn into
  // any "struct?", and there's an infinite number of them.
  //

  //         ~scalar
  //   ~num           ~oop+?
  //            ~@{x:~i64}+?  ~@{y:~i64}+?  ~oop
  //            ~@{x:~i64}    ~@{y:~i64}
  // nil         @{x:nil}      @{y:nil}
  //             @{x:i64}      @{y:i64}
  //             @{x:i64}?     @{y:i64}?     oop
  //    num             oop?
  //          scalar
  @Ignore @Test public void testLattice7() {
    N.reset();
    N scal= new N("scalar");
    N num = new N("num"      ,scal);
    N oop0= new N("oop?"     ,scal);
    N oop = new N("oop"      ,oop0);
    N xi0 = new N("@{x:i64}?",oop0);
    N yi0 = new N("@{y:i64}?",oop0);
    N xi  = new N("@{x:i64}" ,xi0,oop );
    N yi  = new N("@{y:i64}" ,yi0,oop );
    N x0  = new N("@{x:nil}" ,xi  );
    N y0  = new N("@{y:nil}" ,yi  );
    N nil = new N("nil"      ,xi0,yi0,num);
    N xix = new N("~@{x:~i64}",x0  );
    N yix = new N("~@{y:~i64}",y0  );
    N xi_ = new N("~@{x:~i64}+0",xix,nil);
    N yi_ = new N("~@{y:~i64}+0",yix,nil);
    N oopx= new N("~oop"     ,xix,yix);
    N oop_= new N("~oop+0"   ,xi_,yi_,oopx);
    N numx= new N("~num"     ,nil);
    N xscal=new N("~scalar" ,oop_,numx);

    // Mark the non-centerline duals
    scal.set_dual(xscal);
    num .set_dual(numx );
    oop0.set_dual(oop_ );
    oop .set_dual(oopx );
    xi0 .set_dual(xi_  );
    yi0 .set_dual(yi_  );
    xi  .set_dual(xix  );
    yi  .set_dual(yix  );

    test(xscal);
  }

  // Another experiment with nil and lattice.  There is a unified central
  // tuple-nil.  Lattice7 fails because no central tuple-nil.  There is no
  // central string-nil.

  // nil cannot go to either "abc?" nor "def?", as this breaks the lattice,
  // thus nil falls to "str?".  "abc" can fall to "abc?"  but not when mixed in
  // with nil - which makes "abc?" a useless (but correct) entry in the
  // lattice.

  // Making a private nil-type per each regular type restores the lattice.
  // This is the TypeUnion.NIL concept taking to the limit.  So: {oop,oop?}
  // lifts to {str,str?} lifts to e.g. {abc,abc?} and {def,def?}.  abc? lifts
  // to abc:nil; def? lifts to def:nil.


  // Lattice!
  // This structure is tested to be a lattice (with and without {abc?,def?,abc+0,def+0}):

  //          ~scalar
  // ~num                ~oop+0
  //          ~oop        {~i64}+0   {~f64}+0   ~str+0
  //       {~i64} {~f64}                          ~str
  //                     {7}+0 {nil}+0 {7.}+0         "abc"+0 "def"+0
  // i64:0   {7}   {nil}   {7.}                    abc:0  "abc"   "def"  def:0
  //                     {7}?  {nil}?  {7.}?          "abc"?  "def"?
  //       { i64} { f64}                           str
  //           oop        { i64}?    { f64}?    str?
  //  num                 oop?
  //           scalar
  @Test public void testLattice8() {
    N.reset();
    N scal= new N("scalar");

    N num = new N("num"    ,scal);
    N inil= new N("0:int"  ,num);

    N oop0= new N("oop?"   ,scal);
    N oop = new N("oop"    ,oop0);
    N i0  = new N("(i64)?" ,oop0);
    N f0  = new N("(f64)?" ,oop0);
    N i70 = new N("(7)?"   ,i0);
    N f70 = new N("(7.)?"  ,f0);
    N i   = new N("(i64)"  ,oop,i0);
    N f   = new N("(f64)"  ,oop,f0);
    N n0  = new N("(nil)?" ,i70,f70);

    N n   = new N("(nil)"  ,n0,i,f);
    N i7  = new N("(7)"    ,i);
    N f7  = new N("(7.)"   ,f);
    N tnil= new N("0:tup"   ,n0);

    N str0= new N("str?"   ,oop0);
    N str = new N("str"    ,str0,oop  );
    N abc0= new N("abc?"   ,str0);
    N def0= new N("def?"   ,str0);

    N abc = new N("abc"    ,str,abc0);
    N def = new N("def"    ,str,def0);
    N abcnil= new N("0:abc",abc0);
    N defnil= new N("0:def",def0);

    N abc_= new N("abc+0"   ,abc,abcnil);
    N def_= new N("def+0"   ,def,defnil);
    N strx= new N("~str"    ,abc,def);
    N str_= new N("~str+0"  ,strx,abc_,def_);

    N n_  = new N("(nil)+0" ,tnil,n);
    N ix  = new N("(~i64)"  ,n,i7);
    N fx  = new N("(~f64)"  ,n,f7);
    N i7_ = new N("(7)+0"   ,n_);
    N f7_ = new N("(7.)+0"  ,n_);
    N i_  = new N("(~i64)+0",ix,i7_);
    N f_  = new N("(~f64)+0",fx,f7_);
    N oopx= new N("~oop"    ,ix,fx,strx);
    N oop_= new N("~oop+0"  ,oopx,i_,f_,str_);

    N numx= new N("~num"    ,inil);

    N xscl= new N("~scalar" ,oop_,numx);

    // Mark the non-centerline duals
    scal.set_dual(xscl );
    num .set_dual(numx );
    oop0.set_dual(oop_ );
    oop .set_dual(oopx );
    i0  .set_dual(i_   );
    f0  .set_dual(f_   );
    i70 .set_dual(i7_  );
    f70 .set_dual(f7_  );
    i   .set_dual(ix   );
    f   .set_dual(fx   );
    n0  .set_dual(n_   );

    str0.set_dual(str_ );
    str .set_dual(strx );
    abc0.set_dual(abc_ );
    def0.set_dual(def_ );

    test(xscl);
  }


  // Lattice!
  // This structure is tested to be a lattice.

  // Testing mixed tuple contents:
  //                  ( ANY,ANY...)
  //                             (ANY,ALL...)
  //   (~i64,ANY...)  (~str,ANY...)
  //                       (~i64,ALL...)  (~str,ALL...)
  //   ( i64,ANY...)  ( str,ANY...)
  //                       ( i64,ALL...)  ( str,ALL...)
  //          (ALL,ANY...)
  //                  ( ALL,ALL...)
  @Test public void testLattice9() {
    N.reset();
    N bot = new N("( ALL,ALL)");
    N i64 = new N("( i64,ALL)",bot);
    N str = new N("( str,ALL)",bot);

    N xi64= new N("(~i64,ALL)",i64);
    N xstr= new N("(~str,ALL)",str);

    N xbot= new N("( ANY,ALL)",xstr,xi64);
    N xtop= new N("( ALL,ANY)",bot);

    N i64x= new N("( i64,ANY)",xtop);
    N strx= new N("( str,ANY)",xtop);

    N xi64x=new N("(~i64,ANY)",i64x);
    N xstrx=new N("(~str,ANY)",strx);

    N top = new N("( ANY,ANY)" ,xi64x,xstrx,xbot);

    // Mark the non-centerline duals
    bot.set_dual(top);
    xbot.set_dual(xtop);

    i64.set_dual(xi64x);
    str.set_dual(xstrx);

    xi64.set_dual(i64x);
    xstr.set_dual(strx);

    test(top);
  }


  // Testing for lattices over trees - specifically Bits.java trees.  Expanding
  // all tree parents into their leaves gives us a lattice over sets and
  // set-inclusions, which typically ARE a lattice
  // (https://en.wikipedia.org/wiki/Lattice_(order) pic#1).
  // Set elements are 2,5,6 are all independent sets (siblings in the tree).

  // The following is NOT a lattice (matches pic#7): The MEET of {+2+5} and 6
  // is either {2&6} or {5&6}, no GLB.
  //
  //         {+2+5+6}
  //        /    |   \
  //  {+2+5}  {+2+6}  {+5+6}
  //    |  /  \    /   \   |
  //    2        5        6    -- centerline constants
  //    |  \  /    \   /   |
  //  { 2&5}  { 2&6}  { 5&6}
  //        \    |   /
  //         { 2&5&6}
  @Ignore @Test public void testLattice10() {
    N.reset();
    N x256 = new N("{ 2&5&6}");

    N x25  = new N("{ 2&5}",x256);
    N x26  = new N("{ 2&6}",x256);
    N x56  = new N("{ 5&6}",x256);

    N c2   = new N("2",x25,x26);
    N c5   = new N("5",x25,x56);
    N c6   = new N("6",x26,x56);

    N o25  = new N("{+2+5}",c2,c5);
    N o26  = new N("{+2+6}",c2,c6);
    N o56  = new N("{+5+6}",c5,c6);

    N o256 = new N("{+2+5+6}",o25,o26,o56);

    // Mark the non-centerline duals
    x256.set_dual(o256);
    x25 .set_dual(o25 );
    x26 .set_dual(o26 );
    x56 .set_dual(o56 );

    test(o256);
  }

  // Add some extra bits: A+BC, B+AC, C+AB, A(B+C), B(A+C), C(A+B)
  //
  // Observation: the complete power-set of ABC and complements should be a
  // simple lattice - of exponental size!

  // Keeping a exponential powerset is too large.
  //   https://en.wikipedia.org/wiki/Espresso_heuristic_logic_minimizer
  // Program to (efficiently, not optimally) reduce boolean expressions.
  
  // Might allow the powerset, which in turn allows choice sets of bits, which
  // allows a lattice w/meet/join/dual to represent Overloads.  
  @Ignore @Test public void testLattice10_a() {
    N.reset();
    N xABC = new N("ABC");

    N xAB  = new N("AB",xABC);
    N xAC  = new N("AC",xABC);
    N xBC  = new N("BC",xABC);

    N pABC = new N("AB+AC",xAB,xAC);
    N pBCA = new N("AB+BC",xAB,xBC);
    N pCAB = new N("AC+BC",xAC,xBC);
    
    N CA   = new N("A",pABC);
    N CB   = new N("B",pBCA);
    N CC   = new N("C",pCAB);

    N sABC = new N("BC+A",CA,pBCA,pCAB);
    N sBCA = new N("AC+B",CB,pCAB,pABC);
    N sCAB = new N("AB+C",CC,pBCA,pABC);
    
    N oAB  = new N("A+B",sABC,sBCA);
    N oAC  = new N("A+C",sABC,sCAB);
    N oBC  = new N("B+C",sBCA,sCAB);

    N oABC = new N("A+B+C",oAB,oAC,oBC);

    // Mark the non-Centerline duals
    xABC.set_dual(oABC);
    xAB .set_dual(oAB );
    xAC .set_dual(oAC );
    xBC .set_dual(oBC );

    pABC.set_dual(sABC);
    pBCA.set_dual(sBCA);
    pCAB.set_dual(sCAB);

    test(oABC);
  }

  
  // Same as Lattice10, except no centerline constants; everything is either up
  // or down.  Still not a Lattice.  The MEET of {+2+5} and &6 is either {2&6}
  // or {5&6}, no GLB.
  // The following is NOT a lattice (matches pic#7).  Set elements are 2,5,6
  // and are all independent sets (siblings in the tree).
  //
  //         {+2+5+6}
  //        /    |   \
  //  {+2+5}  {+2+6}  {+5+6}
  //    | /  \      /  \  |
  //   +2       +5       +6
  //    |        |        |
  //   &2       &5       &6
  //    | \  /      \  /  |
  //  { 2&5}  { 2&6}  { 5&6}
  //        \    |   /
  //         { 2&5&6}
  @Ignore @Test public void testLattice11() {
    N.reset();
    N x256 = new N("{ 2&5&6}");

    N x25  = new N("{ 2&5}",x256);
    N x26  = new N("{ 2&6}",x256);
    N x56  = new N("{ 5&6}",x256);

    N x2   = new N("&2",x25,x26);
    N x5   = new N("&5",x25,x56);
    N x6   = new N("&6",x26,x56);

    N o2   = new N("+2",x2);
    N o5   = new N("+5",x5);
    N o6   = new N("+6",x6);

    N o25  = new N("{+2+5}",o2,o5);
    N o26  = new N("{+2+6}",o2,o6);
    N o56  = new N("{+5+6}",o5,o6);

    N o256 = new N("{+2+5+6}",o25,o26,o56);

    // Mark the non-centerline duals
    x256.set_dual(o256);
    x25 .set_dual(o25 );
    x26 .set_dual(o26 );
    x56 .set_dual(o56 );

    x2  .set_dual(o2  );
    x5  .set_dual(o5  );
    x6  .set_dual(o6  );

    test(o256);
  }


  // The following IS a lattice (two copies of pic#1 joined by the empty set).
  // Set elements are 2,5,6 and are all independent sets (siblings in the tree).
  //
  //         {+2+5+6}
  //        /    |   \
  //  {+2+5}  {+2+6}  {+5+6}
  //    |  /  \    /   \   |
  //   +2       +5       +6
  //     \       |      /
  //            [ ]
  //     /       |      \
  //   &2       &5       &6
  //    |  \  /    \   /   |
  //  { 2&5}  { 2&6}  { 5&6}
  //        \    |   /
  //         { 2&5&6}
  @Test public void testLattice12() {
    N.reset();
    N x256 = new N("{ 2&5&6}");

    N x25  = new N("{ 2&5}",x256);
    N x26  = new N("{ 2&6}",x256);
    N x56  = new N("{ 5&6}",x256);

    N x2   = new N("&2",x25,x26);
    N x5   = new N("&5",x25,x56);
    N x6   = new N("&6",x26,x56);

    N mt   = new N("[]",x2,x5,x6);

    N o2   = new N("+2",mt);
    N o5   = new N("+5",mt);
    N o6   = new N("+6",mt);

    N o25  = new N("{+2+5}",o2,o5);
    N o26  = new N("{+2+6}",o2,o6);
    N o56  = new N("{+5+6}",o5,o6);

    N o256 = new N("{+2+5+6}",o25,o26,o56);

    // Mark the non-centerline duals
    x256.set_dual(o256);
    x25 .set_dual(o25 );
    x26 .set_dual(o26 );
    x56 .set_dual(o56 );

    x2  .set_dual(o2  );
    x5  .set_dual(o5  );
    x6  .set_dual(o6  );

    test(o256);
  }

  // Not a lattice; exactly Pic.8 from Lattice_(order) page.
  // Set {1} is the parent of {2,3}.
  // Using just a {+1} means: pick any of 2 or 3.
  // Using {2,3} means: pick any 2 AND pick any 3.

  // Cannot collapse {+1,+2,+3} into {+1}, because this does not return both a
  // 2 and a 3.  Instead, since {+2,+3} "cover" {+1}, can remove the +1.
  // Assume all tree-splits are complete, and only the primitives & Parse have
  // more than 2 (otherwise fidx & alias splits are *splits* and make 2 from 1).
  //
  //          {+1}
  //        {+2+3+4}
  //  {+2+3} {+2+4}  {+3+4}    ### &2 meet {+3+4}
  //  {+2}    {+3}     {+4}    ### &2&3 and &2&4
  //  {&2}    {&3}     {&4}
  //  {&2&3} {&2&4}  {&3&4}
  //        {&2&3&4}
  //          {&1}
  @Ignore
  @Test public void testLattice12a() {
    N.reset();
    N _1  = new N("{&1}");
    N _234= new N("{&2&3&4}",_1);

    N _23 = new N("{&2&3}",_234);
    N _24 = new N("{&2&4}",_234);
    N _34 = new N("{&3&4}",_234);

    N _2   = new N("&2",_23,_24);
    N _3   = new N("&3",_23,_34);
    N _4   = new N("&4",_24,_34);

    N x2   = new N("+2",_2);
    N x3   = new N("+3",_3);
    N x4   = new N("+4",_4);

    N x23 = new N("{+2+3}",x2,x3);
    N x24 = new N("{+2+4}",x2,x4);
    N x34 = new N("{+3+4}",x3,x4);

    N x234= new N("{+2+3+4}",x23,x24,x34);

    N x1  = new N("{+1}",x234);

    // Mark the non-centerline duals
    x234.set_dual(_234);
    x23 .set_dual(_23 );
    x24 .set_dual(_24 );
    x34 .set_dual(_34 );

    x2  .set_dual(_2  );
    x3  .set_dual(_3  );
    x4  .set_dual(_4  );

    x1  .set_dual(_1  );

    test(x1);
  }


  // Bits indicate in/out.  Another bit for up/down.  Another bit for bulk
  // meet/join.  In the implementation, if a parent in is IN, then all children
  // are IN, and forced zero.  Future/unnamed children are IN.  If a parent is
  // OUT, then each child can be in or out.  Future/unnamed children are OUT.
  //
  //          +{~2~3~4}
  //  +{~2~3}  +{~2~4}  +{~3~4}
  //  +{~2}    +{~3}      +{~4}
  //  &{~2}    &{~3}      &{~4}
  //  &{~2~3}  &{~2~4}  &{~3~4}
  //          &{~2~3~4}
  //
  //          +{ 2 3 4}
  //  +{ 2 3}  +{ 2 4}  +{ 3 4}
  //  +{ 2}    +{ 3}      +{ 4}
  //  &{ 2}    &{ 3}      &{ 4}
  //  &{ 2 3}  &{ 2 4}  &{ 3 4}
  //          &{ 2 3 4}
  //
  @Ignore
  @Test public void testLattice12b() {
    N.reset();
    N and_234= new N("&{ 2 3 4}");

    N and_23 = new N("&{ 2 3}",and_234);
    N and_24 = new N("&{ 2 4}",and_234);
    N and_34 = new N("&{ 3 4}",and_234);

    N and_2   = new N("&{ 2}",and_23,and_24);
    N and_3   = new N("&{ 3}",and_23,and_34);
    N and_4   = new N("&{ 4}",and_24,and_34);

    N oor_2   = new N("+{ 2}",and_2);
    N oor_3   = new N("+{ 3}",and_3);
    N oor_4   = new N("+{ 4}",and_4);

    N oor_23 = new N("+{ 2 3}",oor_2,oor_3);
    N oor_24 = new N("+{ 2 4}",oor_2,oor_4);
    N oor_34 = new N("+{ 3 4}",oor_3,oor_4);

    N oor_234= new N("+{ 2 3 4}",oor_23,oor_24,oor_34);

    N andx234= new N("&{~2~3~4}",oor_234);

    N andx23 = new N("&{~2~3}",andx234);
    N andx24 = new N("&{~2~4}",andx234);
    N andx34 = new N("&{~3~4}",andx234);

    N andx2   = new N("&{~2}",andx23,andx24);
    N andx3   = new N("&{~3}",andx23,andx34);
    N andx4   = new N("&{~4}",andx24,andx34);

    N oorx2   = new N("+{~2}",andx2);
    N oorx3   = new N("+{~3}",andx3);
    N oorx4   = new N("+{~4}",andx4);

    N oorx23 = new N("+{~2~3}",oorx2,oorx3);
    N oorx24 = new N("+{~2~4}",oorx2,oorx4);
    N oorx34 = new N("+{~3~4}",oorx3,oorx4);

    N oorx234= new N("+{~2~3~4}",oorx23,oorx24,oorx34);

    // Mark the non-centerline duals
    andx234.set_dual(oor_234);

    andx23 .set_dual(oor_23 );
    andx24 .set_dual(oor_24 );
    andx34 .set_dual(oor_34 );

    andx2  .set_dual(oor_2  );
    andx3  .set_dual(oor_3  );
    andx4  .set_dual(oor_4  );

    oorx2  .set_dual(and_2  );
    oorx3  .set_dual(and_3  );
    oorx4  .set_dual(and_4  );

    oorx23 .set_dual(and_23 );
    oorx24 .set_dual(and_24 );
    oorx34 .set_dual(and_34 );

    oorx234.set_dual(and_234);

    test(oorx234);
  }


  // Same as lattice 12, except using a high & low empty sets.
  // Set elements are 2,5,6 and are all independent sets (siblings in the tree).
  //
  //         {+2+5+6}
  //        /    |   \
  //  {+2+5}  {+2+6}  {+5+6}
  //    |  /  \    /   \   |
  //   +2       +5       +6
  //     \       |      /
  //            [+]               -- high empty
  //            [ ]               -- low  empty
  //     /       |      \
  //   &2       &5       &6
  //    |  \  /    \   /   |
  //  { 2&5}  { 2&6}  { 5&6}
  //        \    |   /
  //         { 2&5&6}
  @Test public void testLattice12d() {
    N.reset();
    N x256 = new N("{ 2&5&6}");

    N x25  = new N("{ 2&5}",x256);
    N x26  = new N("{ 2&6}",x256);
    N x56  = new N("{ 5&6}",x256);

    N x2   = new N("&2",x25,x26);
    N x5   = new N("&5",x25,x56);
    N x6   = new N("&6",x26,x56);

    N mt   = new N("[]",x2,x5,x6);

    N o2   = new N("+2",mt);
    N o5   = new N("+5",mt);
    N o6   = new N("+6",mt);

    N o25  = new N("{+2+5}",o2,o5);
    N o26  = new N("{+2+6}",o2,o6);
    N o56  = new N("{+5+6}",o5,o6);

    N o256 = new N("{+2+5+6}",o25,o26,o56);

    // Mark the non-centerline duals
    x256.set_dual(o256);
    x25 .set_dual(o25 );
    x26 .set_dual(o26 );
    x56 .set_dual(o56 );

    x2  .set_dual(o2  );
    x5  .set_dual(o5  );
    x6  .set_dual(o6  );

    test(o256);
  }

  // Same as testLattice12, except 6 is now nil... which is on the centerline.
  // Not a lattice, although testLattice12 IS.
  // This implies I need a sign-nil: unsigned nil sits on the centerline.
  // Set elements are 2,5 and are all independent sets (siblings in the tree).
  //
  //         {+2+5+0}
  //        /    |   \
  //  {+2+5}  {+2+0}  {+5+0}
  //    |  /  \    /   \  /
  //   +2       +5       |
  //     \       |       |
  //            [ ]      0
  //     /       |       |
  //   &2       &5       |
  //    |  \  /    \   /  \
  //  { 2&5}  { 2&0}  { 5&0}
  //        \    |   /
  //         { 2&5&0}
  @Ignore @Test public void testLattice13() {
    N.reset();
    N x250 = new N("{ 2&5&0}");

    N x25  = new N("{ 2&5}",x250);
    N x20  = new N("{ 2&0}",x250);
    N x50  = new N("{ 5&0}",x250);

    N x2   = new N("&2",x25,x20);
    N x5   = new N("&5",x25,x50);

    N nil  = new N("0",x20,x50);
    N mt   = new N("[]",x2,x5);

    N o2   = new N("+2",mt);
    N o5   = new N("+5",mt);

    N o25  = new N("{+2+5}",o2,o5);
    N o20  = new N("{+2+0}",o2,nil);
    N o50  = new N("{+5+0}",o5,nil);

    N o250 = new N("{+2+5+0}",o25,o20,o50);

    // Mark the non-centerline duals
    x250.set_dual(o250);
    x25 .set_dual(o25 );
    x20 .set_dual(o20 );
    x50 .set_dual(o50 );

    x2  .set_dual(o2  );
    x5  .set_dual(o5  );

    test(o250);
  }


  // Tests as a lattice.  The following is testLattice12, with 0 instead of 6
  // AND more structure appended around: {scalar->int->{nint,nil}} and its
  // inverse.  nil ONLY goes to +/-0.  Each bit-set, e.g. {+5+0} or {+0}
  // expands to a full pointer-target-type 6-element mini-lattice:
  //    ~obj
  // ~rec  ~str
  //  rec   str
  //     obj
  //
  // Which means crossing-nil has to choose between pointing at
  // {+0->obj} or {+0->~obj} but canNOT point at e.g. {+0->rec}.
  //
  //                  /--- ~scalar
  //                /-          \
  //         {+2+5+0}           ~int
  //        /    |   \          /   \
  //  {+2+5}  {+2+0}  {+5+0}    |  ~nint
  //    |  /  \    /   \   |    |    |
  //   +2       +5       +0     |
  //     \       |      /    \  /
  //            [ ]           nil
  //     /       |      \    /  \
  //   &2       &5       &0     |
  //    |  \  /    \   /   |    |    |
  //  { 2&5}  { 2&0}  { 5&0}    |   nint
  //        \    |   /          \   /
  //         { 2&5&0}            int
  //                \-          /
  //                  \---  scalar
  //
  @Test public void testLattice14() {
    N.reset();
    N xscl = new N("scalar");
    N x250 = new N("{ 2&5&0}",xscl);
    N xint = new N("int",xscl);

    N x25  = new N("{ 2&5}",x250);
    N x20  = new N("{ 2&0}",x250);
    N x50  = new N("{ 5&0}",x250);
    N xnint= new N("nint",xint);

    N x2   = new N("&2",x25,x20);
    N x5   = new N("&5",x25,x50);
    N x0   = new N("&0",x20,x50);

    N mt   = new N("[]",x2,x5,x0);
    N nil  = new N("nil",x0,xint);

    N o2   = new N("+2",mt);
    N o5   = new N("+5",mt);
    N o0   = new N("+0",mt,nil);

    N onint= new N("~nint",xnint);
    N o25  = new N("{+2+5}",o2,o5);
    N o20  = new N("{+2+0}",o2,o0);
    N o50  = new N("{+5+0}",o5,o0);

    N oint = new N("~int",nil,onint);
    N o250 = new N("{+2+5+0}",o25,o20,o50);
    N sclr = new N("~scalar",o250,oint);

    // Mark the non-centerline duals
    xscl.set_dual(sclr);
    x250.set_dual(o250);

    x25 .set_dual(o25 );
    x20 .set_dual(o20 );
    x50 .set_dual(o50 );
    xint.set_dual(oint);
    xnint.set_dual(onint);

    x2  .set_dual(o2  );
    x5  .set_dual(o5  );
    x0  .set_dual(o0  );

    test(sclr);
  }

  // Building the simplist possible 2-alias ptr lattice, then adding nil.
  // The two aliases are 0 & 4, and the ptr-lattice includes {obj,rec,str}.
  // Alias lattice has 7 states:  Ptr-lattice has 6:
  //   ~0~4                           ~obj
  //  ~0  ~4                       ~rec  ~str
  //    mt                          rec   str
  //   0   4                           obj
  //    0 4

  // These two lattices are "multiplied" yielding 42 states.  Then we inject
  // 'nil'.  Does 'nil' have edges to "[0]->obj"? "[0]->~obj"?  Something else?
  // Tested as Lattice: [0]-> obj  <==  NIL  <==  [~0]->~obj
  // Fails  as Lattice: [0]->~obj  <==  NIL  <==  [~0]-> obj
  @Test public void testLattice15() {
    N.reset();

    // Layer [ 0 4] -> {~obj,~rec,~str,str,rec,obj}
    N n_04_obj = new N("n_04_obj");
    N n_04_rec = new N("n_04_rec",n_04_obj);
    N n_04_str = new N("n_04_str",n_04_obj);
    N n_04xrec = new N("n_04xrec",n_04_rec);
    N n_04xstr = new N("n_04xstr",n_04_str);
    N n_04xobj = new N("n_04xobj",n_04xrec,n_04xstr);

    // Layer [ 0  ] -> {~obj,~rec,~str,str,rec,obj}
    N n_0__obj = new N("n_0__obj"                  ,n_04_obj);
    N n_0__rec = new N("n_0__rec",n_0__obj         ,n_04_rec);
    N n_0__str = new N("n_0__str",n_0__obj         ,n_04_str);
    N n_0_xrec = new N("n_0_xrec",n_0__rec         ,n_04xrec);
    N n_0_xstr = new N("n_0_xstr",n_0__str         ,n_04xstr);
    N n_0_xobj = new N("n_0_xobj",n_0_xrec,n_0_xstr,n_04xobj);

    // Layer [   4] -> {~obj,~rec,~str,str,rec,obj}
    N n__4_obj = new N("n__4_obj"                  ,n_04_obj);
    N n__4_rec = new N("n__4_rec",n__4_obj         ,n_04_rec);
    N n__4_str = new N("n__4_str",n__4_obj         ,n_04_str);
    N n__4xrec = new N("n__4xrec",n__4_rec         ,n_04xrec);
    N n__4xstr = new N("n__4xstr",n__4_str         ,n_04xstr);
    N n__4xobj = new N("n__4xobj",n__4xrec,n__4xstr,n_04xobj);

    // Layer [    ] -> {~obj,~rec,~str,str,rec,obj}
    N n_mt_obj = new N("n_mt_obj"                  ,n_0__obj,n__4_obj);
    N n_mt_rec = new N("n_mt_rec",n_mt_obj         ,n_0__rec,n__4_rec);
    N n_mt_str = new N("n_mt_str",n_mt_obj         ,n_0__str,n__4_str);
    N n_mtxrec = new N("n_mtxrec",n_mt_rec         ,n_0_xrec,n__4xrec);
    N n_mtxstr = new N("n_mtxstr",n_mt_str         ,n_0_xstr,n__4xstr);
    N n_mtxobj = new N("n_mtxobj",n_mtxrec,n_mtxstr,n_0_xobj,n__4xobj);

    // An UNSIGNED NIL works IFF NIL expands as-if "[0]->obj", which means
    // meeting with NIL loses the base type of a pointer.  But it remains a
    // lattice.

    // Signed Nil works, and is a lattice.
    N NIL = new N(" NIL",n_0__obj);
    N XNIL= new N("XNIL",n_0_xobj);

    // Layer [~0  ] -> {~obj,~rec,~str,str,rec,obj}
    N nx0__obj = new N("nx0__obj"                  ,n_mt_obj, NIL);
    N nx0__rec = new N("nx0__rec",nx0__obj         ,n_mt_rec);
    N nx0__str = new N("nx0__str",nx0__obj         ,n_mt_str);
    N nx0_xrec = new N("nx0_xrec",nx0__rec         ,n_mtxrec);
    N nx0_xstr = new N("nx0_xstr",nx0__str         ,n_mtxstr);
    N nx0_xobj = new N("nx0_xobj",nx0_xrec,nx0_xstr,n_mtxobj, XNIL);

    // Layer [~4  ] -> {~obj,~rec,~str,str,rec,obj}
    N nx_4_obj = new N("nx_4_obj"                  ,n_mt_obj);
    N nx_4_rec = new N("nx_4_rec",nx_4_obj         ,n_mt_rec);
    N nx_4_str = new N("nx_4_str",nx_4_obj         ,n_mt_str);
    N nx_4xrec = new N("nx_4xrec",nx_4_rec         ,n_mtxrec);
    N nx_4xstr = new N("nx_4xstr",nx_4_str         ,n_mtxstr);
    N nx_4xobj = new N("nx_4xobj",nx_4xrec,nx_4xstr,n_mtxobj);

    // Layer [~0~4] -> {~obj,~rec,~str,str,rec,obj}
    N nx04_obj = new N("nx04_obj"                  ,nx0__obj,nx_4_obj);
    N nx04_rec = new N("nx04_rec",nx04_obj         ,nx0__rec,nx_4_rec);
    N nx04_str = new N("nx04_str",nx04_obj         ,nx0__str,nx_4_str);
    N nx04xrec = new N("nx04xrec",nx04_rec         ,nx0_xrec,nx_4xrec);
    N nx04xstr = new N("nx04xstr",nx04_str         ,nx0_xstr,nx_4xstr);
    N nx04xobj = new N("nx04xobj",nx04xrec,nx04xstr,nx0_xobj,nx_4xobj);


    // Mark the non-centerline duals
    n_04_obj.set_dual(nx04xobj);
    n_04_rec.set_dual(nx04xrec);
    n_04_str.set_dual(nx04xstr);
    n_04xrec.set_dual(nx04_rec);
    n_04xstr.set_dual(nx04_str);
    n_04xobj.set_dual(nx04_obj);

    n_0__obj.set_dual(nx0_xobj);
    n_0__rec.set_dual(nx0_xrec);
    n_0__str.set_dual(nx0_xstr);
    n_0_xrec.set_dual(nx0__rec);
    n_0_xstr.set_dual(nx0__str);
    n_0_xobj.set_dual(nx0__obj);

    n__4_obj.set_dual(nx_4xobj);
    n__4_rec.set_dual(nx_4xrec);
    n__4_str.set_dual(nx_4xstr);
    n__4xrec.set_dual(nx_4_rec);
    n__4xstr.set_dual(nx_4_str);
    n__4xobj.set_dual(nx_4_obj);

    n_mt_obj.set_dual(n_mtxobj);
    n_mt_rec.set_dual(n_mtxrec);
    n_mt_str.set_dual(n_mtxstr);

    NIL.set_dual(XNIL);

    test(nx04xobj);
  }

  // Named subtypes, plus array (subtype string), tuple (subtype rec).
  // NOT A LATTICE as soon as you have more than 1 name.
  //
  //        ~obj             And named subtypes A, B
  //    ~ary    ~tup            ~obj ==> A:~obj ==> A:~tup  ==> A:~rec ==> A:rec ==> A:tup ==> A:obj ==> obj
  //  ~str        ~rec
  //   str         rec
  //     ary     tup
  //         obj
  //
  // This IS a lattice for a single name (and nested names), but not for
  // multiple names.
  //
  @Ignore @Test public void testLattice16() {
    N.reset();

    N __obj = new N("__obj");
    N A_obj = new N("A_obj",__obj);
    N B_obj = new N("B_obj",__obj);

    N __ary =   new N("__ary",__obj);
    N A_ary =     new N("A_ary",__ary,A_obj);
    N B_ary =     new N("B_ary",__ary,B_obj);
    N __tup =   new N("__tup",__obj);
    N A_tup =     new N("A_tup",__tup,A_obj);
    N B_tup =     new N("B_tup",__tup,B_obj);

    N __str =     new N("__str",__ary);
    N A_str =       new N("A_str",__str,A_ary);
    N B_str =       new N("B_str",__str,B_ary);
    N __rec =     new N("__rec",__tup);
    N A_rec =       new N("A_rec",__rec,A_tup);
    N B_rec =       new N("B_rec",__rec,B_tup);

    N Axrec =       new N("A~rec",A_rec);
    N Bxrec =       new N("B~rec",B_rec);
    N _xrec =     new N("_~rec",Axrec,Bxrec);
    N Axstr =       new N("A~str",A_str);
    N Bxstr =       new N("B~str",B_str);
    N _xstr =     new N("_~str",Axstr,Bxstr);

    N Axtup =     new N("A~tup",Axrec);
    N Bxtup =     new N("B~tup",Bxrec);
    N _xtup =   new N("_~tup",_xrec,Axtup,Bxtup);
    N Axary =     new N("A~ary",Axstr);
    N Bxary =     new N("B~ary",Bxstr);
    N _xary =   new N("_~ary",_xstr,Axary,Bxary);

    N Axobj = new N("A~obj",Axary,Axtup);
    N Bxobj = new N("B~obj",Bxary,Bxtup);
    N _xobj = new N("_~obj",_xtup,_xary,Axobj,Bxobj);

    __obj.set_dual(_xobj);
    __ary  .set_dual(_xary);
    __str    .set_dual(_xstr);
    __tup  .set_dual(_xtup);
    __rec    .set_dual(_xrec);
    A_obj  .set_dual(Axobj);
    A_ary    .set_dual(Axary);
    A_str      .set_dual(Axstr);
    A_tup    .set_dual(Axtup);
    A_rec    .set_dual(Axrec);
    B_obj  .set_dual(Bxobj);
    B_ary    .set_dual(Bxary);
    B_str      .set_dual(Bxstr);
    B_tup    .set_dual(Bxtup);
    B_rec    .set_dual(Bxrec);

    test(_xobj);
  }

  // Named subtypes, plus array (subtype string), tuple (subtype rec).  Similar
  // to the testLattice6 case, only pick up names at the outermost level.
  //
  //        ~obj             And named subtypes A, B
  //    ~ary    ~tup            ~obj ==> A:~obj ==> A:~tup  ==> A:~rec ==> A:rec ==> A:tup ==> A:obj ==> obj
  //  ~str        ~rec          ~obj ==> B:~obj ==> B:~tup  ==> B:~rec ==> B:rec ==> B:tup ==> B:obj ==> obj
  //   str         rec       NO INNER EDGES, e.g. A:rec ==> rec !!!
  //     ary     tup
  //         obj
  //
  // This IS a lattice for a single name (and nested names), but not for
  // multiple names.
  //
  @Test public void testLattice17() {
    N.reset();

    N __obj = new N("__obj");
    N A_obj = new N("A_obj",__obj);
    N B_obj = new N("B_obj",__obj);

    N __ary =   new N("__ary",__obj);
    N A_ary =     new N("A_ary",A_obj);
    N B_ary =     new N("B_ary",B_obj);
    N __tup =   new N("__tup",__obj);
    N A_tup =     new N("A_tup",A_obj);
    N B_tup =     new N("B_tup",B_obj);

    N __str =     new N("__str",__ary);
    N A_str =       new N("A_str",A_ary);
    N B_str =       new N("B_str",B_ary);
    N __rec =     new N("__rec",__tup);
    N A_rec =       new N("A_rec",A_tup);
    N B_rec =       new N("B_rec",B_tup);

    N Axrec =       new N("A~rec",A_rec);
    N Bxrec =       new N("B~rec",B_rec);
    N _xrec =     new N("_~rec",__rec);
    N Axstr =       new N("A~str",A_str);
    N Bxstr =       new N("B~str",B_str);
    N _xstr =     new N("_~str",__str);

    N Axtup =     new N("A~tup",Axrec);
    N Bxtup =     new N("B~tup",Bxrec);
    N _xtup =   new N("_~tup",_xrec);
    N Axary =     new N("A~ary",Axstr);
    N Bxary =     new N("B~ary",Bxstr);
    N _xary =   new N("_~ary",_xstr);

    N Axobj = new N("A~obj",Axary,Axtup);
    N Bxobj = new N("B~obj",Bxary,Bxtup);
    N _xobj = new N("_~obj",_xtup,_xary,Axobj,Bxobj);

    __obj.set_dual(_xobj);
    __ary  .set_dual(_xary);
    __str    .set_dual(_xstr);
    __tup  .set_dual(_xtup);
    __rec    .set_dual(_xrec);
    A_obj  .set_dual(Axobj);
    A_ary    .set_dual(Axary);
    A_str      .set_dual(Axstr);
    A_tup    .set_dual(Axtup);
    A_rec    .set_dual(Axrec);
    B_obj  .set_dual(Bxobj);
    B_ary    .set_dual(Bxary);
    B_str      .set_dual(Bxstr);
    B_tup    .set_dual(Bxtup);
    B_rec    .set_dual(Bxrec);

    test(_xobj);

  }

  // Nil, not-nil, ints, floats, scalars
  @Test public void testLattice18() {
    N.reset();
    N  sclr = new N(" sclr");
    N nsclr = new N("nsclr",sclr );

    N int64 = new N("int64",sclr );
    N flt64 = new N("flt64",sclr );
    N obj40 = new N("obj*?",sclr );

    N nint_ = new N("nint ",int64,nsclr);
    N nflt_ = new N("nflt ",flt64,nsclr);
    N obj4_ = new N("obj* ",obj40,nsclr);

    N int8  = new N("int8 ",int64,flt64);
    N nint8 = new N("nint8",int8 ,nint_, nflt_);

    N lonil = new N("lonil",int8 ,obj40);
    N hinil = new N("hinil",nsclr);

    N xnit8 = new N("xnit8",nint8);
    N xint8 = new N("xint8",xnit8,hinil);

    N xnint = new N("~nint",xnit8);
    N xnflt = new N("~nflt",xnit8);
    N xnobj = new N("~obj*",obj4_);

    N xint_ = new N("~int6",xnint,xint8);
    N xflt_ = new N("~flt6",xnflt,xint8);
    N xobj4 = new N("~obj?",xnobj,hinil);

    N xnscl = new N("~nscl",xnint,xnflt,xnobj,lonil);
    N xsclr = new N("~scal",xint_,xflt_,xobj4,xnscl);

    sclr .set_dual(xsclr);
    nsclr.set_dual(xnscl);
    int64.set_dual(xint_);
    int8 .set_dual(xint8);
    flt64.set_dual(xflt_);
    obj40.set_dual(xobj4);
    nint8.set_dual(xnit8);
    nint_.set_dual(xnint);
    nflt_.set_dual(xnflt);
    obj4_.set_dual(xnobj);
    lonil.set_dual(hinil);

    test(xsclr);
  }

  // Test to figure out how to handle XSCALAR, XNSCALAR with EMPTY structs, in the
  // world where structs are Scalars.
  // Nil, not-nil, ints, scalars, empty struct, struct with a field.
  @Test public void testLattice19() {
    // There is a cube around field "c=???"

    N.reset();
    N  sclr  = new N(" scalar");
    N nsclr  = new N("nscalar",sclr );

    N int64  = new N(" int64 ",sclr );
    N objmt  = new N(" ()    ",sclr );

    N nint_  = new N(" nint  ",int64,nsclr);

    N obj01  = new N(" (c=  int)",objmt);
    N objni  = new N(" (c= nint)",obj01,nsclr);
    N obj00  = new N(" (c= 0   )",obj01);
    N obj11  = new N(" (c=~nint)",objni);
    N obj10  = new N(" (c=~ int)",obj00,obj11);

    N lonil  = new N("lonil",int64,obj01);
    N zero   = new N(" zero",int64);
    N hinil  = new N("hinil",nsclr);

    N xobj10 = new N("~(c=  int)",obj01);
    N xobjni = new N("~(c= nint)",xobj10,objni);
    N xobj00 = new N("~(c= 0   )",obj00,xobj10);
    N xobj11 = new N("~(c=~nint)",obj11,xobjni);
    N xobj01 = new N("~(c=~ int)",obj10,xobj11,xobj00, hinil);

    N xnint  = new N("~nint  ",nint_);

    N xint_  = new N("~int64 ",xnint,hinil,zero);
    N xobjmt = new N("~()    ",xobj01);

    N xnscl  = new N("~nsclar",xnint,xobj11,lonil);
    N xsclr  = new N("~scalar",xobjmt,xint_,xnscl);

    sclr .set_dual(xsclr);
    nsclr.set_dual(xnscl);
    int64.set_dual(xint_);
    objmt.set_dual(xobjmt);
    nint_.set_dual(xnint);
    obj01.set_dual(xobj01);
    obj00.set_dual(xobj00);
    objni.set_dual(xobj11);
    obj10.set_dual(xobj10);
    obj11.set_dual(xobjni);
    lonil.set_dual(hinil);

    test(xsclr);
  }

  // Build a lattice with a lattice-extender.
  // I started with scalar -> nscalar -> ~nscalar -> ~scalar
  // Added outside the extension lattice: () -> ~()
  // Added:  int64 -> ~ int64
  // Added: nint64 -> ~nint64
  // Added: zero
  // Added: nil, xnil
  @Test public void testLattice20() {
    N.reset();

    // Base lattice, to be extended
    N  sclr  = new N(" scalar");
    N nsclr  = new N("nscalar", sclr);
    N int64  = new N(" int64 ", sclr);
    N nint6  = new N("nint64 ",nsclr,int64);
    N  nil   = new N(" nil   ",int64);
    N zero   = new N("zero   ",int64);
    N two    = new N(" 2     ",nint6);
    N three  = new N(" 3     ",nint6);
    N xnil   = new N("xnil   ", sclr);
    N xnint  = new N("~nint64",two,three);
    N xint6  = new N("~int64 ",xnint,zero,xnil);
    N xnscl  = new N("~nsclar",xnint);
    N xsclr  = new N("~scalar",xnscl,xint6,nil);
    xsclr.set_dual( sclr);
    xnscl.set_dual(nsclr);
    xnint.set_dual(nint6);
    xnil .set_dual( nil );
    xint6.set_dual(int64);
    N[] ns = new N[]{sclr,nsclr,int64,nint6,nil,zero,two,three,xnil,xnint,xint6,xnscl,xsclr};
    int len = ns.length;
    // Test base lattice, and reset
    test(xsclr);
    for( N n : ns )
      { n._cnt=0; n._reaches.clear(); n._sups.clear(); }

    // Build the extended lattice
    String lowrap0 = " (c=%s)", hiwrap0 = "~(c=%s)";
    N[] xns0 = lattice_extender(ns,lowrap0,hiwrap0);
    assert xns0[ 0     ]._t.equals(String.format(lowrap0, sclr._t));
    assert xns0[len*2-1]._t.equals(String.format(hiwrap0,xsclr._t));

    // Build the extended lattice
    String lowrap1 = " (d=%s)", hiwrap1 = "~(d=%s)";
    N[] xns1 = lattice_extender(ns,lowrap1,hiwrap1);
    assert xns1[ 0     ]._t.equals(String.format(lowrap1, sclr._t));
    assert xns1[len*2-1]._t.equals(String.format(hiwrap1,xsclr._t));

    // NO: Plug "@{}" between the original and extended lattices
    // Use Scalar directly, NO EMPTY STRUCT
    xns0[0]._subs.push(sclr);
    xns1[0]._subs.push(sclr);
    xsclr._subs.push(xns0[len*2-1]);
    xsclr._subs.push(xns1[len*2-1]);

    // Edges for nscalar/xnscalar, same as Scalar
    assert xns0[        1]._t.equals(String.format(lowrap0,nsclr._t));
    assert xns0[len*2-1-1]._t.equals(String.format(hiwrap0,xnscl._t));
    xns0[1]._subs.push( nsclr );
    xns1[1]._subs.push( nsclr );
    xnscl._subs.push(xns0[len*2-1-1]);
    xnscl._subs.push(xns1[len*2-1-1]);

    // Fails to add edges "going in" at the high side, out at the low side.  If
    // adding ~int to ~@{c=~int} and ~@{d=~int}, and vice-versa @{c=int} and
    // @{c=int} to int, we get two joins of int64 and nscalr as @{c=int64} and
    // @{d=int64}.

    // Try adding edges "going in" at the low side, and out at Scalar.  So
    // adding int -> @{c=int},@{d=int}, and vice-versa ~@{c=~int}, ~@{d=~int}
    // -> ~int.
    assert xns0[        2]._t.equals(String.format(lowrap0,int64._t));
    assert xns0[len*2-1-2]._t.equals(String.format(hiwrap0,xint6._t));
    int64._subs.push( xns0[2] );
    int64._subs.push( xns1[2] );
    xns0[len*2-1-2]._subs.push(xint6);
    xns1[len*2-1-2]._subs.push(xint6);

    // Edges for nint/xnint
    assert xns0[        3]._t.equals(String.format(lowrap0,nint6._t));
    assert xns0[len*2-1-3]._t.equals(String.format(hiwrap0,xnint._t));
    nint6._subs.push( xns0[3] );
    nint6._subs.push( xns1[3] );
    xns0[len*2-1-3]._subs.push(xnint);
    xns1[len*2-1-3]._subs.push(xnint);

    // Broken to add edges for NIL
    //// Edges for nil/xnil
    //assert xns0[        4]._t.equals(String.format(lowrap0, nil._t));
    //assert xns0[len*2-1-4]._t.equals(String.format(hiwrap0,xnil._t));
    //nil._subs.push( xns0[4] );
    //nil._subs.push( xns1[4] );
    //xns0[len*2-1-4]._subs.push(xnil);
    //xns1[len*2-1-4]._subs.push(xnil);

    // Remove redundant edge xnscl->xnint6
    // Remove redundant edge nint6->nscalr
    assert xnscl._subs.at(0)._t.equals("~nint64");
    assert nint6._subs.at(0)._t.equals("nscalar");
    xnscl._subs.del(0);
    nint6._subs.del(0);

    // Remove redundant edge xsclr->xint64
    // Remove redundant edge int64->scalar
    assert xsclr._subs.at(1)._t.equals("~int64 ");
    assert int64._subs.at(0)._t.equals(" scalar");
    xsclr._subs.del(1);
    int64._subs.del(0);

    test(xsclr);
  }

  // Lattice extender: take a set of N as a lattice with duals and edges.  Make
  // 2 copies, declare one copy low and the other high.  Make the low copy have
  // edges to the high.  Make hi/lo duals work inside-out.  Return the double-
  // sized set of N.

  // Example: ~A -> ~B -> C -> B -> A, extend with "%s1" and "%s2".
  //  Make dups:
  //   ~A1 -> ~B1 -> C1 -> B1 -> A1
  //   ~A2 -> ~B2 -> C2 -> B2 -> A2
  // Add edges low to high:
  //   ~A2 -> ~A1,   ~B2 -> ~B1, C2  -> C1,  B2  ->  B1, A2  ->  A1
  // Dual outside-in:
  //   ~A1 <-> A2,   ~B1 <-> B2, C1 <-> C2,  B1 <-> ~B2, A1 <-> ~A2

  static N[] lattice_extender( N[] ns, String lowrap, String hiwrap) {

    // Clone without edges, wrap names.
    int len = ns.length;
    N[] xns = new N[len*2];
    for( int i=0; i<len; i++ ) {
      xns[i    ] = new N(String.format(lowrap, ns[i]._t));
      xns[i+len] = new N(String.format(hiwrap, ns[i]._t));
    }
    // Edges in clones
    for( int i=0; i<len; i++ ) {
      for( N edge : ns[i]._subs ) {
        int idx = Util.find(ns,edge);
        xns[i    ]._subs.push(xns[idx    ]);
        xns[i+len]._subs.push(xns[idx+len]);
      }
    }

    // Add edges low to high
    for( int i=0; i<len; i++ )
      xns[i+len]._subs.push(xns[i]);

    // Dual, outside-in
    for( int i=0; i<len; i++ ) {
      int idx = ns[i]._dual==ns[i] // Self-dual?
        ? len+i                 // Self-duals find their matching other half
        : len*2-1-i;            // Other duals are symmetric in ns not xns, and so need the symmetric part in xns
      xns[i].set_dual(xns[idx]);
    }

    return xns;
  }


  // More complete, simpler lattice.  Structs do not invert (so sit on the
  // centerline), and must have at least 1 field.  In this lattice the notion
  // of a struct @{c=_} is like the difference between int and flt.  nil falls
  // to @{c=int}, so I can usefully meet nil and a struct.

  // Maybe extend this is a 2nd field that "nests" inside @{c=_} so we can
  // allow @{c=_,x=_} and @{c=_,y=_} both of which subtype @{c=_}.  Same
  // as the old TypeStruct, all extra fields already exist at Top/Bot.

  // CNC - next open question:  how do multi-fields stack.
  // Theory: TS is "just" an infinite collection of fields, with defaults for most.
  // now meet nil with this collection-
  //  - which comes to: @{c=nint,d=scalar}
  //
  // CNC - cyclic struct types vs meet?
  @Test public void testLattice21() {
    N.reset();

    // Lattice template.
    N  b64 = new N(0,"  " );
    N nb64 = new N(0," n",  b64);
    N  b32 = new N(0,"32",  b64);
    N nb32 = new N(0,"n32",nb64,b32);
    N zero = new N(0," 0", b32);
    N two  = new N(0," 2",nb32);
    N three= new N(0," 3",nb32);
    N xnb32= new N(0,"~n32",two,three);
    N xb32 = new N(0,"~32",xnb32,zero);
    N xnb  = new N(0,"~n",xnb32);
    N xb64 = new N(0," ~",xnb,xb32);
    xb64.set_dual(b64);
    xnb .set_dual(nb64);
    xb32.set_dual(b32);
    xnb32.set_dual(nb32);
    N[] ns = new N[]{b64,nb64,b32,nb32,zero,two,three,xnb32,xb32,xnb,xb64};
    int len = ns.length;

    // Build the int lattice
    N[] ins = lattice_extender(ns,"%sint");

    // Build the flt lattice
    N[] fns = lattice_extender(ns,"%sflt");

    // Wrap with scalar, nscalr
    N  sclr = new N("scalar");
    N nsclr = new N("nscalr", sclr);
    N xnscl = new N("~nsclr"      );
    N xsclr = new N("~scalr",xnscl);
    nsclr.set_dual(xnscl);
    xsclr.set_dual( sclr);
    add_edge(0,  sclr, ins);
    add_edge(0,  sclr, fns);
    add_edge(1, nsclr, ins);
    add_edge(1, nsclr, fns);

    // Split nil.  Feels odd to connect ~nScalar with nil and ~nil to nScalar,
    // but required else not a lattice.
    N  nil = new N(" nil");
    N xnil = new N("~nil",nsclr);
    xnil.set_dual(nil);
    add_edge(len-1-2, xnil, ins);
    add_edge(len-1-2, xnil, fns);
    xnscl._subs.push(nil);

    // Can I ~nil->0int->nil ?
    // NO: Crossing Nil.
    assert ins[4]._t.equals(" 0int");
    //ins[4]._subs.push(nil);
    //xnil._subs.push(ins[4]);
    //fns[4]._subs.push(nil);
    //xnil._subs.push(fns[4]);

    // Add edge from f64/i64 to i32
    // NO: No valid join for eg int and nflt; both ~flt and ~nscalar
    //add_edge(2, fns[0], ins);

    // Build larger lattice for structures
    N b_scal = new N(0," SC");
    b64._subs.push(b_scal);
    N bnscal = new N(0," NS",b_scal);
    nb64._subs.push(bnscal);
    N b_nil = new N(0," NIL",b32);
    N bxnil = new N(0,"~NIL",bnscal);
    xb32._subs.push(bxnil);
    N bxnscal = new N(0,"~NS",xnb,b_nil);
    N bxscalr = new N(0,"~SC",xb64,bxnscal);
    bxscalr.set_dual(b_scal);
    bxnscal.set_dual(bnscal);
    bxnil  .set_dual(b_nil );
    N[] xns = new N[]{b_scal,bnscal,b64,nb64,b32,nb32,b_nil,zero,two,three,bxnil,xnb32,xb32,xnb,xb64,bxnscal,bxscalr};

    // Empty signed struct surround all other structs ?
    // Can I ~() -> @{c=~...} ->...-> @{c= ...} -> () ?
    //       ~() -> @{d=~...} ->...-> @{d= ...} -> () ?
    // NO: Crossing Nil through the ()->n()->C/D@{} path.
    // Means directly above/below @{c=+/-Scalar} must be +/-Scalar.
    //N   mt = new N("  ()",sclr);
    //N  nmt = new N(" n()",nsclr,mt);
    //N xnmt = new N("~n()");
    //N x_mt = new N("~ ()",xnmt);
    //xnscl._subs.push(xnmt);
    //xsclr._subs.push(x_mt);
    //x_mt.set_dual( mt);
    //xnmt.set_dual(nmt);

    // Build the @{c=_} lattice
    N[] cns = lattice_extender(xns,"@{c=%sint}");
    // Connect to outer lattice
    add_edge(0,  sclr, cns);
    add_edge(1, nsclr, cns);
    add_edge(10,  xnil, cns);

    // Build the @{d=_} lattice
    N[] dns = lattice_extender(xns,"@{d=%sflt}");
    // Connect to outer lattice
    add_edge(0,  sclr, dns);
    add_edge(1, nsclr, dns);
    add_edge(10,  xnil, dns);

    test(xsclr);

    // Check the lattice similar to main AA.
    // Commutativity: true by definition in this case.
    // Symmetry 1 : if A&B==MT, then ~A&~MT==~A and ~B&~MT==~B
    assert check_symmetry1();
    // Associative: (A&B)&C == A&(B&C)
    assert check_associative();
    // Symmetry 2 : if A isa B, then A.join(C) isa B.join(C)
    //              if A&B ==B, then ~(~A&~C) & ~(~B&~C) == ~(~B&~C)
    // After some algebra, this becomes: (A&B) + C == B + C; since A&B==B, this
    // is a trivial condition, except that in practice it caught a lot of
    // broken implementations.
    assert check_symmetry2();
  }

  void add_edge( int idx, N n, N[] ns ) {
    ns[idx]._subs.push(n);
    n._dual._subs.push(ns[ns.length-1-idx]);
  }

  //
  void add_edge( int idx, N n, N[]... nns ) {
    for( N[] ns : nns )
      add_edge(idx,n,ns);
  }

  // Clone and wrap the given lattice
  private static N[] lattice_extender0( N[] ns, String wrap) {
    int len = ns.length;
    N[] xns = new N[len];
    for( int i=0; i<len; i++ )
      xns[i] = new N(String.format(wrap, ns[i]._t));

    // Edges in clones
    for( int i=0; i<len; i++ )
      for( N edge : ns[i]._subs )
        xns[i]._subs.push(xns[Util.find(ns,edge)]);
    return xns;
  }
  // Clone and wrap and dual the given lattice
  private static N[] lattice_extender( N[] ns, String wrap) {
    int len = ns.length;
    N[] xns = lattice_extender0(ns,wrap);
    // Duals
    for( int i=0; i<len>>1; i++ )
      xns[i].set_dual(xns[Util.find(ns,ns[i]._dual)]);

    return xns;
  }

  // Check symmetry:  if A&B==MT, then ~A&~MT==~A and ~B&~MT==~B
  static boolean check_symmetry1() {
    for( N n : N.NS ) {
      for( N m : N.NS ) {
        N mt = n.meet(m);
        assertSame(n._dual.meet(mt._dual), n._dual);
        assertSame(m._dual.meet(mt._dual), m._dual);
      }
    }
    return true;
  }

  static boolean check_associative() {
    for( N a : N.NS )
      for( N b : N.NS )
        for( N c : N.NS )
          assertSame(a.meet(b).meet(c),a.meet(b.meet(c)));
    return true;
  }

  // Symmetry 2 : if A isa B, then A.join(C) isa B.join(C)
  // After some algebra, this is the same as (A&B)+ C === B+C
  // Given a correct join (hence dual) this is trivial.
  static boolean check_symmetry2() {
    for( N a : N.NS ) {
      for( N b : N.NS ) {
        N mt = a.meet(b);
        if( mt==b ) {
          for( N c : N.NS ) {
            N a_c = a.join(c);
            N b_c = b.join(c);
            assertSame(a_c.meet(b_c),b_c);
          }
        }
      }
    }
    return true;
  }

  // A wholly unrelated variant of NIL: every other lattice element is NOT-NIL,
  // and has 2 bits/4 states: OR-NIL (choice of nil), AND-NIL (classic low with
  // nil), NOT-NIL (classic low not-nil), IS-NIL (and the other element is
  // ignored).  The new state is {NIL and [TypeMemPtr or TypeInt or TypeFlt]}.
  // Shows up in HM tests, where an escaped function getting called worse
  // possible external arguments knows it handles a NIL, but cannot (yet) pin
  // down that the not-nil values are TypeMemPtr or TypeFunPtr or what.
  @Test public void testLattice22() {
    N.reset();

    // Basic lattice, with ints and TypeMemPtr to some constant strings
    N _scl = new N(0," scalr");

    N _i64 = new N(0," int64",_scl);
    N _i2  = new N(0," 2    ",_i64);
    N _i3  = new N(0," 3    ",_i64);
    N xi64 = new N(0,"~int64",_i2,_i3); // Has a dual

    N _tmp = new N(0," tmp ",_scl);
    N _abc = new N(0,"\"abc\"",_tmp);
    N _def = new N(0,"\"def\"",_tmp);
    N xtmp = new N(0,"~tmp ",_abc,_def); // Has a dual

    N xscl = new N(0,"~scalr",xi64,xtmp);// Has a dual

    N[] ns = new N[]{_scl,_i64,_tmp,_i2,_i3,_abc,_def,xtmp,xi64,xscl};
    int nduals = 3; // xi64,xtmp,xscl
    int len = ns.length;

    N[] ans = lattice_extender0(ns,"%s&0"); // AND nil
    N[] nns = lattice_extender0(ns,"%s  "); // NOT nil
    N[] ens = lattice_extender0(ns,"%s=0"); // YES nil
    N[] ons = lattice_extender0(ns,"%s+0"); // OR  nil

    // Edges from corresponding elements AND is below NOT, NOT is below OR
    add_edge(nns,ans);
    add_edge(ens,ans);
    add_edge(ons,nns);
    add_edge(ons,ens);

    //----------------------------------
    // Big Single Nil is not a lattice
    //// Da Big Nil
    //N nil = new N("nil");
    //
    //// Edge from bottom of ORs to NIL, and NIL to top of ANDs
    //ons[0]._subs.push(nil);
    //nil._subs.push(ans[len-1]);

    //----------------------------------
    // Duals, outside-in for ORs and ANDs
    for( int i=0; i<len; i++ ) {
      N n = ans[len-1-i];
      if( n._t.charAt(0) == '~' )
        n.set_dual(ons[i]);
    }
    for( int i=0; i<len; i++ ) {
      N n = ons[len-1-i];
      if( n._t.charAt(0) == '~' )
        n.set_dual(ans[i]);
    }
    for( int i=0; i<len; i++ ) {
      N n = ans[i];
      if( n._dual==n )          // No dual yet, so dual to the matching ons
        n.set_dual(ons[i]);
    }

    // Duals outside-in for NOTs, YESs
    for( int i=0; i<nduals; i++ )
      nns[len-1-i].set_dual(nns[i]);
    for( int i=0; i<nduals; i++ )
      ens[len-1-i].set_dual(ens[i]);

    test(ons[len-1]);

    // Check the lattice similar to main AA.
    // Commutativity: true by definition in this case.
    // Symmetry 1 : if A&B==MT, then ~A&~MT==~A and ~B&~MT==~B
    assert check_symmetry1();
    // Associative: (A&B)&C == A&(B&C)
    assert check_associative();
    // Symmetry 2 : if A isa B, then A.join(C) isa B.join(C)
    //              if A&B ==B, then ~(~A&~C) & ~(~B&~C) == ~(~B&~C)
    // After some algebra, this becomes: (A&B) + C == B + C; since A&B==B, this
    // is a trivial condition, except that in practice it caught a lot of
    // broken implementations.
    assert check_symmetry2();

  }

  void add_edge(N[] froms, N[] tos) {
    for( int i=0; i<tos.length; i++ )
      froms[i]._subs.push(tos[i]);
  }

  void set_dual(N[] ns0, N[] ns1, int max) {
    int len = ns0.length;
    for( int i=0; i<max; i++ )
      ns0[len-1-i].set_dual(ns1[i]);
  }


  // A wholly unrelated variant of NIL: every other lattice element is NOT-NIL,
  // and has 2 bits/4 states: OR-NIL (choice of nil), AND-NIL (classic low with
  // nil), NOT-NIL (classic low not-nil), IS-NIL (and the other element is
  // ignored).  The new state is {NIL and [TypeMemPtr or TypeInt or TypeFlt]}.
  // Shows up in HM tests, where an escaped function getting called worse
  // possible external arguments knows it handles a NIL, but cannot (yet) pin
  // down that the not-nil values are TypeMemPtr or TypeFunPtr or what.

  // Using 2 versions of NIL instead of subclasses
  @Test public void testLattice22_nil2() {
    N.reset();

    // Basic lattice, with ints and TypeMemPtr to some constant strings
    N _scl = new N(0," scalr");

    N _i64 = new N(0," int64",_scl);
    N _i2  = new N(0," 2    ",_i64);
    N _i3  = new N(0," 3    ",_i64);
    N xi64 = new N(0,"~int64",_i2,_i3); // Has a dual

    N _tmp = new N(0," tmp ",_scl);
    N _abc = new N(0,"\"abc\"",_tmp);
    N _def = new N(0,"\"def\"",_tmp);
    N xtmp = new N(0,"~tmp ",_abc,_def); // Has a dual

    N xscl = new N(0,"~scalr",xi64,xtmp);// Has a dual

    N[] ns = new N[]{_scl,_i64,_tmp,_i2,_i3,_abc,_def,xtmp,xi64,xscl};
    int nduals = 3; // xi64,xtmp,xscl
    int len = ns.length;

    N[] ans = lattice_extender0(ns,"%s&0"); // AND nil
    N[] nns = lattice_extender0(ns,"%s  "); // NOT nil
    N[] ons = lattice_extender0(ns,"%s+0"); // OR  nil

    // Edges from corresponding elements AND is below NOT, NOT is below OR
    add_edge(nns,ans);
    add_edge(ons,nns);

    //----------------------------------
    N  nil = new N( "nil");
    N xnil = new N("~nil"); // NO Edge xnil->nil
    nil.set_dual(xnil);

    // Edge from xnil to AND-xscalar
    xnil._subs.push(ans[len-1]);
    // Edge from OR-scalar to YES-nil
    ons[0]._subs.push(nil);
    // This next set DOES work:
    // Edge from OR-xscalar to YES-xnil.
    ons[len-1]._subs.push(xnil);
    // Edges from YES-nil to AND-scalar
    nil._subs.push(ans[0]);
    // This next set does not work: allowing ~tmp+0 and ~int+0 to fall to xnil
    //ons[7]._subs.push(xnil);
    //ons[8]._subs.push(xnil);
    //nil._subs.push(ans[1]);
    //nil._subs.push(ans[2]);


    //----------------------------------
    // Duals, outside-in for ORs and ANDs
    for( int i=0; i<len; i++ ) {
      N n = ans[len-1-i];
      if( n._t.charAt(0) == '~' )
        n.set_dual(ons[i]);
    }
    for( int i=0; i<len; i++ ) {
      N n = ons[len-1-i];
      if( n._t.charAt(0) == '~' )
        n.set_dual(ans[i]);
    }
    for( int i=0; i<len; i++ ) {
      N n = ans[i];
      if( n._dual==n )          // No dual yet, so dual to the matching ons
        n.set_dual(ons[i]);
    }

    // Duals outside-in for NOTs, YESs
    for( int i=0; i<nduals; i++ )
      nns[len-1-i].set_dual(nns[i]);

    test(ons[len-1]);

    // Check the lattice similar to main AA.
    // Commutativity: true by definition in this case.
    // Symmetry 1 : if A&B==MT, then ~A&~MT==~A and ~B&~MT==~B
    assert check_symmetry1();
    // Associative: (A&B)&C == A&(B&C)
    assert check_associative();
    // Symmetry 2 : if A isa B, then A.join(C) isa B.join(C)
    //              if A&B ==B, then ~(~A&~C) & ~(~B&~C) == ~(~B&~C)
    // After some algebra, this becomes: (A&B) + C == B + C; since A&B==B, this
    // is a trivial condition, except that in practice it caught a lot of
    // broken implementations.
    assert check_symmetry2();

  }


  // Looking at simple unions, this one without a nil.
  //
  // The join of int and flt is [3 + 3.14] - magic constants.
  // Which means adding e.g. '2' to the lattice makes it not-a-lattice.
  
  //            ~Scalar
  //        &[~int + ~flt]          
  // &[~int + 3.14]        &[ 3 + ~flt]
  //   ~int   &[ 3 + 3.14]        ~flt 
  //        3               3.14     
  //    int   &[ 3 & 3.14]         flt
  // &[ int & 3.14]        &[ 3 &  flt]
  //        &[ int &  flt]
  //            Scalar
  @Test public void testLattice23() {
    N.reset();
    N scalar    = new N("Scalar");
    
    N _i_AND__f = new N("[ int &  flt]", scalar );
    N _i_AND_pi = new N("[ int & 3.14]",_i_AND__f);
    N _3_AND__f = new N("[  3  &  flt]",_i_AND__f);
    N _i        = new N( " int"        ,_i_AND_pi);
    N _f        = new N(        " flt" ,_3_AND__f);

    N _3_AND_pi = new N("[  3  & 3.14]",_i_AND_pi,_3_AND__f);
    N _3        = new N(  " 3 "        ,_3_AND_pi,_i);
    N _pi       = new N(        "3.14" ,_3_AND_pi,_f);
    N _3_OR_pi  = new N("[  3  + 3.14]",_3,_pi);
    
    N xi        = new N( "~int"        ,_3 );
    N xf        = new N( "~flt"        ,_pi);
    N _3_OR_xf  = new N("[  3  + ~flt]",_3_OR_pi,xf);
    N xi_OR_pi  = new N("[~int + 3.14]",_3_OR_pi,xi);
    N xi_OR_xf  = new N("[~int + ~flt]",_3_OR_xf,xi_OR_pi);
    N xscalr    = new N("~Scalar",xi_OR_xf);

    scalar   .set_dual(xscalr);
    _i_AND__f.set_dual(xi_OR_xf);
    _i_AND_pi.set_dual(xi_OR_pi);
    _3_AND__f.set_dual(_3_OR_xf);
    _i       .set_dual(xi);
    _f       .set_dual(xf);
    _3_AND_pi.set_dual(_3_OR_pi);

    test(xscalr);
  }

  // Same as testLattice23, but with an additional int constant '2'.
  // NOT A LATTICE
  
  //            ~Scalar
  //        &[~int + ~flt]          
  // &[~int + 3.14]        &[ 2 + ~flt]   &[ 3 + ~flt]  
  //   ~int   &[ 3 + 3.14]        ~flt
  //          &[ 2 + 3.14]
  //    2 3                       3.14     
  //          &[ 2 & 3.14]
  //    int   &[ 3 & 3.14]         flt
  // &[ int & 3.14]        &[ 2 &  flt]   &[ 3 &  flt]
  //        &[ int &  flt]
  //            Scalar
  @Ignore
  @Test public void testLattice23a() {
    N.reset();
    N scalar    = new N("Scalar");
    
    N _i_AND__f = new N("[ int &  flt]", scalar );
    N _i_AND_pi = new N("[ int & 3.14]",_i_AND__f);
    N _2_AND__f = new N("[  2  &  flt]",_i_AND__f);
    N _3_AND__f = new N("[  3  &  flt]",_i_AND__f);
    N _i        = new N( " int"        ,_i_AND_pi);
    N _f        = new N(        " flt" ,_2_AND__f,_3_AND__f);

    N _2_AND_pi = new N("[  2  & 3.14]",_i_AND_pi,_2_AND__f);
    N _3_AND_pi = new N("[  3  & 3.14]",_i_AND_pi,_3_AND__f);
    N _2        = new N(  " 2 "        ,_2_AND_pi,_i);
    N _3        = new N(  " 3 "        ,_3_AND_pi,_i);
    N _pi       = new N(        "3.14" ,_2_AND_pi,_3_AND_pi,_f);
    N _2_OR_pi  = new N("[  2  + 3.14]",_2,_pi);
    N _3_OR_pi  = new N("[  3  + 3.14]",_3,_pi);
    
    N xi        = new N( "~int"        ,_3, _2 );
    N xf        = new N( "~flt"        ,_pi);
    N _2_OR_xf  = new N("[  2  + ~flt]",_2_OR_pi,xf);
    N _3_OR_xf  = new N("[  3  + ~flt]",_3_OR_pi,xf);
    N xi_OR_pi  = new N("[~int + 3.14]",_3_OR_pi,_2_OR_pi,xi);
    N xi_OR_xf  = new N("[~int + ~flt]",_3_OR_xf,_2_OR_xf,xi_OR_pi);
    N xscalr    = new N("~Scalar",xi_OR_xf);

    scalar   .set_dual(xscalr);
    _i_AND__f.set_dual(xi_OR_xf);
    _i_AND_pi.set_dual(xi_OR_pi);
    _2_AND__f.set_dual(_2_OR_xf);
    _3_AND__f.set_dual(_3_OR_xf);
    _i       .set_dual(xi);
    _f       .set_dual(xf);
    _2_AND_pi.set_dual(_2_OR_pi);
    _3_AND_pi.set_dual(_3_OR_pi);

    test(xscalr);
  }

  // Simple injection of small ints into float ranges
  @Test public void testLattice24() {
    N.reset();
    N scalar    = new N("Scalar");
    
    N i64 = new N("i64", scalar );
    N f64 = new N("f64", scalar );
    
    N i32 = new N("i32", i64,f64 );
    N f32 = new N("f32", f64 );
    
    N i1  = new N("i1" , i32,f32 );
    
    N one = new N("1"  , i1 );
    N pi  = new N("3.14",f32 );

    N i1x = new N("~i1" , one );
    
    N i32x= new N("~i32", i1x );
    N f32x= new N("~f32", pi, i1x  );
    
    N i64x= new N("~i64", i32x);
    N f64x= new N("~f64", f32x,i32x);
    
    N xscalr    = new N("~Scalar",i64x,f64x);

    scalar.set_dual(xscalr);
    i64   .set_dual(i64x  );
    f64   .set_dual(f64x  );
    i32   .set_dual(i32x  );
    f32   .set_dual(f32x  );
    i1    .set_dual(i1x   );

    test(xscalr);

    // Check the lattice similar to main AA.
    // Commutativity: true by definition in this case.
    // Symmetry 1 : if A&B==MT, then ~A&~MT==~A and ~B&~MT==~B
    assert check_symmetry1();
    // Associative: (A&B)&C == A&(B&C)
    assert check_associative();
    // Symmetry 2 : if A isa B, then A.join(C) isa B.join(C)
    //              if A&B ==B, then ~(~A&~C) & ~(~B&~C) == ~(~B&~C)
    // After some algebra, this becomes: (A&B) + C == B + C; since A&B==B, this
    // is a trivial condition, except that in practice it caught a lot of
    // broken implementations.
    assert check_symmetry2();

  }

  
  // Open question for a future testLattice test:
  //
  //    Under what circumstances can 'meet' return a NIL?
  //
  // Seems obvious that nil.meet(nil) returns nil.  What about nil.meet(0:int)?
  // nil.meet([0]->obj)?  Current theory is: Yes, provided nil was an input and
  // strictly not otherwise.  Denies eg: [~0+4]->~obj.meet(~[0+2]->~obj) which
  // you might imagine returning [~0]->~obj - the nil inverse.  How about
  // [0]->obj.meet([0]->obj) - two instances of not-nil-but-nil-equivalents?
  // Same question for 0:int.meet(0:int) and 0:flt.meet(0:int).  And then the
  // same question for: 0:int.meet([0]->obj)?
  //
}
