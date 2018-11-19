package com.cliffc.aa;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import org.junit.Test;
import org.junit.Ignore;

import java.util.BitSet;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class TestLattice {
  private static class N {
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
    N(String t, N... subs) {
      _id = ID++;
      _t=t;
      _subs = new Ary<>(subs);
      _sups = new Ary<>(new N[1],0); // Fill in later
      _reaches = new BitSet();
      _dual = this;
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
      System.out.println(new SB().i(indent).toString()+toString());
      for( N sub : _subs ) sub.walk_print(bs,indent+1);
    }
    @Override public String toString() {
      SB sb = new SB().p(_t).p(" -> ");
      for( N sub : _subs ) sb.p(sub._t).p(" ");
      return sb.toString();
    }
    // top-down find extra edges
    boolean walk_min_edge( int vs[], N sup ) {
      vs[_id]++;
      if( sup != null ) {
        for( N sup0 : _sups )
          if( sup._reaches.get(sup0._id) ) {
            System.out.println("Edge "+sup0._t+" -> "+_t+" and also path "+sup0._t+" ... -> "+sup._t+" -> "+_t);
            return false;
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
  }

  // Complete the lattice and test it
  private static void test(N top) {
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
  // instead of being unique.  Similarly meet of {~oop,null} is not well
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
    N i64 = new N("{i64}"   ,oop0);
    
    N i8  = new N("{i8}"    ,i64);
    N str = new N("str"     ,str0);
    N abc = new N("abc"     ,str);
    N def = new N("def"     ,str);
    N t7  = new N("{7}"     ,i8);
    N t0  = new N("{nil}"   ,i8);
    N nil = new N("nil"     ,str0,num);
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
}
