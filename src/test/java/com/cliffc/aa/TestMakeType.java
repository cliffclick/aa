package com.cliffc.aa;

import com.cliffc.aa.TestLattice.N;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.Util;
import org.junit.Test;

public class TestMakeType {
  public N _ntop, _nbot;

  @Test public void testMakeType() {
    N.reset();

    TCon F2 = new TCon("2.14");
    TCon F3 = new TCon("3.14");
    TOR FLT = new TOR("~flt64","flt64",F2,F3);
    
    TCon I2 = new TCon("2");
    TCon I3 = new TCon("3");
    TOR INT64 = new TOR("~int64","int64",I2,I3);

    // TODO:
    // Add TFP
    // Add Struct
    // Add TMP
    // Add TMEM
    
    TestMakeType SCALAR = new TOR("XSCALAR","SCALAR",FLT,INT64);
    TNilWrap NIL_SCALARS = new TNilWrap(SCALAR);
    
    
    TestMakeType CTRL = new TWrap("XCTRL","CTRL",null);
    TestMakeType MEM  = new TWrap("XMEM" ,"MEM" ,null);

    TestMakeType ROOT = new TOR("any","all",CTRL,MEM,NIL_SCALARS);
    TestLattice.test(ROOT._ntop);

        // Check the lattice similar to main AA.
    // Commutativity: true by definition in this case.
    // Symmetry 1 : if A&B==MT, then ~A&~MT==~A and ~B&~MT==~B
    assert TestLattice.check_symmetry1();
    // Associative: (A&B)&C == A&(B&C)
    assert TestLattice.check_associative();
    // Symmetry 2 : if A isa B, then A.join(C) isa B.join(C)
    //              if A&B ==B, then ~(~A&~C) & ~(~B&~C) == ~(~B&~C)
    // After some algebra, this becomes: (A&B) + C == B + C; since A&B==B, this
    // is a trivial condition, except that in practice it caught a lot of
    // broken implementations.
    assert TestLattice.check_symmetry2();
  }

  // Gather the lattice elements into an array, sorted breadth-first
  N[] gather_lattice() {
    Ary<N> ns    = new Ary<>(new N[1],0);
    Ary<N> work1 = new Ary<>(new N[1],0);
    Ary<N> work2 = new Ary<>(new N[1],0);
    work1.push(_ntop);
    while( true ) {
      while( !work1.isEmpty() ) {
        N n = work1.pop();
        if( ns.find(n)== -1 ) {
          ns.push(n);
          for( N nx : n._subs )
            work2.push(nx);
        }
      }
      if( work2.isEmpty() ) break;
      Ary<N> tmp = work1;
      work1 = work2;
      work2 = tmp;
      work2.clear();
    }
    
    return ns.asAry();
  }

  public static final class TCon extends TestMakeType {
    final String _con;
    public TCon(String con) {
      _con = con;
      _ntop = _nbot = new N(con);
      // No call to set_dual since centerline
    }
  }
  
  // Wrap a type with another
  public static final class TWrap extends TestMakeType {
    public final TestMakeType _in;
    public TWrap(String top, String bot, TestMakeType in ) {
      _in = in;
      _nbot = new N(bot);       // To be filled in later
      N ntop = in==null ? _nbot : in._ntop;
      if( in!=null ) {
        assert in._nbot._subs._len==0;
        in._nbot._subs.push(_nbot);
      }
      _ntop = new N(top,ntop);
      _nbot.set_dual(_ntop);
    }
  }

  // Wrap a set of types.  You get to pick one.
  public static final class TOR extends TestMakeType {
    public final TestMakeType[] _ins;
    public TOR(String top, String bot, TestMakeType... ins ) {
      assert ins.length>0;      // Use wrapper for empty list
      _ins = ins;
      _nbot = new N(bot);       // To be filled in later
      N[] tops = new N[ins.length];
      for( int i=0; i<ins.length; i++ ) {
        TestMakeType in = ins[i];
        assert in._nbot._subs._len==0;
        in._nbot._subs.push(_nbot);
        tops[i] = in._ntop;
      }
      _ntop = new N(top,tops);
      _nbot.set_dual(_ntop);
    }
  }

  // Take a SESE lattice, and clone/wrap it as follows:
  
  // Top -> ~nil/NIL  -> all AND-nil classes -> Bot   ?, AND-nil
  // Top -> all OR-nil  classes -> xnil/XNIL -> Bot  +0, OR -nil
  // Top ->         NOT-nil classes          -> Bot      NOT-nil


  // Top is actually the top from OR -nil
  // Bot is actually the bot from AND-nil
  
  // The original lattice is cloned twice; the OR copy points node-by-node to
  // the NOT copy, which points node-by-node to the AND copy.  NIL is inserted
  // above the AND copy, and XNIL below the OR copy.
  public static final class TNilWrap extends TestMakeType {
    public final TestMakeType _in;
    public TNilWrap(TestMakeType in ) {
      _in = in;

      // Clone twice and edges from ORs -> NOTs -> ANDs
      N[] NOTs = in.gather_lattice();
      N[] OR_s = clone(NOTs);
      N[] ANDs = clone(NOTs);
      add_edge(OR_s,NOTs);
      add_edge(NOTs,ANDs);

      // Insert nil
      N nil = new N("nil");
      add_edge(nil,ANDs[0]);
      add_edge(OR_s[0],nil);

      // Insert xnil
      int len = ANDs.length;
      N xnil = new N("xnil");
      add_edge(xnil,ANDs[len-1]);
      add_edge(OR_s[len-1],xnil);
      nil.set_dual(xnil);

      // top/bot hooks
      _ntop = OR_s[0];
      _nbot = ANDs[len-1];

      // Duals inside out.  This is complicated because of constants in the original NOTs set.
      // The clone preserved their order, but we need to reverse the clones order.
      for( int i=0; i<len; i++ ) {
        N d0 = ANDs[i];
        if( NOTs[i]._dual==NOTs[i] ) { // Centerline constant 
          d0.set_dual(OR_s[i]);        // Dual matches AND-vs-OR
        } else {
          String s = NOTs[i]._dual._t;
          N d1 = find(OR_s,s);
          d0._dual = d1;
          d1._dual = d0;
        }
      }
      
      rename(OR_s,"%s+0");
      rename(NOTs,"n%s");
    }

    static N find(N[] ns, String s) {
      for( N n : ns )
        if( s.equals( n._t ) )
          return n;
      return null;
    }
    
    // Clone a SESE lattice, preserving all internal edges.
    // Input (and output) are sorted breadth-first.
    static N[] clone( N[] ns ) {
      N[] xs = new N[ns.length];
      for( int i=0; i<ns.length; i++ )
        xs[i] = new N(ns[i]._t);
      for( int i=0; i<ns.length; i++ )
        for( N edge : ns[i]._subs )
          xs[i]._subs.push(xs[Util.find(ns,edge)]);
      return xs;
    }

    static void rename( N[] ns, String format ) {
      for( N n : ns ) 
        n._t = String.format(format, n._t);
    }

    // Add edges from set 0 to set 1
    static void add_edge( N[] ns0, N[] ns1 ) {
      for( int i=0; i<ns0.length; i++ )
        ns0[i]._subs.push(ns1[i]);
    }

    static void add_edge( N n, N m ) { n._subs.push(m); }
  }
}
