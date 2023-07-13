package com.cliffc.aa;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.Util;
import java.util.Arrays;
import org.junit.Ignore;
import org.junit.Test;

import static org.junit.Assert.*;
import com.cliffc.aa.TestLattice.N;
import static com.cliffc.aa.AA.unimpl;

public class TestMakeType {
  public N _ntop, _nbot;

  @Test public void testMakeType() {
    N.reset();


    TCon F2 = new TCon("2.14");
    TCon F3 = new TCon("3.14");
    TOR FLT = new TOR("~flt64","flt64",F2,F3);
    
    TOR SCALAR = new TOR("XSCALAR","SCALAR",FLT);
    TNilWrap MEGA_NILS = new TNilWrap("MEGA_HI_NIL","MEGA_LO_NIL",SCALAR);
    
    
    TestMakeType CTRL = new TWrap("XCTRL","CTRL",null);
    TestMakeType MEM  = new TWrap("XMEM" ,"MEM" ,null);
    
    TestMakeType ROOT = new TOR("any","all",CTRL,MEM,MEGA_NILS);
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

  // Top -> ~nil/NIL  -> all AND-nil classes -> Bot   ?, AND-nil
  // Top -> all OR-nil  classes -> xnil/XNIL -> Bot  +0, OR -nil
  // Top ->         NOT-nil classes          -> Bot      NOT-nil
  public static final class TNilWrap extends TestMakeType {
    public final TestMakeType _in;
    public TNilWrap(String top, String bot, TestMakeType in ) {

      N[] lattice = in.gather_lattice();
      N[] or_not = TestLattice.lattice_extender(lattice,"%s+0","%s");
      N[] OR_s = Arrays.copyOfRange(or_not,0,lattice.length);
      N[] NOTS = Arrays.copyOfRange(or_not,lattice.length,or_not.length);
      throw com.cliffc.aa.AA.unimpl();

      
    }
  }
}


