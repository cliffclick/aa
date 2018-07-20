package com.cliffc.aa;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import org.junit.Test;

import java.util.BitSet;

import static org.junit.Assert.assertTrue;

public class TestLattice {
  private static class N {
    private static int ID=0;
    static Ary<N> NS=new Ary<>(new N[1],0);
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
      for( N sub : _subs ) {
        if( sub._dual._subs.find(_dual) == -1 ) {
          System.out.println(""+_t+" -> "+sub._t+"; expect "+sub._dual._t+" -> "+_dual._t);
          return false;
        }
      }
      for( N sub : _subs ) if( !sub.walk_dual(bs) ) return false;
      return true;
    }
    
  }

  // Lattice!
  // This structure is tested to be a lattice:

  // oop? -> {str?,tup?} -> { null, string constants, tuple constants } -> {~str+?,~tup+?} -> ~oop+?
  
  // Notice NO {oop,~oop} as this makes the non-lattice issue; meet of
  // {oop,null} is not well-defined, as it tops out as either {~str+?,~tup+?}
  // instead of being unique.
  @Test public void testLattice0() {
    N  oop0= new N( "oop?");
    N  str0= new N( "str?",oop0);
    N  tup0= new N( "tup?",oop0);
    N  str = new N( "str" ,str0);
    N  tup = new N( "tup" ,tup0);
    N  nil = new N( "0",str0,tup0);
    N  abc = new N( "\"abc\"",str);
    N  def = new N( "\"def\"",str);
    N  flx = new N( "@{x}"   ,tup);
    N  fly = new N( "@{y}"   ,tup);
    N  strx= new N("~str" ,abc,def);
    N  tupx= new N("~tup" ,flx,fly);
    N  str_= new N("~str+0",strx,nil);
    N  tup_= new N("~tup+0",tupx,nil);
    N  oop_= new N("~oop+0",str_,tup_);
    // Mark the non-centerline duals
    oop0.set_dual(oop_);
    str0.set_dual(str_);
    tup0.set_dual(tup_);
    str .set_dual(strx);
    tup .set_dual(tupx);
    N top = oop_;
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
    for( N a : N.NS )
      for( N b : N.NS ) if( a._id < b._id ) {
        BitSet bs = (BitSet)a._reaches.clone();
        bs.and(b._reaches);
        int cnt = bs.cardinality();
        int max=-1;
        for( int x=bs.nextSetBit(0); x>=0; x=bs.nextSetBit(x+1) )
          if( max==-1 || N.NS.at(x)._cnt > N.NS.at(max)._cnt )
            max=x;
        if( N.NS.at(max)._cnt < cnt ) {
          System.out.println("No meet found for "+a._t+" and "+b._t);
        }
      }
  }
}
