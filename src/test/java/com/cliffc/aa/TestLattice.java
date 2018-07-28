package com.cliffc.aa;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import org.junit.Test;
import org.junit.Ignore;

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
    for( N a : N.NS )
      for( N b : N.NS ) if( a._id < b._id ) {
        BitSet bs = (BitSet)a._reaches.clone();
        bs.and(b._reaches);
        int cnt = bs.cardinality();
        int max = -1, max2 = -1;
        for( int x=bs.nextSetBit(0); x>=0; x=bs.nextSetBit(x+1) )
          if( max==-1 || N.NS.at(x)._cnt > N.NS.at(max)._cnt ) {
            max2=max=x;
          } else if( N.NS.at(x)._cnt == N.NS.at(max)._cnt )
            max2=x;
        N nmax = N.NS.at(max);
        if( nmax._cnt < cnt ) {
          System.out.println("No meet found for "+a._t+" and "+b._t+", tied candidates are: "+nmax._t+" and "+N.NS.at(max2)._t);
          
        }
      }
  }
  
  // Lattice!
  // This structure is tested to be a lattice:

  //      ~scalar
  //    ~num    ~oop+?
  //  ~int        { ~str+?, ~tup+? }
  //                { ~str, ~tup }
  //  3       0      { "abc", "def", @{x:1}, @{x:1,y:1} }
  //                { str, tup }
  //   int        { str?, tup? }
  //     num    oop?
  //        scalar

  // Notice NO {oop,~oop} as this makes the non-lattice issue; join of
  // {oop,null} is not well-defined, as it tops out as either ~str+? OR ~tup+?
  // instead of being unique.  Similarly meet of {~oop,null} is not well
  // defined, and bottoms out as either {str?} OR {tup?}.
  @Test public void testLattice0() {
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

    N i3  = new N("3",int8 );
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

  // back to field-by-field for structs; each tuple/struct has a {choice-null,
  // not-null, support-null, is-null}.  Each field is Top, field, Bot,
  // replicated for all fields separately.  Also, the nil choice is available
  // for all combos; so there are lots of variations of nil.  There is a lowest
  // nil and a highest nil.  Struct nil is different from int 0, and seeing a 0
  // probably means producing a union{0[_,_]0,0:int}
  @Test public void testLattice2() {
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
}
