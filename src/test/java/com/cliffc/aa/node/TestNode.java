package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.NonBlockingHashMapLong;
import com.cliffc.aa.util.Util;
import org.junit.Test;

import java.util.Arrays;

public class TestNode {
  // A private set of input nodes to feed into each tested Node - a hand-rolled
  // sub-graph.
  private Node[] _ins;
  // A private GVN for computing value() calls.
  private GVNGCM _gvn;

  // A sparse list of all subtypes.  The outer array is the index into
  // Type.ALL_TYPES(), and the inner array is the set of immediate sub-Types
  // (again as indices into ALL_TYPES).  Numbers are sorted.
  private int[][] _subtypes;
  
  // Build a minimal spanning sub-Type tree from the set of sample types.
  // We'll use this to know which other types sub-Type this type... and thus be
  // more efficient in testing all Types which subtype another Type.  The outer
  // array is the index into Type.ALL_TYPES(), and the inner array is the set
  // of immediate sub-Types (again as indices into ALL_TYPES).
  private int[][] _min_subtypes;

  private NonBlockingHashMapLong<Type> _values;
  
  // temp/junk holder for "instant" junits, when debugged moved into other tests
  @Test public void testNode() {
    
  }

  // A sparse list of all subtypes.  The outer array is the index into
  // Type.ALL_TYPES(), and the inner array is the set of immediate sub-Types
  // (again as indices into ALL_TYPES).  ALL_TYPES is sorted by 'isa'.  Numbers
  // in subs[i] are sorted and always greater than 'i'.
  private static int[][] make_subtypes(Type[] alltypes) {
    int[][] subs = new int[alltypes.length][];
    int[] tmp = new int[alltypes.length];
    for( int i=0; i<subs.length; i++ ) {
      int len=0;
      for( int j=0; j<subs.length; j++ )
        if( i!=j && alltypes[i].isa(alltypes[j]) )
          tmp[len++]=j;         // isa numbers are sorted by increasing 'j'
      subs[i] = Arrays.copyOfRange(tmp,0,len);
    }
    return subs;
  }
  
  // Build a minimal subtype graph from the set of sample types.  We'll use
  // this to know which other types sub-Type this type... and thus be more
  // efficient in testing all Types which subtype another Type.  The outer
  // array is the index into Type.ALL_TYPES(), and the inner array is the set
  // of immediate sub-Types (again as indices into ALL_TYPES).
  private int[][] make_minimal_graph() {

    int[][] subs = new int[_subtypes.length][];
    for( int i=0; i<subs.length; i++ )
      subs[i] = _subtypes[i].clone();
    
    // For all types
    for( int i=0; i<subs.length; i++ ) {
      int[] subis = subs[i];
      // For all 'i' subtypes
      for( int j=0; j<subis.length && subis[j] != -1; j++ ) {
        int[] subjs = subs[subis[j]];
        // Pull out of subis all things found in subjs.  We have a subtype isa
        // path from i->j by design of _subtypes, and the j->k list in subjs.
        // Remove any i->k as being redundant.
        int ix = j+1, ixx = j+1; // Index to read, index to keep non-dups
        int jx = 0; // Index to read the k's
        while( ix<subis.length && jx<subjs.length ) {
          int six = subis[ix];
          int sjx = subjs[jx];
          assert sjx != -1;
          if( six==-1 ) break; // Hit end-of-array sentinel
          if( six==sjx ) { ix++; jx++; } // i->j and j->sjx and i->sjx, skip both forward
          else if( six < sjx ) subis[ixx++] = subis[ix++]; // Keep and advance
          else jx++;                                       // Advance
        }
        while( ixx < ix ) subis[ixx++] = -1; // Sentinel remaining unused elements
      }
      int ix = Util.find(subs[i],-1);
      if( ix != -1 ) subs[i] = Arrays.copyOfRange(subs[i],0,ix); // Compress extra elements
    }
    
    return subs;
  }
  
  // Major test for monotonic behavior from value() calls.  Required to prove
  // correctness & linear-time speed from GCP & a major part of GVN.iter().
  // (for GVN.iter(), ideal() calls ALSO have to be monotonic but using a
  // different metric thats harder to test for).

  // How this works: for all Node.value() calls, for all input types, if the
  // input type changes monotonically, so does the output type.  Many input
  // types are illegal for many Nodes, and can/should be asserted for by the
  // Node.  However, all legal inputs should produce an output with the
  // monotonicity invariant.

  @Test public void testMonotonic() {
    // All The Types we care to reason about.  There's an infinite number of
    // Types, but mostly are extremely similar - so we limit ourselves to a
    // subset which has at least one of unique (Java) subtype, plus some
    // variations inside the more complete (Java) Types.
    _subtypes = make_subtypes(Type.ALL_TYPES());

    // Build a minimal spanning sub-Type tree from the set of sample types.
    // We'll use this to know which other types sub-Type this type... and thus be
    // more efficient in testing all Types which subtype another Type.
    _min_subtypes = make_minimal_graph();

    // Per-node-type cached value() results
    _values = new NonBlockingHashMapLong<>();

    // Setup to compute a value() call: we need a tiny chunk of Node graph with
    // known inputs.
    _gvn = new GVNGCM();
    _ins = new Node[4];
    _ins[0] = new RegionNode(null,new ConNode<Type>(Type.CTRL),new ConNode<Type>(Type.CTRL));
    for( int i=1; i<_ins.length; i++ )
      _ins[i] = new ConNode<Type>(Type.SCALAR);
    Node mem = new ConNode<Type>(TypeMem.MEM);

    Node unr = Env.top().lookup("+"); // All the "+" functions
    test1monotonic(new   CallNode(false,null,_ins[0],mem,  unr  ,_ins[2],_ins[3]));
    test1monotonic(new   CallNode(false,null,_ins[0],mem,_ins[1],_ins[2],_ins[3]));
    test1monotonic(new    ConNode<Type>(          TypeInt.FALSE));
    test1monotonic(new    ConNode<Type>(          TypeStr.ABC  ));
    test1monotonic(new    ConNode<Type>(          TypeFlt.FLT64));
    test1monotonic(new   CastNode(_ins[0],_ins[1],TypeInt.FALSE));
    test1monotonic(new   CastNode(_ins[0],_ins[1],TypeStr.ABC  ));
    test1monotonic(new   CastNode(_ins[0],_ins[1],TypeFlt.FLT64));
    test1monotonic(new  CProjNode(_ins[0],0));
    test1monotonic(new EpilogNode(_ins[0],mem,_ins[1],_ins[2],_ins[3],1,"unknown_ref"));
    test1monotonic(new    ErrNode(_ins[0],"err",  TypeInt.FALSE));
    test1monotonic(new    ErrNode(_ins[0],"err",  TypeStr.ABC  ));
    test1monotonic(new    ErrNode(_ins[0],"err",  TypeFlt.FLT64));
    test1monotonic(new    ErrNode(_ins[0],"err",  Type   .CTRL ));
    test1monotonic(new    FunNode(new Type[]{TypeInt.INT64}));
    test1monotonic(new     IfNode(_ins[0],_ins[1]));
    test1monotonic(new   LoadNode(_ins[0],_ins[1],0,null));
    test1monotonic(new    NewNode(new Node[]{null,_ins[1],_ins[2]},TypeStruct.FLDS(2)));
    test1monotonic(new    NewNode(new Node[]{null,_ins[1],_ins[2]},TypeStruct.FLDS(2),new byte[2]));
    test1monotonic(new   ParmNode( 1, "x",_ins[0],(ConNode)_ins[1],"badgc"));
    test1monotonic(new    PhiNode("badgc",_ins[0],_ins[1],_ins[2]));
    for( PrimNode prim : PrimNode.PRIMS )
      test1monotonic_prim(prim);
    test1monotonic(new   ProjNode(_ins[0],1));
    test1monotonic(new RegionNode(null,_ins[1],_ins[2]));
    //                  ScopeNode has no inputs, and value() call is monotonic
    //                    TmpNode has no inputs, and value() call is monotonic
    test1monotonic(new   TypeNode(TypeInt.FALSE,_ins[1],null));
    test1monotonic(new   TypeNode(TypeStr.ABC  ,_ins[1],null));
    test1monotonic(new   TypeNode(TypeFlt.FLT64,_ins[1],null));
    test1monotonic(new UnresolvedNode(_ins[0],_ins[1],_ins[2]));
  }

  private void test1monotonic(Node n) {
    assert n._defs._len>0;
    test1monotonic_init(n);
  }
  
  // Fill a Node with {null,edge,edge} and start the search
  private void test1monotonic_prim(PrimNode prim) {
    PrimNode n = prim.copy();
    assert n._defs._len==0;
    n.add_def( null  );
    n.add_def(_ins[1]);
    if( n._targs._ts.length >= 2 ) n.add_def(_ins[2]);
    test1monotonic_init(n);
  }
  
  private void test1monotonic_init(final Node n) {
    _values.clear();
    set_value_type(n,0);
    test1monotonic(n,0);
  }
  
  // Recursively walk all combos of types, compute values and verifying
  // monotonicity
  private void test1monotonic(final Node n, final long xx) {
    Type[] all = Type.ALL_TYPES();
    Type vn = get_value_type(xx);
    // Subtypes in 4 node input directions
    int[] stx0 = stx(n,xx,0);
    int[] stx1 = stx(n,xx,1);
    int[] stx2 = stx(n,xx,2);
    int[] stx3 = stx(n,xx,3);

    for( int x0 : stx0 )
      for( int x1 : stx1 )
        for( int x2 : stx2 )
          for( int x3 : stx3 ) {
            // Check for this type combo from the cache
            long xxx = xx(x0,x1,x2,x3);
            Type vm = _values.get(xxx);
            boolean visited = vm != null;
            if( !visited ) vm = set_value_type(n,xxx);
            // The major monotonicity assert
            if( !vn.isa(vm) ) {
              System.out.println(n.xstr()+"("+all[xx(xx,0)]+","+all[xx(xx,1)]+","+all[xx(xx,2)]+","+all[xx(xx,3)]+") = "+vn);
              System.out.println(n.xstr()+"("+all[     x0 ]+","+all[     x1 ]+","+all[     x2 ]+","+all[     x3 ]+") = "+vm);
            }
            if( !visited ) test1monotonic(n,xxx); // Recurse
          }
  }

  private static int[] stx_any = new int[]{0};
  private int[] stx(final Node n, long xx, int i) {
    if( i >= n._defs._len || n.in(i) == null ) return stx_any;
    return _min_subtypes[xx(xx,i)];
  }

  // Get the value Type for 4 input types.  Must exist.
  private Type get_value_type(long xx) {
    Type vt = _values.get(xx);
    assert vt!=null;
    return vt;
  }
  // Set the value Type for 4 input types.  Must not exist.
  private Type set_value_type(Node n, long xx ) {
    Type[] alltypes = Type.ALL_TYPES();
    _gvn.setype(_ins[0],                        alltypes[xx(xx,0)]);
    _gvn.setype(_ins[1],((ConNode)_ins[1])._t = alltypes[xx(xx,1)]);
    _gvn.setype(_ins[2],((ConNode)_ins[2])._t = alltypes[xx(xx,2)]);
    _gvn.setype(_ins[3],((ConNode)_ins[3])._t = alltypes[xx(xx,3)]);
    Type vt = n.value(_gvn);
    Type old = _values.put(xx,vt);
    assert old==null;
    return vt;
  }

  private static long xx( int i0, int i1, int i2, int i3 ) {
    return i0+(i1<<8)+(i2<<16)+(i3<<24);
  }
  private static int xx(long xx, int i) { return (int)((xx>>(i<<3)) & 0xffL); }
}
