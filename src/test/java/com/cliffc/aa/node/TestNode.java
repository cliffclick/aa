package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.NonBlockingHashMapLong;
import com.cliffc.aa.util.Util;
import org.junit.Ignore;
import org.junit.Test;

import java.util.Arrays;

public class TestNode {
  // A private set of input nodes to feed into each tested Node - a hand-rolled
  // sub-graph.
  private ConNode[] _ins;
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
  private int[][] make_minimal_graph(Type[] alltypes) {

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

  @Test @Ignore public void testMonotonic() {
    // All The Types we care to reason about.  There's an infinite number of
    // Types, but mostly are extremely similar - so we limit ourselves to a
    // subset which has at least one of unique (Java) subtype, plus some
    // variations inside the more complete (Java) Types.
    _subtypes = make_subtypes(Type.ALL_TYPES());
    
    // Build a minimal spanning sub-Type tree from the set of sample types.
    // We'll use this to know which other types sub-Type this type... and thus be
    // more efficient in testing all Types which subtype another Type.
    _min_subtypes = make_minimal_graph(Type.ALL_TYPES());

    // Per-node-type cached value() results
    _values = new NonBlockingHashMapLong<>();

    // Setup to compute a value() call: we need a tiny chunk of Node graph with
    // known inputs.
    _gvn = new GVNGCM();
    _ins = new ConNode[4];
    for( int i=0; i<_ins.length; i++ )
      _ins[i] = new ConNode<Type>(Type.SCALAR);
    
    test1monotonic_NXX(new PrimNode.AddF64());
    //test1monotonicType(0,new ConNode(Type.SCALAR));
    //test1monotonicType(2,new CastNode(_ins[0],_ins[1],Type.SCALAR));

    
  }

  // Fill a Node with {null,edge,edge} and start the search
  private void test1monotonic_NXX(Node n) {
    assert n._defs._len==0;
    n.add_def( null  );
    n.add_def(_ins[1]);
    n.add_def(_ins[2]);
    _values.clear();
    set_value_type(n,0,0,0,0,xx(0,0,0,0));
    test1monotonic(n,0,0,0,0);
  }
  
  // Recursively walk all combos of types, compute values and verifying
  // monotonicity
  private void test1monotonic(final Node n, final int i0, final int i1, final int i2, final int i3 ) {
    Type vn = get_value_type(i0,i1,i2,i3);
    if( n._defs.at(0)!=null ) {
      int[] at0s = _min_subtypes[i0];
      for( int i=0; i<at0s.length; i++ ) {
        // Check for this type combo from the cache
        long xx = xx(i ,i1,i2,i3);
        Type vm = _values.get(xx);
        boolean old = vm == null;
        if( vm == null ) vm = set_value_type(n,at0s[i],i1,i2,i3,xx);
        // The major monotonicity assert
        assert vn.isa(vm);
        if( !old ) 
          throw AA.unimpl(); // Recurse
      }
    }

    // CNC - not afraid of O(65^2), all combos of 2 types to e.g. AddF64Node.
    // But yes getting afraid of O(64^4), all combos to e.g. CallNode; needs a
    // control, a function, and some args.  But the control is limited to 2,
    // and the function is not evaled.  So have a value_pre_check call which
    // checks all args for sanity.  Here, we cut off the search.  During normal
    // GVN operations we flag an assert for insane args.
    
    int[] at1s = _min_subtypes[i1];
    for( int i=0; i<at1s.length; i++ ) {
      long xx = xx(i0,at1s[i] ,i2,i3);
      Type vm = _values.get(xx);
      boolean old = vm == null;
      if( vm == null ) vm = set_value_type(n,at1s[i],i1,i2,i3,xx);
      // The major monotonicity assert
      assert vn.isa(vm);
      if( !old ) 
        throw AA.unimpl(); // Recurse
    }
      
    throw AA.unimpl(); // Repeat for i2,i3
    
  }

  // Get the value Type for 4 input types.  Must exist.
  private Type get_value_type(int i0, int i1, int i2, int i3) {
    long xx = xx(i0,i1,i2,i3);
    Type vt = _values.get(xx);
    assert vt!=null;
    return vt;
  }
  // Set the value Type for 4 input types.  Must not exist.
  private Type set_value_type(Node n, int i0, int i1, int i2, int i3, long xx ) {
    Type[] alltypes = Type.ALL_TYPES();
    _gvn.setype(_ins[0],_ins[0]._t = alltypes[i0]);
    _gvn.setype(_ins[1],_ins[1]._t = alltypes[i1]);
    _gvn.setype(_ins[2],_ins[2]._t = alltypes[i2]);
    _gvn.setype(_ins[3],_ins[3]._t = alltypes[i3]);
    Type vt = n.value(_gvn);
    Type old = _values.put(xx,vt);
    assert old==null;
    return vt;
  }

  private static long xx( int i0, int i1, int i2, int i3 ) {
    return i0+(i1<<8)+(i2<<16)+(i3<<24);
  }
}
