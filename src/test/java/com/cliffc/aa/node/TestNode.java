package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.NonBlockingHashMapLong;
import com.cliffc.aa.util.Util;
import org.junit.Test;

import java.util.Arrays;
import java.util.HashMap;

import static org.junit.Assert.assertEquals;

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

  // Array doubling of longs
  long[] _work = new long[1];
  int _work_len;

  // Worse-case output for a Node
  private Type _alltype;

  private int _errs;

  // temp/junk holder for "instant" junits, when debugged moved into other tests
  @Test public void testNode() {
    Type.init0(new HashMap<>());
    Env.top();
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

  private void push( long x ) {
    if( _work_len == _work.length )
      _work = Arrays.copyOf(_work,_work_len<<1);
    _work[_work_len++] = x;
  }

  private long pop() { return _work[--_work_len]; }

  // Print subtypes in RPO
  private void print( int x, int d ) {
    Type dt = _values.get(x);
    if( dt==null ) {
      _values.put(x,dt=TypeInt.con(d));
      int[] subs = _min_subtypes[x];
      for( int sub : subs )
        print(sub,d+1);
      System.out.println("#"+x+" = "+Type.ALL_TYPES()[x]+" "+d+" "+dt.getl());
    } else if( d < dt.getl() ) {
      _values.put(x,TypeInt.con(d));
      System.out.println("Shrink #"+x+" = "+Type.ALL_TYPES()[x]+" "+d+" "+dt.getl());
    }
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

  @SuppressWarnings("unchecked")
  @Test public void testMonotonic() {
    Type.init0(new HashMap<>());
    Env.top();
    assert _errs == 0;          // Start with no errors
    // All The Types we care to reason about.  There's an infinite number of
    // Types, but mostly are extremely similar - so we limit ourselves to a
    // subset which has at least one of unique subtype, plus some variations
    // inside the more complex Types.
    _subtypes = make_subtypes(Type.ALL_TYPES());

    // Build a minimal spanning sub-Type tree from the set of sample types.
    // We'll use this to know which other types sub-Type this type... and thus be
    // more efficient in testing all Types which subtype another Type.
    _min_subtypes = make_minimal_graph();

    // Add self-type in slot0 of the minimal graph, so we iterate over
    // ourselves and our children
    for( int i=0; i<_min_subtypes.length; i++ ) {
      int[] ms = _min_subtypes[i];
      int[] xs = new int[ms.length+1];
      System.arraycopy(ms,0,xs,1,ms.length);
      xs[0] = i;
      _min_subtypes[i] = xs;
    }
    

    // Per-node-type cached value() results
    _values = new NonBlockingHashMapLong<>();

    // Print the types and subtypes in a RPO
    print(0,0);
    _values.clear();

    // Setup to compute a value() call: we need a tiny chunk of Node graph with
    // known inputs.
    _gvn = new GVNGCM();
    _ins = new Node[4];
    _ins[0] = new RegionNode(null,new ConNode<>(Type.CTRL),new ConNode<>(Type.CTRL));
    for( int i=1; i<_ins.length; i++ )
      _ins[i] = new ConNode<>(Type.SCALAR);
    Node mem = new ConNode<Type>(TypeMem.MEM);
    FunNode fun_forward_ref = new FunNode("anon");

    Node unr = Env.top().lookup("+"); // All the "+" functions
    FunNode fun_plus = ((EpilogNode)unr.in(1)).fun();

    TypeMemPtr from_ptr = TypeMemPtr.make(BitsAlias.REC,TypeStruct.POINT);
    TypeMemPtr to_ptr   = TypeMemPtr.make(BitsAlias.REC,TypeName.TEST_STRUCT);
    test1monotonic(new IntrinsicNode.ConvertPtrTypeName("test",from_ptr,to_ptr,null,_ins[1],_ins[2]));


    test1monotonic(new   CallNode(false,null,_ins[0],  unr  ,mem,_ins[2],_ins[3]));
    test1monotonic(new   CallNode(false,null,_ins[0],_ins[1],mem,_ins[2],_ins[3]));
    test1monotonic(new    ConNode<Type>(          TypeInt.FALSE));
    test1monotonic(new    ConNode<Type>(          TypeStr.ABC  ));
    test1monotonic(new    ConNode<Type>(          TypeFlt.FLT64));
    test1monotonic(new   CastNode(_ins[0],_ins[1],TypeInt.FALSE));
    test1monotonic(new   CastNode(_ins[0],_ins[1],TypeStr.ABC  ));
    test1monotonic(new   CastNode(_ins[0],_ins[1],TypeFlt.FLT64));
    test1monotonic(new  CProjNode(_ins[0],0));
    test1monotonic(new EpilogNode(_ins[0],mem,_ins[1],_ins[2],fun_forward_ref,"unknown_ref"));
    test1monotonic(new EpilogNode(_ins[0],mem,_ins[1],_ins[2],fun_plus,"plus"));
    test1monotonic(new    ErrNode(_ins[0],"\nerr\n",  TypeInt.FALSE));
    test1monotonic(new    ErrNode(_ins[0],"\nerr\n",  TypeStr.ABC  ));
    test1monotonic(new    ErrNode(_ins[0],"\nerr\n",  TypeFlt.FLT64));
    test1monotonic(new    ErrNode(_ins[0],"\nerr\n",  Type   .CTRL ));
    test1monotonic(new    FunNode(new Type[]{TypeInt.INT64}));
    test1monotonic(new     IfNode(_ins[0],_ins[1]));
    for( IntrinsicNewNode prim : IntrinsicNewNode.INTRINSICS )
      test1monotonic_intrinsic(prim);
    test1monotonic(new IntrinsicNode.ConvertPtrTypeName("test",from_ptr,to_ptr,null,mem,_ins[1]));
    test1monotonic(new   LoadNode(_ins[0],_ins[1],_ins[2],0,null));
    test1monotonic(new MemMergeNode(_ins[1],_ins[2]));
    test1monotonic(new    NewNode(new Node[]{null,_ins[1],_ins[2]},TypeStruct.POINT));
    test1monotonic(new    NewNode(new Node[]{null,_ins[1],_ins[2]},TypeName.TEST_STRUCT));
    ((ConNode<Type>)_ins[1])._t = Type.SCALAR; // ParmNode reads this for _alltype
    test1monotonic(new   ParmNode( 1, "x",_ins[0],(ConNode)_ins[1],"badgc"));
    test1monotonic(new    PhiNode("badgc",_ins[0],_ins[1],_ins[2]));
    for( PrimNode prim : PrimNode.PRIMS )
      test1monotonic_prim(prim);
    test1monotonic(new   ProjNode(_ins[0],1));
    test1monotonic(new RegionNode(null,_ins[1],_ins[2]));
    test1monotonic(new  StoreNode(_ins[0],_ins[1],_ins[2],_ins[3],0,null));
    //                  ScopeNode has no inputs, and value() call is monotonic
    //                    TmpNode has no inputs, and value() call is monotonic
    test1monotonic(new   TypeNode(TypeInt.FALSE,_ins[0],_ins[1],null));
    test1monotonic(new   TypeNode(TypeStr.ABC  ,_ins[0],_ins[1],null));
    test1monotonic(new   TypeNode(TypeFlt.FLT64,_ins[0],_ins[1],null));

    assertEquals(0,_errs);
  }

  private void test1monotonic(Node n) {
    assert n._defs._len>0;
    test1monotonic_init(n);
  }

  // Fill a Node with {null,edge,edge} and start the search
  private void test1monotonic_prim(PrimNode prim) {
    PrimNode n = (PrimNode)prim.copy(_gvn);
    assert n._defs._len==0;
    n.add_def( null  );
    n.add_def(_ins[1]);
    if( n._targs._ts.length >= 2 ) n.add_def(_ins[2]);
    test1monotonic_init(n);
  }

  // Fill a Node with {null,edge,edge} and start the search
  private void test1monotonic_intrinsic(IntrinsicNewNode prim) {
    IntrinsicNewNode n = prim.copy(_gvn);
    assert n._defs._len==0;
    n.add_def( null  );
    n.add_def(_ins[1]);         // memory
    n.add_def(_ins[2]);         // arg
    if( n._targs._ts.length >= 2 ) n.add_def(_ins[3]);
    test1monotonic_init(n);
  }

  private void test1monotonic_init(final Node n) {
    System.out.println(n.xstr());
    _values.clear();
    _alltype = n.all_type();
    assert _alltype.is_con() || (!_alltype.above_center() && _alltype.dual().above_center());

    set_value_type(n,0);        // Setup worklist and first node
    Type[] all = Type.ALL_TYPES();
    while( _work_len > 0 ) {
      long xx = pop();
      int i0 = xx(xx,0), i1 = xx(xx,1), i2 = xx(xx,2), i3 = xx(xx,3);
      System.out.println(""+i0+","+i1+","+i2+","+i3+","+all[i0]+","+all[i1]+","+all[i2]+","+all[3]);
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
              if( vm == null ) vm = set_value_type(n,xxx);
              // The major monotonicity assert
              if( !vn.isa(vm) ) {
                System.out.println(n.xstr()+"("+all[xx(xx,0)]+","+all[xx(xx,1)]+","+all[xx(xx,2)]+","+all[xx(xx,3)]+") = "+vn);
                System.out.println(n.xstr()+"("+all[     x0 ]+","+all[     x1 ]+","+all[     x2 ]+","+all[     x3 ]+") = "+vm);
                _errs++;
              }
          }
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
  @SuppressWarnings("unchecked")
  private Type set_value_type(Node n, long xx ) {
    Type[] alltypes = Type.ALL_TYPES();
    _gvn.setype(_ins[0],                        alltypes[xx(xx,0)]);
    _gvn.setype(_ins[1],((ConNode)_ins[1])._t = alltypes[xx(xx,1)]);
    _gvn.setype(_ins[2],((ConNode)_ins[2])._t = alltypes[xx(xx,2)]);
    _gvn.setype(_ins[3],((ConNode)_ins[3])._t = alltypes[xx(xx,3)]);
    Type vt = n.value(_gvn);
    // Assert the alltype() bounds any value() call result.
    assert vt.isa(_alltype);
    assert _alltype.dual().isa(vt);
    Type old = _values.put(xx,vt);
    assert old==null;
    push(xx);                   // Now visit all children
    return vt;
  }

  private static long xx( int i0, int i1, int i2, int i3 ) {
    return i0+(i1<<8)+(i2<<16)+(i3<<24);
  }
  private static int xx(long xx, int i) { return (int)((xx>>(i<<3)) & 0xffL); }
}
