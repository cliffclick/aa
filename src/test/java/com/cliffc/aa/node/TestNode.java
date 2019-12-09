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

  // Types being used for testing
  private Type[] _alltypes;

  // A sparse list of all subtypes.  The outer array is the index into
  // Type._alltypes(), and the inner array is the set of immediate sub-Types
  // (again as indices into _alltypes).  Numbers are sorted.
  private int[][] _subtypes;

  // Build a minimal spanning sub-Type tree from the set of sample types.
  // We'll use this to know which other types sub-Type this type... and thus be
  // more efficient in testing all Types which subtype another Type.  The outer
  // array is the index into Type._alltypes(), and the inner array is the set
  // of immediate sub-Types (again as indices into _alltypes).
  private int[][] _min_subtypes;

  private NonBlockingHashMapLong<Type> _values;
  private static long hash( long h ) {
    h ^= (h>>>20) ^ (h>>>12);
    h ^= (h>>> 7) ^ (h>>> 4);
    h += h<<7; // smear low bits up high, for hashcodes that only differ by 1
    return h;
  }
  private Type get( long h ) { return _values.get(hash(h)); }
  private Type put( long h, Type t ) { return _values.put(hash(h),t); }

  // Array doubling of longs
  private long[] _work = new long[1];
  private int _work_len;

  // Worse-case output for a Node
  private Type _alltype;

  private int _errs;

  // temp/junk holder for "instant" junits, when debugged moved into other tests
  @Test public void testNode() {
    Type.init0(new HashMap<>());
    Env.top();
  }

  // A sparse list of all subtypes.  The outer array is the index into
  // _alltypes, and the inner array is the set of immediate sub-Types
  // (again as indices into _alltypes).  _alltypes is sorted by 'isa'.  Numbers
  // in subs[i] are sorted and always greater than 'i'.
  private int[][] make_subtypes() {
    int[][] subs = new int[_alltypes.length][];
    int[] tmp = new int[_alltypes.length];
    for( int i=0; i<subs.length; i++ ) {
      int len=0;
      for( int j=0; j<subs.length; j++ )
        if( i!=j && _alltypes[i].isa(_alltypes[j]) )
          tmp[len++]=j;         // isa numbers are sorted by increasing 'j'
      subs[i] = Arrays.copyOfRange(tmp,0,len);
    }
    return subs;
  }

  // Build a minimal subtype graph from the set of sample types.  We'll use
  // this to know which other types sub-Type this type... and thus be more
  // efficient in testing all Types which subtype another Type.  The outer
  // array is the index into Type._alltypes(), and the inner array is the set
  // of immediate sub-Types (again as indices into _alltypes).
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
    Type dt = get(x);
    if( dt==null ) {
      put(x,dt=TypeInt.con(d));
      int[] subs = _min_subtypes[x];
      for( int sub : subs )
        print(sub,d+1);
      System.out.println("#"+x+" = "+_alltypes[x]+" "+d+" "+dt.getl());
    } else if( d < dt.getl() ) {
      put(x,TypeInt.con(d));
      System.out.println("Shrink #"+x+" = "+_alltypes[x]+" "+d+" "+dt.getl());
    }
  }


  // Major test for monotonic behavior from value() calls.  Required to prove
  // correctness & linear-time speed from GCP & a major part of GVN.iter().
  // (for GVN.iter(), ideal() calls ALSO have to be monotonic but using a
  // different metric that is harder to test for).

  // How this works: for all Node.value() calls, for all input types, if the
  // input type changes monotonically, so does the output type.  Many input
  // types are illegal for many Nodes, and can/should be asserted for by the
  // Node.  However, all legal inputs should produce an output with the
  // monotonicity invariant.

  public static void main( String[] args ) { new TestNode().testMonotonic();  }
  @SuppressWarnings("unchecked")
  @Test public void testMonotonic() {
    Type.init0(new HashMap<>());
    Env.top();
    assert _errs == 0;          // Start with no errors

    // Types we are testing
    _alltypes = Type.ALL_TYPES();
    // A subset used to help diagnose this algorithm.
    //Type[] ts = new Type[] {
    //  Type.ALL,Type.ANY,Type.CTRL,Type.XCTRL, Type.SCALAR, Type.XSCALAR, Type.NSCALR, Type.XNSCALR,
    //  Type.NUM, Type.XNUM, Type.NIL
    //};
    //for( int i=0; i<ts.length; i++ )
    //  for( int j=i+1; j<ts.length; j++ )
    //    if( ts[j].isa(ts[i]) ) { Type tmp = ts[i]; ts[i] = ts[j]; ts[j] = tmp; }
    //_alltypes = ts;

    // All The Types we care to reason about.  There's an infinite number of
    // Types, but mostly are extremely similar - so we limit ourselves to a
    // subset which has at least one of unique subtype, plus some variations
    // inside the more complex Types.
    _subtypes = make_subtypes();

    // Build a minimal spanning sub-Type tree from the set of sample types.
    // We'll use this to know which other types sub-Type this type... and thus be
    // more efficient in testing all Types which subtype another Type.
    _min_subtypes = make_minimal_graph();

    // Per-node-type cached value() results
    _values = new NonBlockingHashMapLong<Type>(128*1024*1024,false);

    // Print the types and subtypes in a RPO
    //print(0,0);
    //_values.clear(true);

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
    FunNode fun_plus = ((FunPtrNode)unr.in(1)).fun();
    RetNode ret = fun_plus.ret();
    CallNode call = new CallNode(false,null,unr);

    TypeMemPtr from_ptr = TypeMemPtr.make(BitsAlias.REC,TypeStruct.POINT);
    TypeMemPtr to_ptr   = TypeMemPtr.make(BitsAlias.REC,TypeName.TEST_STRUCT);

    // Testing 1 set of types into a value call.
    // Comment out when not debugging.
    Type rez = test1jig(new CastNode(_ins[0],_ins[1],TypeMemPtr.STRPTR),
            Type.CTRL,Type.NUM,Type.ANY,Type.ANY);

    // Cast(flt) ==>
    //   ~nScalar ^ flt = ~nScalar
    //     nil    ^ flt =   0
    // BUT ~nScalar isa nil, but ~nScalar !isa! 0
    // WHY ~nScalar isa nil????  ... should fall to smallest value below nil... that still works for ints & ptrs
    //
    //   nil  ^ *[4] ==> *[+0+4]    // picks up nil choice
    // Number ^ *[4] ==> ~nScalar   // nil isa Number, but *[0+4] !isa! ~nScalar
    //
    // PLAN B: nil isa many_things, nothing isa nil because its supposed to be
    // outside the lattice.  Just weaken asserts around nil?

    // All the Nodes, all Values, all Types
    test1monotonic(new   CallNode(false,null,_ins[0],  unr  ,mem,_ins[2],_ins[3]));
    test1monotonic(new   CallNode(false,null,_ins[0],_ins[1],mem,_ins[2],_ins[3]));
    test1monotonic(new CallEpiNode(call,ret,_ins[1])); // CallNode, then some count of RetNode
    test1monotonic(new    ConNode<Type>(          TypeInt.FALSE));
    test1monotonic(new    ConNode<Type>(          TypeStr.ABC  ));
    test1monotonic(new    ConNode<Type>(          TypeFlt.FLT64));
    // Cannot cast-to-NIL - can only move away from NIL
    //test1monotonic(new   CastNode(_ins[0],_ins[1],TypeInt.FALSE));
    test1monotonic(new   CastNode(_ins[0],_ins[1],Type.NSCALR));
    test1monotonic(new   CastNode(_ins[0],_ins[1],TypeFlt.FLT64));
    test1monotonic(new   CastNode(_ins[0],_ins[1],TypeMemPtr.STRPTR));
    test1monotonic(new   CastNode(_ins[0],_ins[1],TypeMemPtr.STR0));
    test1monotonic(new  CProjNode(_ins[0],0));
    test1monotonic(new    ErrNode(_ins[0],"\nerr\n",  TypeInt.FALSE));
    test1monotonic(new    ErrNode(_ins[0],"\nerr\n",  TypeStr.ABC  ));
    test1monotonic(new    ErrNode(_ins[0],"\nerr\n",  TypeFlt.FLT64));
    test1monotonic(new    ErrNode(_ins[0],"\nerr\n",  Type   .CTRL ));
    test1monotonic(new    FunNode(new Type[]{TypeInt.INT64}));
    test1monotonic(new FunPtrNode(ret));
    test1monotonic(new     IfNode(_ins[0],_ins[1]));
    for( IntrinsicNewNode prim : IntrinsicNewNode.INTRINSICS )
      test1monotonic_intrinsic(prim);
    test1monotonic(new IntrinsicNode.ConvertPtrTypeName("test",from_ptr,to_ptr,null,_ins[1],_ins[2]));
    test1monotonic(new   LoadNode(_ins[1],_ins[2],"x",null));
    test1monotonic(new MemMergeNode(_ins[1],_ins[2],BitsAlias.REC));
    NewNode nnn1 = new NewNode(_ins[0],false);
    nnn1.create("x",_ins[1],TypeStruct.ffinal(),_gvn);
    nnn1.create("y",_ins[2],TypeStruct.ffinal(),_gvn);
    test1monotonic(nnn1);
    NewNode nnn2 = new NewNode(_ins[0],false);
    nnn2.create("x",_ins[1],TypeStruct.ffinal(),_gvn);
    nnn2.create("y",_ins[2],TypeStruct.ffinal(),_gvn);
    nnn2.set_name(_gvn,TypeName.TEST_STRUCT);
    test1monotonic(nnn2);
    ((ConNode<Type>)_ins[1])._t = Type.SCALAR; // ParmNode reads this for _alltype
    test1monotonic(new   ParmNode( 1, "x",_ins[0],(ConNode)_ins[1],null).add_def(_ins[2]));
    test1monotonic(new    PhiNode(null,_ins[0],_ins[1],_ins[2]));
    for( PrimNode prim : PrimNode.PRIMS )
      test1monotonic_prim(prim);
    test1monotonic(new   ProjNode(_ins[0],1));
    test1monotonic(new RegionNode(null,_ins[1],_ins[2]));
    test1monotonic(new    RetNode(_ins[0],mem,_ins[1],_ins[2],fun_plus)); // ctl,mem,val,rpc,fun
    test1monotonic(new  StoreNode(_ins[0],_ins[1],_ins[2],_ins[3],(byte)0,"x",null));
    test1monotonic(new  StoreNode(_ins[0],_ins[1],_ins[2],_ins[3],(byte)1,"x",null));
    //                  ScopeNode has no inputs, and value() call is monotonic
    //                    TmpNode has no inputs, and value() call is monotonic
    test1monotonic(new   TypeNode(TypeInt.FALSE,_ins[1],null));
    test1monotonic(new   TypeNode(TypeMemPtr.ABCPTR,_ins[1],null));
    test1monotonic(new   TypeNode(TypeFlt.FLT64,_ins[1],null));

    assertEquals(0,_errs);
  }

  @SuppressWarnings("unchecked")
  private Type test1jig(final Node n, Type t0, Type t1, Type t2, Type t3) {
    _alltype = n.all_type();
    assert _alltype.is_con() || (!_alltype.above_center() && _alltype.dual().above_center());
    // Prep graph edges
    _gvn.setype(_ins[0],                        t0);
    _gvn.setype(_ins[1],((ConNode)_ins[1])._t = t1);
    _gvn.setype(_ins[2],((ConNode)_ins[2])._t = t2);
    _gvn.setype(_ins[3],((ConNode)_ins[3])._t = t3);
    return n.value(_gvn);
  }

  private void test1monotonic(Node n) {
    assert n._defs._len>0;
    test1monotonic_init(n);
  }

  // Fill a Node with {null,edge,edge} and start the search
  private void test1monotonic_prim(PrimNode prim) {
    PrimNode n = (PrimNode)prim.copy(false,_gvn);
    assert n._defs._len==0;
    n.add_def( null  );
    n.add_def(_ins[1]);
    if( n._targs._ts.length >= 2 ) n.add_def(_ins[2]);
    test1monotonic_init(n);
  }

  // Fill a Node with {null,edge,edge} and start the search
  private void test1monotonic_intrinsic(IntrinsicNewNode prim) {
    IntrinsicNewNode n = prim.copy(false,_gvn);
    assert n._defs._len==0;
    n.add_def( null  );
    n.add_def(_ins[1]);         // memory
    n.add_def(_ins[2]);         // arg
    if( n._targs._ts.length >= 2 ) n.add_def(_ins[3]);
    test1monotonic_init(n);
  }

  @SuppressWarnings("unchecked")
  private void test1monotonic_init(final Node n) {
    System.out.println(n.xstr());
    _values.clear(true);
    _alltype = n.all_type();
    assert _alltype.is_con() || (!_alltype.above_center() && _alltype.dual().above_center());

    put(0,Type.ANY);            // First args are all ANY, so is result
    push(0);                    // Init worklist

    Type[] all = _alltypes;
    long t0 = System.currentTimeMillis(), t2=t0;
    long nprobes = 0, nprobes1=0;
    while( _work_len > 0 ) {
      long xx = pop();
      Type vn = get_value_type(xx);
      int x0 = xx(xx,0), x1 = xx(xx,1), x2 = xx(xx,2), x3 = xx(xx,3);
      // Prep graph edges
      _gvn.setype(_ins[0],                        all[x0]);
      _gvn.setype(_ins[1],((ConNode)_ins[1])._t = all[x1]);
      _gvn.setype(_ins[2],((ConNode)_ins[2])._t = all[x2]);
      _gvn.setype(_ins[3],((ConNode)_ins[3])._t = all[x3]);

      // Subtypes in 4 node input directions
      int[] stx0 = stx(n,xx,0);
      for( int y0 : stx0 )
        set_value_type(n, vn, xx, xx(y0,x1,x2,x3), 0, y0, all );
      set_type(0,all[x0]);

      int[] stx1 = stx(n,xx,1);
      for( int y1 : stx1 )
        set_value_type(n, vn, xx, xx(x0,y1,x2,x3), 1, y1, all );
      set_type(1,all[x1]);

      int[] stx2 = stx(n,xx,2);
      for( int y2 : stx2 )
        set_value_type(n, vn, xx, xx(x0,x1,y2,x3), 2, y2, all );
      set_type(2,all[x2]);

      int[] stx3 = stx(n,xx,3);
      for( int y3 : stx3 )
        set_value_type(n, vn, xx, xx(x0,x1,x2,y3), 3, y3, all );
      set_type(3,all[x3]);

      nprobes1 += stx0.length+stx1.length+stx2.length+stx3.length;
      long t1 = System.currentTimeMillis();
      if( t1-t0 >= 1000 ) {
        nprobes += nprobes1;
        System.out.println("Did "+nprobes1+" in "+(t1-t0)+"msecs, worklist has "+_work_len+" states, total probes "+nprobes+", values="+_values.size());
        nprobes1=0;
        t0=t1;
      }
    }
    nprobes += nprobes1;
    System.out.println("Total probes "+nprobes+" in "+(t0-t2)+"msecs, values="+_values.size());
  }

  private void set_value_type(Node n, Type vn, long xx, long xxx, int idx, int yx, Type[] all ) {
    Type vm = get(xxx);
    if( vm == null ) {
      set_type(idx,all[yx]);
      vm = n.value(_gvn);
      // Assert the alltype() bounds any value() call result.
      assert vm.isa(_alltype);
      assert _alltype.dual().isa(vm);
      Type old = put(xxx,vm);
      assert old==null;
      push(xxx);            // Now visit all children
    }
    // The major monotonicity assert
    int x1 = xx(xx,1);
    int y1 = idx==1 ? yx : x1;
    if( vn!= vm && !vn.isa(vm) && !special_cast_exception(n,x1,y1,all) ) {
      int x0 = xx(xx,0), x2 = xx(xx,2), x3 = xx(xx,3);
      System.out.println(n.xstr()+"("+all[x0]+","+all[x1]+","+all[x2]+","+all[x3]+") = "+vn);
      System.out.println(n.xstr()+"("+all[idx==0?yx:x0]+","+all[idx==1?yx:x1]+","+all[idx==2?yx:x2]+","+all[idx==3?yx:x3]+") = "+vm);
      _errs++;
    }
  }

  // CastNode does a JOIN, sometimes with NIL.  This leads to weird
  // crossing-nil cases that we end up checking for, which should not matter
  // For Real.  Example: Cast to a "str" which is really a *[4]str.  Argument
  // is either a NIL or a Number.  This is a basic distributivity property:
  // If A-isa-B, then A.join(C) -isa- B.join(C).
  //  NIL-isa-Number.  Thus NIL.join(str) -isa- Number.join(str).
  // NIL-JOIN-*[4]str yields *[0+4+]str? (high string-or-NIL choice).
  // Number-JOIN-*[4]str yields ~nScalar (because the Cast is in-error, mixing
  // numbers and pointers).  Since NIL-isa-Number, we expect
  // *[0+4+]str?-isa-~nScalar (via basic distributivity property).
  //
  private boolean special_cast_exception(Node n, int x1, int y1, Type[] all ) {
    //return n instanceof CastNode && (all[x1]==Type.NIL || all[y1]==Type.NIL);
    return false;
  }

  @SuppressWarnings("unchecked")
  private void set_type(int idx, Type tyx) {
    if( idx > 0 ) ((ConNode)_ins[idx])._t = tyx;
    _gvn.setype(_ins[idx], tyx);
  }

  private static int[] stx_any = new int[]{};
  private int[] stx(final Node n, long xx, int i) {
    if( i >= n._defs._len || n.in(i) == null ) return stx_any;
    return _min_subtypes[xx(xx,i)];
  }

  // Get the value Type for 4 input types.  Must exist.
  private Type get_value_type(long xx) {
    Type vt = get(xx);
    assert vt!=null;
    return vt;
  }

  private static long xx( int i0, int i1, int i2, int i3 ) {
    return i0+(i1<<8)+(i2<<16)+(i3<<24);
  }
  private static int xx(long xx, int i) { return (int)((xx>>(i<<3)) & 0xffL); }
}
