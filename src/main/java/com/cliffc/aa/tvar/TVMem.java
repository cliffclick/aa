package com.cliffc.aa.tvar;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.Arrays;

import static com.cliffc.aa.AA.unimpl;

/** A type memory
 *

Theory: indexed by TVPtr.  TVPtr has no sub-parts, it's just the TVPtr.  TVPtrs
can unify, which unifies their mapping in the TVMem, which unifies the mapped
TVStruct.

Made by MProj, including Root & CallEpi.
Merged at Phi and Parm.
Passed in as arg to Call & Fun.
Store maps a TVPtr to a TVStruct (unifies on TVPtr hit).
 */
public class TVMem extends TV3 {
  private Ary<TVPtr> _ptrs; // Map pointers to Structs

  public TVMem() { _ptrs = new Ary<>(new TVPtr[1],0); }

  @Override boolean can_progress() { throw unimpl(); }

  @Override int eidx() { return TVErr.XMEM; }
  //@Override public TVMem as_mem() { return this; }
  @Override public int len() { return _ptrs._len; }  

  TV3 _sharptr(TVMem mem) { return this; }

  TVPtr ptr(int i) {
    TVPtr p0 = _ptrs.at(i);
    if( p0.unified() )        // Might collapse into a prior ptr
      throw unimpl();
    return p0;
  }

  private int find(TVPtr ptr) {
    for( int i=0; i<len(); i++ ) {
      TVPtr pi = ptr(i);
      if( pi._aliases==ptr._aliases )
        return i;
      // TODO: Do not really expect equiv classes.
      assert pi._aliases.is_empty() || !pi._aliases.overlaps(ptr._aliases);
    }
    return -1;
  }

  // Add a new ptr, growing as needed
  private boolean add_mem( TVPtr ptr, TV3 rec ) {
    int max = len();
    _ptrs.setX(max,ptr);
    if( _args==null ) _args = new TV3[_ptrs._es.length];
    else if( max >= _args.length )
      _args = Arrays.copyOf(_args,_ptrs._es.length);
    _args[max] = rec;
    rec.widen(ptr._widen,false);
    //rec.widen((byte)Math.max(_widen,ptr._widen),false);
    // Changed memory shape, move delayed-fresh updates to now
    move_delay();    
    return true;
  }
  
  // -------------------------------------------------------------
  // The public outer access point
  public boolean unify( TVPtr ptr, TV3 rec, boolean test ) {
    assert DUPS.isEmpty();
    boolean progress = _unify(ptr,rec,test);
    DUPS.clear();
    return progress;    
  }
  
  // Unify rec against all aliases.  Also, fold up any unified ptrs.
  boolean _unify( TVPtr ptr, TV3 rec, boolean test ) {
    assert !ptr.unified() && !rec.unified();
    assert rec instanceof TVLeaf || rec instanceof TVStruct || (rec instanceof TVClz clz && clz.rhs() instanceof TVStruct);
    int idx = find(ptr);
    if( idx != -1 ) 
      return arg(idx)._unify(rec,test); // Unify the mem struct
    // Add a new ptr, growing as needed
    return test || add_mem(ptr,rec);
  }
  
  @Override boolean _unify_impl( TV3 tv3 ) {
    TVMem tmem = (TVMem)tv3;     // Invariant when called
    for( int i=0; i<len(); i++ ) // Aliases in this unified into that
      tmem._unify(ptr(i),arg(i),false);
    return true;                // Always return true here
  }

  @Override public void _union_impl( TV3 tv3 ) { }
  

  // -------------------------------------------------------------
  @Override boolean _fresh_unify_impl(TV3 tv3, boolean test) {
    TVMem tmem = (TVMem)tv3;     // Invariant when called
    boolean progress = false;
    for( int i=0; i<len(); i++ ) // Aliases in this unified into that
      progress |= _fresh_unify_impl(tmem,ptr(i),arg(i),test);
    return progress;
  }
  private static boolean _fresh_unify_impl(TVMem tmem, TVPtr fptr, TV3 frec, boolean test) {
    int idx = tmem.find(fptr);
    if( idx != -1 ) 
      return frec._fresh_unify(tmem.arg(idx),test); // Unify the mem struct
    return test || tmem.add_mem(fptr,frec._fresh());
  }

  
  // -------------------------------------------------------------
  @Override boolean _trial_unify_ok_impl( TV3 tv3, boolean extras ) {
    TVMem tmem = (TVMem)tv3;      // Invariant when called    
    for( int i=0; i<len(); i++ )
      for( int j=0; j<tmem.len(); j++ )
        throw unimpl();
    return true;
  }
  @Override boolean _exact_unify_impl( TV3 tv3 ) {
    TVMem mem = (TVMem)tv3;
    // All pointers must match, and new pointers must match
    if( _ptrs._len != mem._ptrs._len ) return false;
    throw unimpl();
  }

  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) { throw unimpl(); }
  @Override void _widen( byte widen ) {
    for( int i=0; i<len(); i++ )
      arg(i).widen(widen,false);
  }
  @Override public TVMem copy() {
    TVMem mem = (TVMem)super.copy();
    mem._ptrs = _ptrs.deepCopy();
    return mem;
  }
  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    sb.p("[[ ");
    for( int i=0; i<len(); i++ ) {
      _ptrs.at(i)._aliases.str(sb).p('=');
      if( _args==null ) sb.p("!!!");
      else _args[i]._str(sb,visit,dups,debug).p(',');
    }
    return sb.unchar().p("]]");
  }
  
}
