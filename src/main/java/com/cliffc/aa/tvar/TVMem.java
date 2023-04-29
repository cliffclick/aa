package com.cliffc.aa.tvar;

import com.cliffc.aa.Oper;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.*;

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
  private int _max;             // Max set of in-use flds/args
  private final Ary<TVPtr> _ptrs;

  public TVMem() { _max = 0; _ptrs = new Ary<>(new TVPtr[1],0); }

  @Override boolean can_progress() { throw unimpl(); }

  @Override int eidx() { return TVErr.XMEM; }
  //@Override public TVMem as_mem() { return this; }
  @Override public int len() { return _max; }  

  // Unify rec against all aliases.  Also, fold up any unified ptrs.
  public boolean unify( TVPtr ptr, TVStruct rec, boolean test ) {
    assert !ptr.unified() && !rec.unified();
    boolean found=false, progress=false;
    for( int i=0; i<_max; i++ ) {
      TVPtr p0 = _ptrs.at(i);
      if( p0.unified() )        // Might collapse into a prior ptr
        throw unimpl();
      // If they overlap, unify
      if( p0==ptr ||
          // Must be a true overlap, not just 2 empty aliases
          (!p0._aliases.is_empty() && p0._aliases.overlaps(ptr._aliases)) ) { 
        progress |= arg(i).unify(rec,test);     // So unify over structs
        if( test && progress ) return true;
      }
      found |= p0==ptr;         // Found a direct hit?
    }    
    if( found ) return progress;

    if( _args==null ) _args = new TV3[1];
    if( _max == _args.length )
      _args = Arrays.copyOf(_args,_max<<1);
    _ptrs.setX(_max,ptr);
    _args[_max++] = rec;
    return true;
  }
  
  // -------------------------------------------------------------
  @Override public boolean _union_impl( TV3 tv3 ) { return false; }
  
  @Override boolean _unify_impl( TV3 tv3 ) {
    TVMem tmem = (TVMem)tv3;    // Invariant when called
    for( int i=0; i<_max; i++ )
      throw unimpl();
    for( int i=0; i<tmem._max; i++ )
      throw unimpl();
    return true;
  }
  // -------------------------------------------------------------
  @Override boolean _fresh_unify_impl(TV3 tv3, boolean test) { throw unimpl(); }

  // -------------------------------------------------------------
  @Override boolean _trial_unify_ok_impl( TV3 tv3, boolean extras ) { throw unimpl(); }
  @Override boolean _exact_unify_impl( TV3 tv3 ) { throw unimpl(); }

  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) { throw unimpl(); }
  @Override void _widen( byte widen ) { throw unimpl(); }

  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    sb.p("[[ ");
    for( int i=0; i<_max; i++ ) {
      _ptrs.at(i)._str(sb,visit,dups,debug).p('=');
      _args   [i]._str(sb,visit,dups,debug).p(',');
    }
    return sb.unchar().p("]]");
  }
  
}

