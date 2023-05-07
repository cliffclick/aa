package com.cliffc.aa.tvar;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import static com.cliffc.aa.AA.unimpl;

/** A ptr-to-struct
 *
 */
public class TVPtr extends TV3 {
  // This is a pointer tracking aliases.
  // The actual pointed-at type is tracked in memory.
  BitsAlias _aliases;
  public TVPtr( BitsAlias aliases ) {
    super(aliases.test(0));
    _aliases = aliases;
  }
  public TVPtr( ) { this(BitsAlias.EMPTY); }
  
  public TVPtr( BitsAlias aliases, TV3 str ) {
    super(aliases.test(0),str);
    _aliases = aliases;
  }

  @Override boolean can_progress() { return false; }

  @Override int eidx() { return TVErr.XPTR; }

  // Make the leader a nilable version of 'this' child
  @Override TV3 find_nil() {
    TVPtr ptr = (TVPtr)copy();
    ptr.add_may_nil(false);
    return ptr;
  }

  // -------------------------------------------------------------
  // Union aliases
  @Override public void _union_impl(TV3 that) {
    TVPtr ptr = (TVPtr)that;    // Invariant when called
    _aliases = _aliases.meet(ptr._aliases);
  }

  @Override boolean _unify_impl(TV3 that ) { return true; }
  
  // -------------------------------------------------------------
  @Override boolean _fresh_unify_impl(TV3 that, boolean test) {
    TVPtr ptr = (TVPtr)that;    // Invariant when called
    if( _aliases==ptr._aliases ) return false;
    BitsAlias aliases = _aliases.meet(ptr._aliases);
    if( aliases == ptr._aliases ) return false;
    ptr._aliases = aliases;
    return true;
  }
  
  // -------------------------------------------------------------
  @Override boolean _trial_unify_ok_impl( TV3 tv3, boolean extras ) {
    TVPtr that = (TVPtr)tv3; // Invariant when called
    return _aliases == that._aliases;
  }

  @Override boolean _exact_unify_impl( TV3 tv3 ) { return true; }
  
  // -----------------
  @Override TV3 _sharptr( TVMem mem ) {
    if( ODUPS.tset(_uid) ) return this;
    assert _args==null || _args.length==0;
    if( _aliases.is_empty() )
      throw unimpl();
    int j=-1;
    int mlen = mem.len();
    for( int i=0; i<mlen; i++ ) {
      TVPtr p0 = mem.ptr(i);      
      if( p0._aliases==_aliases ) j=i;
      else if( p0._aliases.overlaps(_aliases) )
        throw unimpl();         // Expecting exact hit
    }
    if( j== -1 ) throw unimpl(); // Not found
    TVPtr ptr = new TVPtr(_aliases,mem.arg(j)._sharptr(mem));
    ptr._may_nil = _may_nil;
    return ptr;
  }
  
  
  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) {
    // Compatible escaped aliases
    BitsAlias aliases = Env.ROOT.matching_escaped_aliases(this, dep);
    return TypeMemPtr.make(false,_may_nil,aliases,TypeStruct.ISUSED);
  }
  @Override void _widen( byte widen ) { }
  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    sb.p("*");
    _aliases.str(sb);
    if( _args.length>0 && _args[0]!=null ) arg(0)._str(sb,visit,dups,debug,prims);
    if( _may_nil ) sb.p('?');
    return sb;
  }
}
