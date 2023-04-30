package com.cliffc.aa.tvar;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.BitsAlias;
import com.cliffc.aa.type.Type;
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
    ptr._aliases = ptr._aliases.meet_nil();
    ptr.add_may_nil(false);
    return ptr;
  }

  // -------------------------------------------------------------
  // Union aliases
  @Override public boolean _union_impl(TV3 that) {
    
    //return false;
    throw unimpl();
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
    //TVPtr that = (TVPtr)tv3; // Invariant when called
    //// Structural trial unification on the one child
    //return load()._trial_unify_ok( that.load(), extras);
    throw unimpl();
  }

  @Override boolean _exact_unify_impl( TV3 tv3 ) { return true; }
  
  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) {
    //// Compatible escaped aliases
    //BitsAlias aliases = Env.ROOT.matching_escaped_aliases(this, dep);
    //TypeStruct tstr = dep==null ? (TypeStruct)load()._as_flow(dep) : TypeStruct.ISUSED;
    //return TypeMemPtr.make(false,_may_nil,aliases,tstr);
    throw unimpl();
  }
  @Override void _widen( byte widen ) { }
  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    sb.p("*");
    _aliases.str(sb);
    if( _args[0]!=null ) arg(0)._str(sb,visit,dups,debug);
    return sb;
  }
}
