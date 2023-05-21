package com.cliffc.aa.tvar;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.node.PrimNode;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

/** A ptr-to-struct
 *
 */
public class TVPtr extends TV3 {
  // This is a pointer tracking aliases.
  // The actual pointed-at type is tracked in memory.
  BitsAlias _aliases;
  
  public TVPtr( BitsAlias aliases, TVStruct str ) {
    super(aliases.test(0),str);
    _aliases = aliases;
  }

  @Override public TVPtr as_ptr() { return this; }

  public TVStruct load() { return arg(0).as_struct(); }
  
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

  @Override boolean _unify_impl(TV3 that ) {
    TVPtr ptr = (TVPtr)that;    // Invariant when called
    return load()._unify(ptr.load(),false);
  }

  boolean _unify_base( TVBase base, boolean test ) { return _unify(base.clz(),test); }

  boolean _trial_unify_base( TVBase base, boolean extras ) { return _trial_unify_ok(base.clz(),extras); }
  
  // -------------------------------------------------------------
  @Override boolean _fresh_unify_impl(TV3 that, boolean test) {
    boolean progress = super._fresh_unify_impl(that,test);
    if( test && progress ) return true;
    assert !unified();
    TVPtr ptr = (TVPtr)that.find();    // Invariant when called
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
  
  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) {
    // Compatible escaped aliases
    BitsAlias aliases = Env.ROOT.matching_escaped_aliases(this, dep);
    return TypeMemPtr.make(false,_may_nil,aliases,TypeStruct.ISUSED);
  }
  @Override void _widen( byte widen ) { }
  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    if( !prims ) {
      if( _aliases == PrimNode.PINT ._tptr._aliases ) return sb.p("int" );
      if( _aliases == PrimNode.PFLT ._tptr._aliases ) return sb.p("flt" );
      if( _aliases == PrimNode.PSTR ._tptr._aliases ) return sb.p("str" );
      if( _aliases == PrimNode.PMATH._tptr._aliases ) return sb.p("math");
    }
    sb.p("*");
    _aliases.str(sb);
    if( _args.length>0 && _args[0]!=null ) arg(0)._str(sb,visit,dups,debug,prims);
    else sb.p("---");
    if( _may_nil ) sb.p('?');
    return sb;
  }
}
