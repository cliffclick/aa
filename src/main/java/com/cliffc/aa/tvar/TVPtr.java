package com.cliffc.aa.tvar;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.node.PrimNode;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

/** A ptr-to-struct or ground term TypeInt/TypeFlt.
 *  The ground term includes a ptr-to-int-clazz.
 */
public class TVPtr extends TV3 {
  // This is a pointer tracking aliases.
  // The actual pointed-at type is tracked in memory.
  BitsAlias _aliases;

  // Ground term
  TypeNil _t;

  public TVPtr( BitsAlias aliases, TVStruct str ) { this(aliases,str,null); }
  public TVPtr( BitsAlias aliases, TVStruct str, TypeNil tn ) {
    super(aliases.test(0),str);
    _aliases = aliases;
    _t = tn;
  }
  public TVPtr make_from(TypeNil t) { return t==_t ? this : new TVPtr(_aliases,load(),t); }

  @Override public TVPtr as_ptr() { return this; }

  public TVStruct load() { return arg(0).as_struct(); }

  @Override int eidx() { return TVErr.XPTR; }

  //// Make the leader a nilable version of 'this' child
  //@Override TV3 find_nil() {
  //  TVPtr ptr = (TVPtr)copy();
  //  if( ptr._t!=null )
  //    ptr._t = (TypeNil)ptr._t.meet(TypeNil.NIL);
  //  ptr.add_may_nil(false);
  //  return ptr;
  //}

  // -------------------------------------------------------------
  // Union aliases
  @Override public void _union_impl(TV3 that) {
    assert !unified();
    TVPtr ptr = (TVPtr)that;    // Invariant when called
    _aliases = _aliases.meet(ptr._aliases);
    if( _t != null ) {
      if( ptr._t==null ) ptr._t=_t;
      else ptr._t = (TypeNil)ptr._t.meet(_t);
    }
  }

  @Override boolean _unify_impl(TV3 that ) {
    TVPtr ptr = (TVPtr)that;    // Invariant when called
    return load()._unify(ptr.load(),false);
  }

  // -------------------------------------------------------------
  @Override boolean _fresh_unify_impl(TV3 that, boolean test) {
    boolean progress = false;
    TVPtr ptr = (TVPtr)that.find();    // Invariant when called
    // Update aliases
    BitsAlias aliases = _aliases.meet( ptr._aliases );
    if( aliases != ptr._aliases ) {
      ptr._aliases = aliases;
      progress = ptrue();
    }
    // Update Type
    TypeNil t = _t==null ? ptr._t : (ptr._t==null ? _t : (TypeNil)_t.meet(ptr._t));
    if( t != ptr._t ) {
      ptr._t = t;
      progress = ptrue();
    }
    if( test && progress ) return progress;

    return super._fresh_unify_impl(that,test) | progress;
  }

  // -------------------------------------------------------------
  @Override int _trial_unify_ok_impl( TV3 tv3 ) {
    TVPtr that = (TVPtr)tv3; // Invariant when called
    if( _t!=null && that._t!=null ) {
      if( _t.getClass() != that._t.getClass() ) {
        // Mixed int/float is bad, but always can mix in a nil
        if( _t!=TypeNil. NIL && that._t!=TypeNil. NIL &&
            _t!=TypeNil.XNIL && that._t!=TypeNil.XNIL )
          return -1;            // Wrong kind of bases
      }
    }
    return load()._trial_unify_ok(that.load());
  }

  @Override boolean _exact_unify_impl( TV3 tv3 ) { return true; }

  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) {
    if( _t instanceof TypeInt ti ) return ti;
    if( _t instanceof TypeFlt tf ) return tf;
    deps_add(dep);
    // Compatible escaped aliases
    BitsAlias aliases = Env.ROOT.matching_escaped_aliases(this, dep);
    return TypeMemPtr.make(false,_may_nil,aliases,TypeStruct.ISUSED);
  }
  @Override void _widen( byte widen ) {
    if( widen < 2 ) return;
    if( _t==null ) return;
    TypeNil tw = (TypeNil)_t.widen();
    if( tw == _t ) return;
    _t = tw;
    _deps_work_clear();
  }

  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    if( !prims ) {
      if( _aliases == PrimNode.PINT ._tptr._aliases ) return sb.p(_t);
      if( _aliases == PrimNode.PFLT ._tptr._aliases ) return sb.p(_t);
      if( _aliases == PrimNode.PSTR ._tptr._aliases ) return sb.p("*STRZ" );
      if( _aliases == PrimNode.PMATH._tptr._aliases ) return sb.p("*MATH" );
    }
    sb.p("*");
    _aliases.str(sb);
    if( _args.length>0 && _args[0]!=null ) arg(0)._str(sb,visit,dups,debug,prims);
    else sb.p("---");
    if( _may_nil ) sb.p('?');
    return sb;
  }
}
