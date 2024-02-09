package com.cliffc.aa.tvar;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;


/** A ptr-to-struct or ground term TypeInt/TypeFlt.
 *  The ground term includes a ptr-to-int-clazz.
 */
public class TVPtr extends TV3 {
  public static final TVPtr PTRCLZ = new TVPtr(BitsAlias.CLZ,TVStruct.STRCLZ);
  // This is a pointer tracking aliases.
  // The actual pointed-at type is tracked in memory.
  BitsAlias _aliases;

  public TVPtr( BitsAlias aliases, TVStruct str ) {
    super(aliases.test(0),str);
    _aliases = aliases.clear(0);
  }

  @Override public TVPtr as_ptr() { return this; }

  public TVStruct load() { return arg(0).as_struct(); }

  @Override int eidx() { return TVErr.XPTR; }

  public BitsAlias aliases() { return _aliases; }
  
  // -------------------------------------------------------------
  // Union aliases
  @Override public void _union_impl(TV3 that) {
    assert !unified();
    TVPtr ptr = (TVPtr)that;    // Invariant when called
    ptr._aliases = _aliases.meet(ptr._aliases);
  }

  @Override boolean _unify_impl(TV3 that ) {
    TVPtr ptr = (TVPtr)that;    // Invariant when called
    return load()._unify(ptr.load(),false);
  }

  // -------------------------------------------------------------
  @Override boolean _fresh_unify_impl(TV3 that, boolean test) {
    boolean progress = false;
    TVPtr ptr = (TVPtr)that.find();    // Invariant when called
    BitsAlias aliases = _aliases.meet( ptr._aliases );
    
    // Update aliases
    if( aliases != ptr._aliases ) {
      if( !test ) ptr._aliases = aliases;
      progress = ptrue();
    }
    if( test && progress ) return progress;

    return super._fresh_unify_impl(that,test) | progress;
  }

  // -------------------------------------------------------------
  @Override int _trial_unify_ok_impl( TV3 pat ) {
    TVPtr that = (TVPtr) pat; // Invariant when called
    // Cannot fail a trial for non-overlapping aliases, since a union can add
    // aliases later, until the sets overlap.
    return load()._trial_unify_ok(that.load());
  }

  @Override boolean _exact_unify_impl( TV3 tv3 ) { return true; }

  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) {
    deps_add(dep);
    // Compatible escaped aliases
    BitsAlias aliases = Env.ROOT==null ? _aliases : Env.ROOT.matching_escaped_aliases(this, dep);
    return TypeMemPtr.malloc(false,_may_nil,aliases,(TypeStruct)load()._as_flow(dep));
  }

  @Override void _widen( byte widen ) { }

  
  boolean is_nil (TVStruct str) { return str.len()==0 &&  _aliases.is_empty() && _may_nil; }
  boolean is_0clz(TVStruct str) { return str.len()==0 && (_aliases.is_empty() || _aliases==BitsAlias.CLZ); }
  boolean is_prim(TVStruct str) { return str.is_prim() && _aliases==BitsAlias.EMPTY; }
  
  @Override public VBitSet _get_dups_impl(VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    if( _args.length == 0 || _args[0]==null ) return dups; // Broken ptr
    // Look for short-form prints
    // No rollups unless asked for
    TV3 tv0 = debug ? debug_arg(0) : arg(0);
    if( _args[0]==tv0 && tv0 instanceof TVStruct str ) {
      if( is_nil(str) || (is_0clz(str) && !debug) || is_prim(str) ) {
        // Fully replicate a nil, empty clazz, or prim; no dups
        visit.clear(_uid);
        return dups;
      }
    }
    // Normally walk the pointed-at TVStruct
    return tv0._get_dups(visit,dups,debug,prims);
  }
  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    // Broken ptr
    if( _args.length == 0 || _args[0]==null )
      return _aliases.str(sb.p("*")).p("---").p(_may_nil ? "?" : "");
    // Look for short-form prints
    // No rollups unless asked for
    TV3 tv0 = debug ? debug_arg(0) : arg(0);
    if( _args[0]==tv0 && tv0 instanceof TVStruct str ) {
      if( is_nil (str) ) return sb.p("nil");
      if( is_0clz(str) && !debug )  return sb.p("_");
      if( is_prim(str) ) // Shortcut for boxed primitives
        return str._str(sb,visit,dups,debug,prims);
    }
    _aliases.str(sb.p("*"));
    return tv0._str(sb,visit,dups,debug,prims).p(_may_nil ? "?" : "");
  }
}
