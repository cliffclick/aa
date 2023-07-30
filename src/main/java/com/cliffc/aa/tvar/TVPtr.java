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

  public BitsAlias aliases() { return _aliases; }
  
  // -------------------------------------------------------------
  // Union aliases
  @Override public void _union_impl(TV3 that) {
    assert !unified();
    TVPtr ptr = (TVPtr)that;    // Invariant when called
    _aliases = _aliases.meet(ptr._aliases);
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
      ptr._aliases = aliases;
      progress = ptrue();
    }
    if( test && progress ) return progress;

    return super._fresh_unify_impl(that,test) | progress;
  }

  // -------------------------------------------------------------
  @Override int _trial_unify_ok_impl( TV3 tv3 ) {
    TVPtr that = (TVPtr)tv3; // Invariant when called
    return load()._trial_unify_ok(that.load());
  }

  @Override boolean _exact_unify_impl( TV3 tv3 ) { return true; }

  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) {
    deps_add(dep);
    // Compatible escaped aliases
    BitsAlias aliases = Env.ROOT.matching_escaped_aliases(this, dep);
    return TypeMemPtr.make(false,_may_nil,aliases,TypeStruct.ISUSED);
  }

  @Override void _widen( byte widen ) { }
  
 @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    sb.p("*");
    _aliases.str(sb);
    if( _args.length>0 && _args[0]!=null ) arg(0)._str(sb,visit,dups,debug,prims);
    else sb.p("---");
    if( _may_nil ) sb.p('?');
    return sb;
  }
}
