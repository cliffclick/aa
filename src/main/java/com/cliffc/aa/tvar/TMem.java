package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.type.BitsAlias;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

// TVars for aliased memory.  Very similar to a TArgs, except indexed by alias
// number instead of by direct index.  Missing aliases are assumed to be new
// unique TVars and always unify.
public class TMem extends TMulti<TMem> {

  public TMem(TNode mem) { super(mem,new TVar[1]); }
  public TMem(TVar[] parms) { super(null,parms); }

  // Already checks same class, no cycles, not infinite recursion, non-zero parms will_unify.
  @Override boolean _will_unify0(TMem tv) { return true; }

  @Override TMem _fresh_new() { return new TMem(new TVar[_parms.length]); }

  // Unify two TMems alias by alias, except at the given aliases unify this
  // with the given TVar.  Do not merge their TNode sets, since this is not a
  // unifying the two TMems directly.
  public void unify_alias(TMem tmem, BitsAlias aliases, TVar tv) {
    int alen = aliases.max()+1; // Length of aliases
    grow(alen);
    for( int i=0; i<_parms.length; i++ ) {
      TVar lhs =      parm(i);
      TVar rhs = tmem.parm(i);
      if( i<alen && aliases.test_recur(i) ) rhs = tv;
      if( rhs==null ) continue; // Nothing to unify
      if( lhs==null ) {         // No LHS, assume as-if a new TVar
        _parms[i] = rhs;        // Set to RHS
        rhs.push_deps(_deps,null);
      }
      else lhs.unify(rhs);
    }
  }

  // Pretty print
  @Override SB _str(SB sb, VBitSet bs, boolean debug) {
    sb.p("[ ");
    for( int i=0; i<_parms.length; i++ )
      if( _parms[i]!=null ) _parms[i].str(sb.p(i).p(':'),bs,debug).p(' ');
    return sb.p("]");
  }


  @Override void push_dep(TNode tn, VBitSet visit) {
    // Merge and keep all deps lists.  Since null aliases are a shortcut for "a
    // new TVar appears here later" that TVar needs the deps list when it appears.
    merge_dep(tn);        // Merge dependents lists
    // Push to all non-null aliases
    for( int i=0; i<_parms.length; i++ ) {
      TVar parm = parm(i);
      if( parm != null ) parm.push_dep(tn,visit);
    }
  }
  @Override Ary<TNode> push_deps(Ary<TNode> deps, VBitSet visit) {
    if( deps==null ) return deps;
    // Merge and keep all deps lists.  Since null aliases are a shortcut for "a
    // new TVar appears here later" that TVar needs the deps list when it appears.
    merge_deps(deps);     // Merge dependents lists
    // Push to all non-null aliases
    for( int i=0; i<_parms.length; i++ ) {
      TVar parm = parm(i);
      if( parm != null ) parm.push_deps(deps,visit);
    }
    return deps;
  }
}
