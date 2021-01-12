package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.type.BitsAlias;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

// TVars for aliased memory.  Very similar to a TArgs, except indexed by alias
// number instead of by direct index.  Missing aliases are assumed to be new
// unique TVars and always unify.

// TODO: Commonly, this TMem is unified with a parent TMem except at specific
// aliases.  We want to lazily manifest this: make a TMem in which all null
// parms pull from the parent.  Not the same as a Unify!  Once every alias on
// this TMem is not-null, we can drop the parent.

public class TMem extends TMulti<TMem> {

  public TMem(TNode mem) { super(mem,new TVar[1]); }

  // Already checks same class, no cycles, not infinite recursion, non-zero parms will_unify.
  @Override boolean _will_unify0(TMem tv, int cnt) { return true; }

  @Override TMem _fresh_new() { return new TMem(null); }

  // Used by Loads.  Unify tv against all aliases at this field only.  Aliases
  // are either produced by the Parser (so very generic) or from forwards-flow
  // from News and very specific.  Ignore the generic ones until they refine.
  // TODO: As aliases further refine, need to undo-redo prior unifies against
  // larger/weaker aliases.
  public boolean unify_alias_load(BitsAlias aliases, String fld, TVar tv, TNode dep, boolean test) {
    boolean progress=false;
    for( int alias : aliases ) {
      if( alias <= BitsAlias.AARY ) return false; // No unify on parser-specific values
      TVar parm = parm(alias);
      if( parm instanceof TObj ) {
        progress = ((TObj)parm).unify_fld(fld,tv,test);
      } else {
        TObj tvo = new TObj(null).add_fld(fld,tv);
        if( parm==null ) {
          if( test ) return true;    // Definitely will be progress
          //TNode.add_work(tvo.push_dep(dep,null)); // If a new alias, it gets the deps
          //TNode.add_work_all(_deps);
          //grow(alias+1)[alias] = tvo;
          //progress = true;
          throw com.cliffc.aa.AA.unimpl();
        } else {
          progress = parm.unify(tvo,test);
        }
      }
      if( test && progress ) return progress; // Shortcut
    }
    return progress;
  }

  // Used by Store and MrgProj and MemJoin, unify alias by alias except the
  // given ones and not the main TMem
  public boolean unify_mem( BitsAlias aliases, TVar tv, boolean test ) {
    if( !(tv instanceof TMem) ) return false; // No progress until its a TMem
    boolean progress = false;
    TMem tmem = (TMem)tv;
    int len = Math.max(_parms.length,tmem._parms.length);
    for( int i=1; i<len; i++ ) {
      if( aliases.test(i) ) continue;  // Not the given aliases
      TVar tv0 =      parm(i);
      TVar tv1 = tmem.parm(i);
      if( tv0!=null && tv1 != null ) progress |= tv0.unify(tv1,test);
      else {
        if( test ) return true; // Always progress
        TVar tx = tv0==null ? (tv1==null ? new TVar() : tv1) : tv0;
        grow(i+1)[i] = tmem.grow(i+1)[i] = tx;
        progress = true;
      }
    }
    if( !test && progress )
      throw com.cliffc.aa.AA.unimpl();
    //TNode.add_work_all(tv._ns);
    return progress;
  }

  // Used by MrgProj with only the alias.
  public boolean unify_alias(int alias, TVar tv, boolean test) {
    TVar lhs = parm(alias);
    if( lhs==null ) {            // No LHS, assume as-if a new TVar
      if( !test ) {              // If not testing
        grow(alias+1)[alias] = tv; // Set to RHS
        tv.push_deps(_deps,null);
      }
      return true;
    }
    return lhs.unify(tv,test);
  }
  // Used by MemJoin with the set of aliases
  public boolean unify_alias(BitsAlias aliases, TMem tmem, boolean test) {
    boolean progress = false;
    for( int alias : aliases ) {
      TVar parm = tmem.parm(alias);
      if( parm != null )        // Might not be anything yet
        progress |= unify_alias(alias,parm,test);
    }
    return progress;
  }

  // Pretty print
  @Override SB _str(SB sb, VBitSet bs, boolean debug) {
    sb.p("[ ");
    for( int i=0; i<_parms.length; i++ ) {
      TVar p = _parms[i];
      if( p!=null ) {
        if( p.getClass()==TVar.class && p._u==null )
          continue;             // Do not print plain TVars for all aliases
        if( i==7 ) sb.p("7:PRIMS ");
        else p.str(sb.p(i).p(':'),bs,debug).p(' ');
      }
    }
    return sb.p("]");
  }


  @Override TNode push_dep(TNode tn, VBitSet visit) {
    // Merge and keep all deps lists.  Since null aliases are a shortcut for "a
    // new TVar appears here later" that TVar needs the deps list when it appears.
    merge_dep(tn);        // Merge dependents lists
    // Push to all non-null aliases
    for( int i=0; i<_parms.length; i++ ) {
      TVar parm = parm(i);
      if( parm != null ) parm.push_dep(tn,visit);
    }
    return tn;
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
