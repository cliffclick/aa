package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.type.BitsAlias;
import com.cliffc.aa.util.*;


// TVars for memory aliases, where un-mentioned aliases are never looked at.

public class TMem extends TVar {
  // TVar mapping for an alias
  NonBlockingHashMapLong<TVar> _alias2obj;

  public TMem(TNode mem) { super(mem); }

  // Get at alias or null
  TVar obj(int alias) {
    if( _alias2obj==null ) return null;
    TVar tv = _alias2obj.get(alias);
    if( tv==null ) return null;
    TVar tv2 = tv.find();
    if( tv!=tv2 ) _alias2obj.put(alias,tv2);
    return tv2;
  }

  private TVar put( int alias, TVar tv) {
    if( _alias2obj==null ) _alias2obj = new NonBlockingHashMapLong<>();
    return _alias2obj.put(alias, tv);
  }

  // Unify parts after other work is done
  @Override void _unify( TVar tv ) {
    assert _u!=null;                   // Flagged as being unified
    if( tv instanceof TVDead ) return; // Dead, no parts unify
    TMem tmem = (TMem)tv;
    if( _alias2obj==null ) return;     // No parts here to unify into there
    if( tmem._alias2obj==null ) { tmem._alias2obj = _alias2obj; _alias2obj=null; return; } // Trivial move parts from here to there

    for( long a : _alias2obj.keySet() ) {
      int alias = (int)a;
      TVar lhs =      obj(alias);
      TVar rhs = tmem.obj(alias);
      if( rhs==null ) tmem.put(alias,lhs);
      else rhs._unify0(lhs,false);
    }
  }

  // Used by Loads and Stores.  Unify tv against all aliases at this field
  // only.  Aliases are either produced by the Parser (so very generic) or from
  // forwards-flow from News and very specific.  Ignore the generic ones until
  // they refine.  TODO: As aliases further refine, need to undo-redo prior
  // unifies against larger/weaker aliases.
  public boolean unify_alias_fld(TNode nobj, BitsAlias aliases, String fld, TVar tv, TNode dep, boolean test) {
    boolean progress=false;
    for( int alias : aliases ) {
      if( alias <= BitsAlias.AARY ) return false; // No unify on parser-specific values
      TVar tobj = obj(alias);
      if( tobj instanceof TObj ) {
        progress = ((TObj)tobj).unify_fld(fld,tv,test);
      } else if( tobj instanceof TVDead ) {
        // Does no unification, and never any progress
      } else {
        if( test ) return true; // Definitely will be progress
        TObj tvo = new TObj(nobj);
        put(alias,tvo);
        progress = tvo.add_fld(fld,tv,false);
        if( tobj==null ) {
          //TNode.add_work(tvo.push_dep(dep,null)); // If a new alias, it gets the deps
          //TNode.add_work_all(_deps);
        } else {
          assert tobj.getClass()==TVar.class;
          // probably unify tobj (as tvar) with new tvo
          throw com.cliffc.aa.AA.unimpl();
        }
      }
      if( progress && test ) return progress; // Shortcut
    }
    return progress;
  }

  //// Used by Store and MrgProj and MemJoin, unify alias by alias except the
  //// given ones and not the main TMem
  //public boolean unify_mem( BitsAlias aliases, TVar tv, boolean test ) {
  //  if( !(tv instanceof TMem) ) return false; // No progress until its a TMem
  //  boolean progress = false;
  //  TMem tmem = (TMem)tv;
  //  int len = Math.max(_parms.length,tmem._parms.length);
  //  for( int i=1; i<len; i++ ) {
  //    if( aliases.test(i) ) continue;  // Not the given aliases
  //    TVar tv0 =      parm(i);
  //    TVar tv1 = tmem.parm(i);
  //    if( tv0!=null && tv1 != null ) progress |= tv0.unify(tv1,test);
  //    else {
  //      if( test ) return true; // Always progress
  //      TVar tx = tv0==null ? (tv1==null ? new TVar() : tv1) : tv0;
  //      grow(i+1)[i] = tmem.grow(i+1)[i] = tx;
  //      progress = true;
  //    }
  //  }
  //  if( !test && progress )
  //    throw com.cliffc.aa.AA.unimpl();
  //  //TNode.add_work_all(tv._ns);
  //  return progress;
  //}

  // Unify at the alias
  public boolean unify_alias(int alias, TVar tv, boolean test) {
    TVar old = obj(alias);
    if( old==null )
      return test || put(alias,tv)==null;
    return old.unify(tv,test);
  }

  // Unify at the aliases, overwrites the default.  All objects at given
  // aliases are already unified.
  public boolean unify_alias(BitsAlias aliases, TMem tmem, boolean test) {
    boolean progress = false;
    TVar tobj=null;
    for( int alias : aliases ) {
      TVar tv = tmem.obj(alias); // Get prior mem idea of this alias
      if( tv==null ) continue;   // No idea (yet) from prior mem
      if( tobj==null ) tobj=tv;  // All objects in this set of aliases are already unified
      else assert tobj==tv;
      progress |= unify_alias(alias,tv,test); // Overwrite the default for alias
      if( progress && test ) return true;
    }
    return progress;
  }


  //// Find instances of 'tv' inside of 'this' via structural recursion.  Walk
  //// the matching Type at the same time.  Report the first one found, and
  //// assert all the others have the same Type.
  //@Override Type _find_tvar(Type t, TVar tv, Type t2) {
  //  if( DUPS.tset(_uid) ) return t2; // Stop cycles
  //  t2 = _find_tvar_self(t,tv,t2);   // Look for direct hit
  //  if( tv==this ) return t2;        // Direct hit is the answer
  //  // Search recursively
  //  TypeMem tt = (TypeMem)t;
  //  for( int i=1; i<_parms.length; i++ ) {
  //    TVar tva = parm(i);
  //    if( tva!=null )
  //      t2 = tva._find_tvar(tt.at(i),tv,t2);
  //  }
  //  return t2;
  //}

  // Pretty print
  @Override SB _str(SB sb, VBitSet bs, boolean debug) {
    if( _alias2obj==null ) return sb.p("[]");
    sb.p("[ ");
    for( long alias : _alias2obj.keySet() ) {
      if( alias==7 ) sb.p("7:PRIMS ");
      else _alias2obj.get(alias).str(sb.p(alias).p(':'),bs,debug).p(' ');
    }
    return sb.p("]");
  }


  @Override public TNode push_dep(TNode tn, VBitSet visit) {
    // Merge and keep all deps lists.  Since null aliases are a shortcut for "a
    // new TVar appears here later" that TVar needs the deps list when it appears.
    merge_dep(tn);        // Merge dependents lists
    //// Push to all non-null aliases
    //for( int i=0; i<_parms.length; i++ ) {
    //  TVar parm = parm(i);
    //  if( parm != null ) parm.push_dep(tn,visit);
    //}
    return tn;
  }
  @Override Ary<TNode> push_deps(Ary<TNode> deps, VBitSet visit) {
    if( deps==null ) return deps;
    // Merge and keep all deps lists.  Since null aliases are a shortcut for "a
    // new TVar appears here later" that TVar needs the deps list when it appears.
    merge_deps(deps);     // Merge dependents lists
    //// Push to all non-null aliases
    //for( int i=0; i<_parms.length; i++ ) {
    //  TVar parm = parm(i);
    //  if( parm != null ) parm.push_deps(deps,visit);
    //}
    return deps;
  }
}
