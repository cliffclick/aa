package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.type.BitsAlias;
import com.cliffc.aa.util.*;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

// TVars for aliased TypeObjs.  Very similar to a TArgs, except indexed by
// field name instead of by direct index.  To allow Duck-Typing, missing fields
// are allowed, and just added on.  Missing aliases are assumed to be new
// unique TVars and always unify.
public class TObj extends TMulti<TObj> {
  HashMap<String,TVar> _flds;
  static final TVar[] TVS0 = new TVar[0];

  public TObj(TNode mem ) { super(mem,TVS0); _flds = new HashMap<>(); }
  private void put( String fld, TVar tv) { _flds.put(fld,tv); }
  // Lazily add fields
  public boolean add_fld(String fld, TVar tv, boolean test) {
    TVar tvo = _flds.get(fld);
    if( tvo==null ) {           // Does not already exist, so progress
      if( !test ) put(fld,tv);  // Put directly
      return true;              // Declare progress
    }
    return tvo.unify(tv,test);  // Progress recursively
  }
  // Union matching field
  boolean unify_fld(String fld, TVar tv0, boolean test) {
    TVar tv1 = _flds.get(fld);
    if( tv1==null ) {
      if( !test ) put(fld,tv0); // Match fields
      return true;              // Progress
    }
    return tv1.find().unify(tv0.find(),test);
  }

  @Override void _unify( TVar tv ) {
    TObj tvo = (TObj)tv;
    assert _flds!=tvo._flds; // do not expect the shortcut to work
    for( Map.Entry<String,TVar> e : _flds.entrySet() ) {
      String fld = e.getKey();
      TVar   tv0 = e.getValue().find();
      TVar   tv1 = tvo._flds.get(fld);
      if( tv1!=null )
        tv0.unify(tv1.find(),false);
      tvo.put(fld,tv0.find());
    }
    _flds = null;               // LHS is dead
  }

  private TVar parm(String fld) {
    TVar tv = _flds.get(fld);
    if( tv==null ) return null;
    TVar tv2 = tv.find();
    if( tv2 != tv ) put(fld,tv2); // Update ala U-F
    return tv2;
  }

  // Already checks same class, no cycles, not infinite recursion, non-zero parms will_unify.
  @Override boolean _will_unify0(TObj tvo, int cnt) {
    // Have to check matching fields.
    if( _flds == tvo._flds ) return true; // Trivial
    if( _flds.size() > tvo._flds.size() ) return tvo._will_unify0(this, cnt); // Smaller on left
    for( Map.Entry<String,TVar> e : _flds.entrySet() ) {
      TVar tv1 = parm(e.getKey());
      if( tv1!=null && !e.getValue()._will_unify(tv1,cnt+1) )
        return false;
    }
    return true;
  }

  // Recursive call for all parms.  Sincee TObj parms are kept in the HashMap
  // instead of _parms, have to override TMulti here.
  @Override boolean _fresh_unify_recursive(int cnt, boolean progress, TMulti tmulti, BitsAlias news, HashSet<TVar> nongen, NonBlockingHashMap<TVar,TVar> dups, boolean test) {
    // Same subclass 'this' and 'tv'
    TObj tobj = (TObj)tmulti;
    for( String pfld : _flds.keySet() ) {
      TVar ptv =      parm(pfld);    // Pattern tvar
      TVar mtv = tobj.parm(pfld);    // Match TVar
      if( mtv==null ) {
        tobj.put(pfld,mtv=new TVar()); // Update for new
        mtv.push_deps(_deps,null);     // Copy any deps
      }
      progress |= ptv._fresh_unify(cnt,mtv, news, nongen, dups, test);
    };
    return progress;
  }

  @Override TObj _fresh_new() { return new TObj(null); }

  // Pretty print
  @Override SB _str(SB sb, VBitSet bs, boolean debug) {
    sb.p("@{ ");
    _flds.forEach( (fld, tv) -> {
        sb.p(fld).p(':');
        if( tv==null ) sb.p('_');
        else tv.str(sb,bs,debug).p(' ');
      });
    return sb.p("}");
  }

  @Override TNode push_dep(TNode tn, VBitSet visit) {
    // Merge and keep all deps lists.  Since null aliases are a shortcut for "a
    // new TVar appears here later" that TVar needs the deps list when it appears.
    merge_dep(tn);        // Merge dependents lists
    for( String fld : _flds.keySet() )
      parm(fld).push_dep(tn,visit);
    return tn;
  }

  @Override Ary<TNode> push_deps(Ary<TNode> deps, VBitSet visit) {
    if( deps==null ) return deps;
    // Merge and keep all deps lists.  Since null aliases are a shortcut for "a
    // new TVar appears here later" that TVar needs the deps list when it appears.
    merge_deps(deps);     // Merge dependents lists
    // Push to all non-null aliases
    for( String fld : _flds.keySet() )
      parm(fld).push_deps(deps,visit);
    return deps;
  }
}
