package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.util.*;

// TVars for aliased TypeObjs.  Very similar to a TArgs, except indexed by
// field name instead of by direct index.  Missing aliases are assumed to be
// new unique TVars and always unify.
public class TObj extends TMulti<TObj> {
  final String[] _flds;

  public TObj(TNode mem, String[] flds ) {
    super(mem,init(mem));
    _flds = flds;
    assert flds.length==_parms.length;
  }
  public TObj(TObj tobj) { super(null,new TVar[tobj._parms.length]); _flds = tobj._flds; }

  // Already checks same class, no cycles, not infinite recursion, non-zero parms will_unify.
  @Override boolean _will_unify0(TObj tv) {
    // Require same field names
    if( _parms.length != tv._parms.length ) return false;
    for( int i=0; i<_flds.length; i++ )
      if( !Util.eq(_flds[i],tv._flds[i]) )
        return false;
    return true;
  }

  @Override TObj _fresh_new() { return new TObj(this); }

  // Unify two TObjs, except at the field, unify with the given TVar.
  public void unify_alias(TObj tobj, String fld, TVar tv) {
    throw com.cliffc.aa.AA.unimpl();
  }

  // Pretty print
  @Override SB _str(SB sb, VBitSet bs, boolean debug) {
    sb.p("@{ ");
    for( int i=0; i<_parms.length; i++ ) {
      sb.p(_flds[i]).p(':');
      if( _parms[i]==null ) sb.p('_');
      else _parms[i].str(sb,bs,debug).p(' ');
    }
    return sb.p("}");
  }
}
