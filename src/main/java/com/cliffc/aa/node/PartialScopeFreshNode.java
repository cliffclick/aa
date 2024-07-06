package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.Util;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVPtr;
import com.cliffc.aa.tvar.TVStruct;
import com.cliffc.aa.type.*;

// Make a fresh instance of a prefix of incoming scope/display.  Only those
// fields defined "so far" are available, and they are all fresh.  "So far" is
// defined by the parser's scope logic, and modified by reordering for mutual
// let rec.
public class PartialScopeFreshNode extends FreshNode {
  final int _alias;
  final String[] _flds;

  public PartialScopeFreshNode( ScopeNode scope ) {
    super(scope.ptr());
    _alias = scope.ptr()._alias;
    StructNode frame = scope.stk();
    // Copy partial list of field names
    _flds = new String[frame.len()];
    for( int i=0; i<frame.len(); i++ )
      _flds[i] = frame.fld(i);
  }

  @Override public String label() { return "PartialScopeFresh"; }
  @Override public Type value() {
    // ptr-to-partial struct
    return TypeMemPtr.make_simple(_alias);
  }

  @Override public Type live_use( int i ) {
    if( i != 0 ) return Type.ALL;
    return val(0) instanceof TypeMemPtr tmp && !tmp.is_simple_ptr()
      ? tmp._obj.flatten_live_fields()
      : val(0).oob();
  }

  private TVPtr _partial;
  @Override public TV3 _set_tvar() {
    // Close any cycles with an early set of self:
    super._set_tvar();

    // Maintain an internal prefix copy of in(0), limited to named fields.
    // This is the "Fresh" template.  I'd like to just Fresh each input field
    // to my output, but because of mut-let-rec cycles I need to grab all the
    // _flds at once.  Maintaining an internal copy to avoid creating a new one
    // each iteration (and thus declaring progress if unifying).
    assert Util.eq(_flds[0],TypeFld.CLZ);
    for( int i=1; i<_flds.length; i++ )
      assert !_flds[i].equals(TypeFld.CLZ);
    TVStruct partial = new TVStruct(_flds,TVStruct.leafs(_flds.length),true);
    partial.arg(0,new TVPtr(BitsAlias.EMPTY, new TVStruct(true) ) );
    _partial = new TVPtr(BitsAlias.make0(_alias),partial);

    // Get the shared closure
    TV3 share = in(0).set_tvar();
    if( !(share instanceof TVPtr sptr) )
      throw AA.TODO();
    TVStruct sclo = sptr.load(); // Shared closure
    // Unify to prefix of the incoming scope
    for( String fld : _flds ) {
      TV3 sarg = sclo   .arg( fld );
      TV3 parg = partial.arg( fld );
      if( sarg == null )
        sclo.add_fld( fld, parg );
      else parg.unify( sarg, false );
    }
    // Fresh-unify self/that
    _partial.fresh_unify(_nongen,tvar(),false);
    return tvar();
  }

  // Only fresh against the listed scope prefix.
  @Override public boolean unify( boolean test ) {
    //return frsh.fresh_unify(_nongen,that,test);
    TV3 that = tvar();
    TV3 fresh = _partial;
    return fresh.fresh_unify(_nongen,that,test);
  }

  @Override void walk_reset0() { _partial=null; super.walk_reset0(); }
}
