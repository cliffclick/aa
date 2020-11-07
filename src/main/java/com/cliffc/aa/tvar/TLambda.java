package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.SB;
import org.jetbrains.annotations.NotNull;

import static com.cliffc.aa.AA.*;

// Type of a Hindley-Milner Lambda operator.
// Same as a N-tuple, but all inputs come from Fun/Parms.
public class TLambda extends TypeVar {
  final int _nargs;

  // Basic H-M type variable supporting U-F and parametric types.
  public TLambda( @NotNull TNode fun, int nargs ) {
    super(fun);
    _nargs = nargs;
  }

  // Type from parts
  @Override public TypeTuple _type(boolean head) {
    final TNode[] parms = _tnode.parms();
    // A N-tuple from inputs
    Type[] ts = Types.get(parms.length);
    ts[CTL_IDX] = _tnode.val();
    ts[MEM_IDX] = parms[MEM_IDX]==null ? TypeMem.ALLMEM    : parms[MEM_IDX].tvar().type();
    ts[FUN_IDX] = parms[FUN_IDX]==null ? TypeMemPtr.NO_DISP: parms[FUN_IDX].tvar().type();
    for( int i=ARG_IDX; i<_nargs; i++ )
      ts[i] = parms[i]==null ? Type.SCALAR : parms[i].tvar().type();
    return TypeTuple.make(ts);
  }

  // Test no fails during unification
  @Override boolean _unify_test(TypeVar tv) {
    if( tv instanceof TVar ) return tv._unify_test(this);
    if( !(tv instanceof TLambda) ) return false;// Fails unification
    TLambda tn = (TLambda)tv;
    // Structural unification
    if( _nargs != tn._nargs ) return false;
    final TNode[] args0 =    _tnode.parms();
    final TNode[] args1 = tn._tnode.parms();
    for( int i=0; i<_nargs; i++ )
      if( args0[i]!=null && args1[i]!=null &&
          !args0[i].tvar()._unify_test(args1[i].tvar()) )
        return false;
    return true;
  }
  
  // Unify this into tv.
  @Override void _unify(TypeVar tv) {
    if( tv instanceof TVar ) { tv._unify(this); return; }
    TLambda tn = (TLambda)tv;
    // Structural unification
    final TNode[] args0 =    _tnode.parms();
    final TNode[] args1 = tn._tnode.parms();
    for( int i=0; i<_nargs; i++ )
      if( args0[i]!=null && args1[i]!=null )
        args0[i].tvar()._unify(args1[i].tvar());
  }

  // Pretty print
  @Override public SB _str(SB sb, boolean pretty) {
    @NotNull TNode           [] parms = _tnode.parms   ();
    @NotNull String @NotNull [] names = _tnode.argnames();
    sb.p('[');
    for( int i=0; i<parms.length; i++ ) {
      TNode tn = parms[i];
      if( tn!=null ) tn.tvar()._str(sb.p(names[i]).p(':'),pretty);
      sb.p(',');
    }
    return sb.unchar().p(']');
  }
}
