package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.SB;
import org.jetbrains.annotations.NotNull;

import static com.cliffc.aa.AA.*;

// Type of a Hindley-Milner Lambda operator.
// Same as a N-tuple, but all inputs come from Fun/Parms.
public class TLambda extends TypeVar {
  final TNode[] _parms; // ParmNodes

  // Basic H-M type variable supporting U-F and parametric types.
  public TLambda( @NotNull TNode fun ) {
    super(fun);
    _parms = fun.parms();
  }

  // Type from parts
  @Override public TypeTuple _type(boolean head) {
    // A N-tuple from inputs
    Type[] ts = Types.get(_parms.length);
    ts[CTL_IDX] = _tnode.tvar().type();
    ts[MEM_IDX] = _parms[MEM_IDX]==null ? TypeMem.ALLMEM    : _parms[MEM_IDX].tvar().type();
    ts[FUN_IDX] = _parms[FUN_IDX]==null ? TypeMemPtr.NO_DISP: _parms[FUN_IDX].tvar().type();
    for( int i=ARG_IDX; i<_parms.length; i++ )
      ts[i] = _parms[i]==null ? Type.SCALAR : _parms[i].tvar().type();
    return TypeTuple.make(ts);
  }

  // Unify this into tv.
  @Override public Object unify(TypeVar tv) {
    if( tv instanceof TVar ) return tv.unify(this);
    if( !(tv instanceof TLambda) )
      throw com.cliffc.aa.AA.unimpl(); // Fails unification
    TLambda tn = (TLambda)tv;
    // Structural unification
    throw unimpl();
  }

  // Pretty print
  @Override public SB _str(SB sb, boolean pretty) {
    sb.p('V').p(uid()).p('[');
    _tnode.tvar()._str(sb,pretty).p(','); // Control
    @NotNull String @NotNull [] names = _tnode.argnames();
    for( int i=1; i<_parms.length; i++ ) {
      TNode tn = _parms[i];
      if( tn!=null ) tn.tvar()._str(sb.p(names[i]).p(':'),pretty);
      sb.p(',');
    }
    return sb.unchar().p(']');
  }
}
