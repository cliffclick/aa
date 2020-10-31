package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.Types;
import com.cliffc.aa.type.TypeTuple;
import com.cliffc.aa.util.SB;
import org.jetbrains.annotations.NotNull;

// Type of a Hindley-Milner Lambda operator.
// Same as a N-tuple, but all inputs come from Fun/Parms.
public class TLambda extends TypeVar {
  private final TNode[] _parms;

  // Basic H-M type variable supporting U-F and parametric types.
  public TLambda( @NotNull TNode fun ) {
    super(fun);
    _parms = fun.parms();
  }

  // Type from parts
  @Override public TypeTuple _type(boolean head) {
    // A N-tuple from inputs
    Type[] ts = Types.get(_parms.length+1);
    ts[0] = _tnode.tvar().type();
    for( int i=0; i<_parms.length; i++ )
      ts[i+1] = _parms[i]==null ? Type.ALL : _parms[i].tvar().type();
    return TypeTuple.make(ts);
  }

  // Unify this into tv.
  @Override public Object unify(TypeVar tv) {
    if( tv instanceof TVar ) return tv.unify(this);
    if( !(tv instanceof TLambda) )
      throw com.cliffc.aa.AA.unimpl(); // Fails unification
    TLambda tn = (TLambda)tv;
    // Structural unification
    throw com.cliffc.aa.AA.unimpl();
  }

  // Pretty print
  @Override public SB _str(SB sb, boolean pretty) {
    sb.p("V").p(uid()).p("[");
    _tnode.tvar()._str(sb,pretty).p(","); // Control
    for( TNode tn : _parms ) {
      if( tn!=null ) tn.tvar()._str(sb,pretty);
      sb.p(",");
    }
    return sb.unchar().p("]");
  }
}
