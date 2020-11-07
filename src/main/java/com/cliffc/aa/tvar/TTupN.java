package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeTuple;
import com.cliffc.aa.type.Types;
import com.cliffc.aa.util.SB;
import org.jetbrains.annotations.NotNull;

// Type of a Hindley-Milner N-tuple operator
// "CMV" for {Control,Memory,Value} as the result of Rets and CallEpis.
// {Control,Memory,Display/Fun,Arg2,Arg3,...} for an N-arg Call.
public class TTupN extends TypeVar {
  private final int _n;

  // Basic H-M type variable supporting U-F and parametric types.
  public TTupN( @NotNull TNode tn, int n ) { super(tn); _n=n; }

  // Type from parts
  @Override public TypeTuple _type(boolean head) {
    // A N-tuple from inputs
    Type[] ts = Types.get(_n);
    for( int i=0; i<_n; i++ )
      ts[i] = _tnode.tvar(i).type();
    return TypeTuple.make(ts);
  }

  // Test no fails during unification
  @Override boolean _unify_test(TypeVar tv) {
    if( tv instanceof TVar ) return tv._unify_test(this);
    if( !(tv instanceof TTupN) ) return false; // Fails unification
    TTupN tn = (TTupN)tv;
    // Structural unification
    throw com.cliffc.aa.AA.unimpl();
  }

  // Unify this into tv.
  @Override public void _unify(TypeVar tv) {
    if( tv instanceof TVar ) { tv._unify(this); return; }
    if( !(tv instanceof TTupN) )
      throw com.cliffc.aa.AA.unimpl(); // Fails unification
    TTupN tn = (TTupN)tv;
    // Structural unification
    throw com.cliffc.aa.AA.unimpl();
  }

  // Pretty print
  @Override public SB _str(SB sb, boolean pretty) {
    sb.p("[");
    for( int i=0; i<_n; i++ )
      _tnode.tvar(i)._str(sb,pretty).p(",");
    return sb.unchar().p("]");
  }
}
