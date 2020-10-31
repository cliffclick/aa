package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.Types;
import com.cliffc.aa.type.TypeTuple;
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
  @Override public Type _type(boolean head) {
    // A N-tuple from inputs
    Type[] ts = Types.get(_n);
    for( int i=0; i<_n; i++ )
      ts[i] = _tnode.tvar(i).type();
    return TypeTuple.make(ts);
  }

  // Unify this into tv.
  @Override public Object unify(TypeVar tv) {
    if( tv instanceof TVar ) return tv.unify(this);
    if( !(tv instanceof TTupN) )
      throw com.cliffc.aa.AA.unimpl(); // Fails unification
    TTupN tn = (TTupN)tv;
    // Structural unification
    throw com.cliffc.aa.AA.unimpl();
  }

  // U-F find algo.  Only TVars can be a child in U-F.
  @Override TypeVar find() { return this; }
  // Pretty print
  @Override public SB _str(SB sb, boolean pretty) {
    sb.p("V").p(uid()).p("[");
    for( int i=0; i<_n; i++ )
      _tnode.tvar(i)._str(sb,pretty).p(",");
    return sb.unchar().p("]");
  }
}
