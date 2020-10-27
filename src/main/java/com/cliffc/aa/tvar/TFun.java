package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeTuple;
import com.cliffc.aa.util.SB;
import org.jetbrains.annotations.NotNull;

// Type of a Hindley-Milner function operator.
// "->N" for n-argument functions.

public class TFun extends TypeVar {
  final int _nargs;

  // Basic H-M type variable supporting U-F and parametric types.
  public TFun( @NotNull TNode tn, int nargs ) { super(tn); _nargs=nargs; }

  // Type from parts.  Grab the nargs (and memory) and the return and build a
  // TypeFunSig.
  @Override public Type _type(boolean head) {
    throw com.cliffc.aa.AA.unimpl();
  }

  // Unify this into tv.
  @Override public Object unify(TypeVar tv) {
    if( tv instanceof TVar ) return tv.unify(this);
    if( !(tv instanceof TFun) )
      throw com.cliffc.aa.AA.unimpl(); // Fails unification
    TFun tf = (TFun)tv;
    // Structural unification
    throw com.cliffc.aa.AA.unimpl();
  }

  // U-F find algo.  Only TVars can be a child in U-F.
  @Override TypeVar find() { return this; }
  // Pretty print
  @Override public SB _str(SB sb, boolean pretty) {
    sb.p("V").p(uid()).p("{ ");
    for( int i=0; i<_nargs; i++ )
      _tnode.targ(i)._str(sb,pretty).p(" ");
    sb.p("-> ");
    _tnode.tret()._str(sb,pretty);
    return sb.p(" }");
  }
}
