package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.type.TypeFunSig;
import com.cliffc.aa.type.TypeTuple;
import com.cliffc.aa.util.SB;
import org.jetbrains.annotations.NotNull;

// Type of a Hindley-Milner function operator.
// "->N" for n-argument functions.
public class TFun extends TypeVar {
  final TLambda _funargs; // Control0, Memory1, Fcn/Disp2, Arg3, Arg4, ...
  final TTupN _rez;       // Control0, Memory1, Result2

  // Basic H-M type variable supporting U-F and parametric types.
  public TFun( @NotNull TNode tn, TLambda funargs, TTupN rez ) { super(tn); _funargs=funargs; _rez=rez; }

  // Type from parts.  Grab the nargs (and memory) and the return and build a
  // TypeFunSig.
  @Override public TypeFunSig _type(boolean head) {
    @NotNull String @NotNull [] names  = _funargs._tnode.argnames();
    TypeTuple targs = _funargs._type(head);
    TypeTuple rez   = _rez    ._type(head);
    TypeFunSig fcn = TypeFunSig.make(names,targs,rez);
    return fcn;
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

  // Pretty print
  @Override public SB _str(SB sb, boolean pretty) {
    sb.p("V").p(uid()).p("{ ");
    _funargs._str(sb,pretty);
    sb.p("-> ");
    _rez._str(sb,pretty);
    return sb.p(" }");
  }
}
