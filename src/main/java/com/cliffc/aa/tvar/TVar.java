package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import org.jetbrains.annotations.NotNull;

import static com.cliffc.aa.AA.unimpl;

// Type of a Var, for something like Hindley-Milner parametric polymorphism.  A
// TypeVar holds the base type for its Node.  TypeVars can be unified (or in
// the same congruence class); the base Type is then the JOIN (not MEET) of all
// unified base types.  Other Types can have TypeVar parts, indicating which
// sub-parts have to have the same Type.  Example for the classic Identity
// function: TypeFunSig(formals:TypeStruct(disp,TypeVar A),ret:TypeVar A).

public class TVar extends TypeVar {
  // Either: HEAD of U-F; _u==null, _uf_kids set with list of children
  // OR:     TAIL of U-F; _u==HEAD, _uf_kids null
  private TypeVar _u;           // Tarjan Union-Find; null==HEAD

  // Basic H-M type variable supporting U-F and parametric types.
  public TVar( @NotNull TNode tn ) { super(tn); ; }

  // Base type from Node
  @Override public Type _type(boolean head) {
    assert !head || _u==null;
    return _tnode.val();
  }

  // Test no fails during unification
  @Override boolean _unify_test(TypeVar tv) {
    return true;
  }
  // Unify this into tv.
  @Override public void _unify(TypeVar tv) {
    if( tv==this ) return;      // Already unioned
    if( tv._tnode.is_dead() ) {
      assert !_tnode.is_dead(); // top of union is alive
      tv._unify(this);
      return;
    }
    _u = tv;
    if( tv._uf_kids==null ) tv._uf_kids = new Ary<>(new TVar[1],0);
    if( _uf_kids != null )  tv._uf_kids.addAll(_uf_kids);
    tv._uf_kids.push(this);
    _uf_kids=null;
  }

  // U-F find algo
  @Override public TypeVar find() {
    if( _u==null ) return this;
    if( !(_u instanceof TVar) || ((TVar)_u)._u==null ) return _u;
    throw unimpl();
  }

  // Pretty print
  @Override public SB _str(SB sb, boolean pretty) {
    if( _u!=null ) {
      if( !pretty ) sb.p("V").p(uid()).p(">>");
      return _u._str(sb,pretty);
    }
    sb.p("V").p(uid());
    //_tnode.val().str(sb.p(":"),new VBitSet(),null,true);
    return sb;
  }
}
