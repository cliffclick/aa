package com.cliffc.aa.tvar;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.TNode;
import org.jetbrains.annotations.NotNull;

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

  private Type _type;           // Base/ground Type

  // Basic H-M type variable supporting U-F and parametric types.
  public TVar( @NotNull TNode tn ) { super(tn); _type=Type.ALL; }

  // Base type from Node
  @Override public Type _type(boolean head) {
    assert !head || _u==null;
    return _type;
  }

  //
  public Type setype( Type t ) { return _type = t; }

  // Unify this into tv.
  @Override public Object unify(TypeVar tv) {
    assert !_tnode.is_dead() && !tv._tnode.is_dead();
    _u = tv;
    if( tv._uf_kids==null ) tv._uf_kids = new Ary<TVar>(new TVar[1],0);
    if( _uf_kids != null )  tv._uf_kids.addAll(_uf_kids);
    return tv._uf_kids.push(this);
  }
  
  // U-F find algo
  @Override public TypeVar find() {
    if( _u==null ) return this;
    if( !(_u instanceof TVar) || ((TVar)_u)._u==null ) return _u;
    throw com.cliffc.aa.AA.unimpl();
  }
  
  // Pretty print
  @Override public SB _str(SB sb, boolean pretty) {
    if( _u!=null ) {
      if( !pretty ) sb.p("V").p(uid()).p(">>");
      return _u._str(sb,pretty);
    }
    sb.p("V").p(uid());
    if( _type!=Type.ANY )
      _type.str(sb.p(":"),new VBitSet(),null,false);
    return sb;
  }
}
