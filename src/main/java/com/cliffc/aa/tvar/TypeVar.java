package com.cliffc.aa.tvar;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.TNode;
import org.jetbrains.annotations.NotNull;

// Type of a Var, for something like Hindley-Milner parametric polymorphism.  A
// TypeVar holds the base type for its Node.  TypeVars can be unified (or in
// the same congruence class); the base Type is then the JOIN (not MEET) of all
// unified base types.  Other Types can have TypeVar parts, indicating which
// sub-parts have to have the same Type.  Example for the classic Identity
// function: TypeFunSig(formals:TypeStruct(disp,TypeVar A),ret:TypeVar A).

abstract public class TypeVar {
  @NotNull final TNode _tnode; // Abstract view of a Node
  Ary<TVar> _uf_kids; // List of union children.  Used for computing JOIN of children.
  public TypeVar( @NotNull TNode tn ) { _tnode=tn; }
  public int uid() { return _tnode.uid(); }
  // Base type from Node
  public Type type() { return find()._type0(); }
  // Top-of-UF type.  Finds self-type, plus join of all children
  Type _type0() {
    assert !_tnode.is_dead();
    Type t0 = Type.ALL;
    if( _uf_kids!=null )        // Join of all children
      for( int i=0; i<_uf_kids._len; i++ ) {
        TVar tv = _uf_kids.at(i);
        if( tv._tnode.is_dead() )  // Lazily strip out dead children
          _uf_kids.del(i--);
        else 
          t0 = t0.join(tv._type(false));
      }
    Type t1 = _type(true);      // Self type
    Type t2 = t0.join(t1);
    return t2;
  }
  abstract public Type _type(boolean head); // Local type as UF root
  // Unify this into tv.
  abstract public Object unify(TypeVar tv);
  abstract TypeVar find();

  // Debug
  public final String toString() { return _str(new SB(),false).toString(); }
  abstract SB _str(SB sb, boolean pretty); 
}
