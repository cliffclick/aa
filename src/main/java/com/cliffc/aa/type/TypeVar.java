package com.cliffc.aa.type;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.TNode;
import org.jetbrains.annotations.NotNull;

// Type of a Var, for something like Hindley-Milner parametric polymorphism.
// A TypeVar has a base type from its Var.  TypeVars can be unified (or in
// the same congruence class); the base Type is then the JOIN (not MEET) of all
// unified base types.  Other Types can have TypeVar parts, indicating which
// sub-parts have to have the same Type.  Example for the classic Identity
// function: TypeFunSig(formals:TypeStruct(disp,TypeVar A),ret:TypeVar A).

public class TypeVar {
  @NotNull private final TNode _tnode;   // Abstract view of a Node

  // Either: HEAD of U-F; _u==null, _uf_child set
  // OR:     TAIL of U-F; _u==HEAD, _uf_child null
  private TypeVar _u;           // Tarjan Union-Find; null==HEAD
  private Ary<TypeVar> _uf_child;// List of union children.  Used for computing JOIN of children.

  private Type _type;           // Base/ground Type

  public TypeVar( @NotNull TNode tn ) { _tnode=tn; _type=Type.ALL; }
  public int uid() { return _tnode.uid(); }


  // TVar: _u,_type[,_tnode][,_uid]
  // TOper:
  // TFun: _args[],_ret
  // TStruct: _flds[]
  // TArray: _elem


  // Base type from Node
  public Type type() { return find()._type(); }
  private Type _type() {
    assert _u==null;
    assert !_tnode.is_dead();
    if( _uf_child==null || _uf_child._len==0 ) return _type;
    Type t = _type;
    for( int i=0; i<_uf_child._len; i++ ) {
      TypeVar tv = _uf_child.at(i);
      if( tv._tnode.is_dead() ) {
        _uf_child.del(i--);
        continue;
      }
      assert tv._u==this;
      t = t.join(tv._type);
      throw com.cliffc.aa.AA.unimpl(); // UNTESTED
    }
    return t;
  }

  //
  public Type setype( Type t ) { return _type = t; }

  // Unify tv into this.
  public void unify(TypeVar tv) {
    assert !_tnode.is_dead();
    assert tv._u==null;
    assert !tv._tnode.is_dead();
    if( tv._uf_child != null && tv._uf_child._len>0 )  throw com.cliffc.aa.AA.unimpl(); // Copy children forward
    if( _uf_child==null ) _uf_child = new Ary<TypeVar>(new TypeVar[1],0);
    tv._u=this;
    _uf_child.push(tv);
  }

  // U-F find algo
  public TypeVar find() {
    if( _u==null ) return this;
    if( _u._u==null ) return _u;
    throw com.cliffc.aa.AA.unimpl();
  }
}
