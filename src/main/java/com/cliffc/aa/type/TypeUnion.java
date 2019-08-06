package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;

import java.util.Arrays;
import java.util.BitSet;
import java.util.Comparator;

// Type union is a meet (or join) of unrelated SCALAR types.  Specifically
// using it for NIL as a JOIN of ZERO and NULL: {TypeInt.ZERO,TypeMemPtr.NIL}
public class TypeUnion extends TypeTuple {
  private static final byte TUNION = -1;
  private TypeUnion( boolean any, Type[] ts ) { super(TUNION, any, ts); }
  private void init( boolean any, Type[] ts ) { super.init(TUNION,any,ts); }
  @Override String open_parens() { return "[["; }
  @Override String clos_parens() { return "]]"; }

  private static TypeUnion FREE=null;
  protected TypeUnion free( TypeUnion ret ) { FREE=this; return ret; }
  static TypeUnion make0( boolean any, Type... ts ) {
    TypeUnion t1 = FREE;
    if( t1 == null ) t1 = new TypeUnion(any, ts);
    else { FREE = null; t1.init(any, ts); }
    assert t1._type==TUNION;
    TypeUnion t2 = (TypeUnion)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  // Common cleanup rules on making new unions
  public  static Type make( boolean any, Type... ts ) { return make(any,new Ary<>(ts)); }
  private static Type make( boolean any, Ary<Type> ts ) {
    if( ts._len == 0 ) throw com.cliffc.aa.AA.unimpl();   //return any ? Type.ANY : Type.ALL;
    // Special rules now apply to keep from growing out all combos.
    //
    // Meet all ints together; meet all floats together; if there is a Number
    // or Real, then blend the ints and floats with all the isa Number types.
    // Meet all strings together.
    //
    // Keep all unique functions.
    // Keep all unique nulls.
    //
    // Disallow all other combos.  Will loosen this later.

    //boolean all_fun=true, all_nil=true;
    //for( Type t : ts ) {
    //  if( t.simple_type() != TFUN ) all_fun=false;
    //  //if( !t.may_be_nil() ) all_nil=false;
    //  throw AA.unimpl();
    //}
    //if( !all_fun && !all_nil ) { // Collapse all the parts
    //  Type x = any ? Type.ALL : Type.ANY;
    //  for( Type t : ts ) x = any ? x.join(t) : x.meet(t);
    //  return x;
    //}

    if( ts._len == 1 ) return ts.at(0); // A single result is always that result

    // The set has to be ordered, to remove dups that vary only by order
    ts.sort_update(Comparator.comparingInt(e -> e._uid)); 
    return make0(any,ts.asAry());
  }

  public static final TypeUnion NIL = (TypeUnion)make(true, TypeMemPtr.NIL, TypeInt.FALSE);
  static final TypeUnion[] TYPES = new TypeUnion[]{NIL};

  @Override protected TypeUnion xdual() {
    // The dual of the current _ts may not match the sort criteria, and this
    // will lead to equal Unions with 2 different layouts.  Re-sort after
    // dual'ing the members.
    Type[] ts = new Type[_ts.length];
    for( int i=0; i<_ts.length; i++ ) ts[i] = _ts[i].dual();
    Arrays.sort(ts, 0, ts.length, Comparator.comparingInt(e -> e._uid));
    return new TypeUnion(!_any, ts);
  }
  
  // TypeUnion can have any type on the right, including base types and another
  // TypeUnion.  Think of a TypeUnion as a list with either add/any/join/'+' or
  // mul/all/meet/'*' operations between elements; as is traditional, we use
  // juxtaposition for mul/all/meet/'*'.  xmeet() is a mul/meet operation
  // itself.  "this" is either [A+B] or [AB], and xmeet(t) computes [A+B]C or
  // [AB]C, where C might be any type including e.g. a union of either [C+D] or [CD].
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TUNION: {
      // Handle the case where they are structurally equal
      TypeUnion tu = (TypeUnion)t;
      assert _any != tu._any || _ts!=tu._ts; // hashcons guarantees we are different here

      // Mixed case, does not really simplify but go to canonical form so
      // nested versions can simplify.
      if( _any != tu._any ) {
        // [AB][C+D] ==> [[ABC]+[ABD]]
        TypeUnion tany = this;
        if( !tany._any )  { tany = tu; tu = this; }
        Type[] anyts = tany._ts;
        Ary<Type> ts = new Ary<>(new Type[anyts.length],0);
        for( Type anyt : anyts ) ts.add(tu.meet(anyt));
        return make(true, full_simplify(ts,true));

      } else if( !_any ) {
        // [AB][CD] ==> [ABCD]
        Ary<Type> ts = new Ary<>(_ts.clone());
        for( Type tx : tu._ts )
          ymeet(ts,false,tx);
        return make(false, ts);
      } else {
        // Meet of 2 joins: [A+B][C+D] ==> [AC+BC+AD+BD]
        Ary<Type> ts = new Ary<>(new Type[_ts.length*tu._ts.length],0);
        for( Type tht : _ts )
          for( Type tut : tu._ts )
            ts.add(tht.meet(tut));
        return make(_any, full_simplify(ts,_any));
      }
    }
    default:                    // Unions can handle all non-union internal types
      Ary<Type> ts = new Ary<>(_ts.clone()); // Defensive clone
      return make(_any, ymeet( ts, _any, t ));
    }
  }

  // Given a list of Types and a Type C, meet them.  C is limited to being a SCALAR type.
  // either [A+B]C ==> [AC+BC]
  // OR     [A*B]C ==> [A*B*C]
  // Simplify the result, always returning the same Ary back
  private static Ary<Type> ymeet( Ary<Type> ts, boolean any, Type t ) {
    assert t.isa_scalar();
    if( any ) { // [A+B]C ==> [AC+BC]
      return full_simplify(ts.map_update(t::meet),any);
    } else {    // [A*B]C ==> [A*B*C]
      // If t isa any element, it is redundant and does not need to be added.
      // Otherwise, filter out elements that isa t, and append t.
      return ts.find(t::isa) == -1 ? ts.filter_update(e->!e.isa(t)).add(t) : ts;
    }
  }

  // Full O(n^2) simplify call, removing redundant members
  //
  // If 'any' is False this is a union-meet, and all types must remain.  If any
  // type A isa type B, A <= B, then B includes all the types that A does, and
  // A is redundant and can be removed.  For instance in {int32|flt64}, int32
  // <= flt64 and can be removed returning {flt64}.
  //
  // If 'any' is True this is a union-join, and all type choices must remain.
  // Again, if A <= B, A has more choices than B and then B is redundant and
  // can be removed.  
  private static Ary<Type> full_simplify( Ary<Type> ts, boolean any ) {
    assert ts._len < 20;        // Huge unions?
    for( int i=0; i<ts._len; i++ )
      for( int j=i+1; j<ts._len; j++ ) {
        Type mt = ts._es[i].meet(ts._es[j]);
        if( mt==ts._es[any ? i : j] ) { ts.del(i--); break; } // remove i, re-run j loop
        if( mt==ts._es[any ? j : i] ) { ts.del(j--);        } // remove j
      }
    return ts;
  }
}
