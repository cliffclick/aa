package com.cliffc.aa;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;

import java.util.Comparator;

// Type union is a meet (or join) of unrelated SCALAR types.  Specifically it
// simplifies out overlapping choices, such as {Flt64*Flt32} :=: Flt64.
public class TypeUnion extends Type {
  public TypeTuple _ts;         // All of these are possible choices
  public boolean _any; // FALSE: meet; must support all; TRUE: join; can pick any one choice
  private TypeUnion( TypeTuple ts, boolean any ) { super(TUNION); init(ts,any); }
  private void init( TypeTuple ts, boolean any ) { _ts = ts;  _any=any;  assert !ts.has_tuple(); }
  @Override public int hashCode( ) { return TUNION+_ts.hashCode()+(_any?1:0);  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeUnion) ) return false;
    TypeUnion t = (TypeUnion)o;
    return _any==t._any && _ts==t._ts;
  }
  @Override public String toString() { return "{"+(_any?"any":"all")+_ts+"}"; }
  private static TypeUnion FREE=null;
  private TypeUnion free( TypeUnion f ) { FREE=f; return this; }
  public static TypeUnion make( TypeTuple ts, boolean any ) {
    TypeUnion t1 = FREE;
    if( t1 == null ) t1 = new TypeUnion(ts,any);
    else { FREE = null; t1.init(ts,any); }
    TypeUnion t2 = (TypeUnion)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }

  // Common cleanup rules on making new unions
  static Type make( boolean any, Type... ts ) { return make(any,new Ary<>(ts)); }
  private static Type make( boolean any, Ary<Type> ts ) {
    if( ts._len == 0 ) throw AA.unimpl();   //return any ? Type.ANY : Type.ALL;
    // Special rules now apply to keep from growing out all combos of
    // e.g. float-constants.  All {float,int,str} types are meeted and
    // their meet replaces them.
    int fx=-1, ix=-1, sx=-1, ux=-1;
    for( int i=0; i<ts._len; i++ ) {
      Type t = ts._es[i];
      if( t._type == Type.TFLT ) {
        if( fx==-1 ) fx=i;
        else { ts._es[fx] = ts._es[fx].meet(t); ts.del(i--);  }
      }
      if( t._type == Type.TINT ) {
        if( ix==-1 ) ix=i;
        else { ts._es[ix] = ts._es[ix].meet(t); ts.del(i--);  }
      }
      if( t._type == Type.TSTR ) {
        if( sx==-1 ) sx=i;
        else { ts._es[sx] = ts._es[sx].meet(t); ts.del(i--);  }
      }
      if( t._type == Type.TFUN ) ux = i;
    }
    // Also, if the remaining int fits in the remaining float, drop the int
    if( fx!=-1 && ix!=-1 && (((TypeInt)ts._es[ix])._z<<1) <= ((TypeFlt)ts._es[fx])._z && ((TypeFlt)ts._es[fx])._x==-1 )
      ts.del(ix);
    // Cannot mix functions and numbers
    if( ux != -1 && (fx!=-1 || ix!=-1 || sx!=-1) )
      return Type.SCALAR;

    if( ts._len == 1 ) return ts._es[0]; // A single result is always that result
    // The set has to be ordered, to remove dups that vary only by order
    ts.sort_update(Comparator.comparingInt(e -> e._uid)); 
    return make(TypeTuple.make(any?TypeErr.ANY:TypeErr.ALL,1.0,ts.asAry()),any);
  }

  static final TypeUnion ANY_NUM = (TypeUnion)make(true , TypeInt.INT64, TypeFlt.FLT64);
  static final TypeUnion ALL_NUM = (TypeUnion)make(false, TypeInt.INT64, TypeFlt.FLT64);
  static final TypeUnion[] TYPES = new TypeUnion[]{ANY_NUM,ALL_NUM};

  @Override protected TypeUnion xdual() { return new TypeUnion((TypeTuple)_ts.dual(),!_any); }
  
  // TypeUnion can have any type on the right, including base types and another
  // TypeUnion.  Think of a TypeUnion as a list with either add/any/join/'+' or
  // mul/all/meet/'*' operations between elements; as is traditional, we use
  // juxtaposition for mul/all/meet/'*'.  xmeet() is a mul/meet operation
  // itself.  "this" is either [A+B] or [AB], and xmeet(t) computes [A+B]C or
  // [AB]C, where C might be any type including e.g. a union of either [C+D] or [CD].
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TERROR: return ((TypeErr)t)._all ? t : this;
    case TTUPLE: return TypeErr.ALL; // Tuple-vs-scalar
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
        Type[] anyts = tany._ts._ts;
        Ary<Type> ts = new Ary<>(new Type[anyts.length],0);
        for( Type anyt : anyts ) ts.add(tu.meet(anyt));
        return make(true, full_simplify(ts,true));

      } else if( !_any ) {
        // [AB][CD] ==> [ABCD]
        Ary<Type> ts = new Ary<>(_ts._ts.clone());
        for( Type tx : tu._ts._ts )
          ymeet(ts,false,tx);
        return make(false, ts);
      } else {
        // Meet of 2 joins: [A+B][C+D] ==> [AC+BC+AD+BD]
        Ary<Type> ts = new Ary<>(new Type[_ts._ts.length*tu._ts._ts.length],0);
        for( Type tht : _ts._ts )
          for( Type tut : tu._ts._ts )
            ts.add(tht.meet(tut));
        return make(_any, full_simplify(ts,_any));
      }
    }
    default:                    // Unions can handle all non-union internal types
      Ary<Type> ts = ymeet( new Ary<>(_ts._ts.clone()), _any, t );
      return make(_any, ts);
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

  @Override public Type ret() {
    Ary<Type> rets = new Ary<>(Type.class);
    for( int i=0; i<_ts._ts.length; i++ )
      rets.add(((TypeFun)_ts._ts[i])._ret);
    return make(_any,full_simplify(rets,_any));
  }
  @Override protected boolean canBeConst() { return _any && _ts.canBeConst(); }
  @Override public boolean above_center() {
    if( _any ) {
      for( Type t : _ts._ts )
        if( t.above_center() )
          return true;
      return false;
    } else {
      for( Type t : _ts._ts )
        if( !t.above_center() )
          return false;
      return true;
    }
  }
  // Lattice of conversions:
  // -1 unknown; top; might fail, might be free (Scalar->Int); Scalar might lift
  //    to e.g. Float and require a user-provided rounding conversion from F64->Int.
  //  0 requires no/free conversion (Int8->Int64, F32->F64)
  // +1 requires a bit-changing conversion (Int->Flt)
  // 99 Bottom; No free converts; e.g. Flt->Int requires explicit rounding
  @Override public byte isBitShape(Type t) {
    if( t._type == Type.TSCALAR ) return 0;
    return 99;
    //throw AA.unimpl();
  }
  // Filter out functions with the wrong args; error for non-functions
  @Override public Type filter(int nargs) {
    if( _any ) {
      Type j = TypeErr.ALL;
      for( Type t : _ts._ts )
        if( t.filter(nargs)!=null )
          j = j.join(t);
      return j;
    }
    throw AA.unimpl();
  }

  // Return non-zero if allowed to be infix
  @Override public byte op_prec() { return _ts.at(0).op_prec(); }
  // Better error message
  public String errMsg() {
    assert _any;                // Expect only function choice here
    TypeFun tf = (TypeFun)_ts.at(0);
    String name = tf.funnode()._name;
    SB sb = new SB().p(name).p(':').p('[');
    for( Type t : _ts._ts )
      ((TypeFun)t).str(sb).p(',');
    return sb.p(']').toString();
  }
}
