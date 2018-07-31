package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.Ary;

import java.util.Arrays;
import java.util.Comparator;

// Type union is a meet (or join) of unrelated SCALAR types.  Specifically it
// simplifies out overlapping choices, such as {Flt64*Flt32} :=: Flt64.
public class TypeUnion extends Type {
  private TypeTuple _ts;         // All of these are possible choices
  private boolean _any; // FALSE: meet; must support all; TRUE: join; can pick any one choice
  private TypeUnion( TypeTuple ts, boolean any ) { super(TUNION); init(ts,any); }
  private void init( TypeTuple ts, boolean any ) { _ts = ts;  _any=any;  assert !ts.has_union_or_tuple(); }
  @Override public int hashCode( ) { return TUNION+_ts.hashCode()+(_any?1:0);  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeUnion) ) return false;
    TypeUnion t = (TypeUnion)o;
    return _any==t._any && _ts==t._ts;
  }
  //@Override public String toString() {
  //  if( _ts._ts.length==2 ) {
  //    //String s = _any?"+":"";
  //    //if( _ts.at(0)==TypeInt.NULL && _ts.at(1).is_oop() )  return _ts.at(1)+s+"?";
  //    //if( _ts.at(1)==TypeInt.NULL && _ts.at(0).is_oop() )  return _ts.at(0)+s+"?";
  //    throw AA.unimpl();
  //  }
  //  return "{"+(_any?"any":"all")+_ts+"}";
  //}
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
  public  static Type make( boolean any, Type... ts ) { return make(any,new Ary<>(ts)); }
  private static Type make( boolean any, Ary<Type> ts ) {
    if( ts._len == 0 ) throw com.cliffc.aa.AA.unimpl();   //return any ? Type.ANY : Type.ALL;
    // Special rules now apply to keep from growing out all combos of
    // e.g. float-constants.  All {float,int,str} types are meeted and
    // their meet replaces them.
    int fx=-1, ix=-1, ox=-1, ux=-1, rx=-1;
    Type[] es = ts._es;
    for( int i=0; i<ts._len; i++ ) {
      Type t = es[i];
      switch( t.simple_type() ) {
      case Type.TFUN:   ux = i;   break;
      case Type.TRPC:   rx = i;   break;
      case Type.TINT:   if( ix==-1 ) ix=i;  else  i = meet_dup(any,ts,ix,i);  break;
      case Type.TFLT:   if( fx==-1 ) fx=i;  else  i = meet_dup(any,ts,fx,i);  break;
        // All Oops, plus Scalar, Number, other weirdnesses
      default:          if( ox==-1 ) ox=i;  else  i = meet_dup(any,ts,ox,i);  break;
      }
    }
    // Also, if the remaining int fits in the remaining float, drop the int
    if( fx!=-1 && ix!=-1 ) {
      TypeInt ti = (TypeInt)es[ix].base();
      TypeFlt tf = (TypeFlt)es[fx].base();
      if( (ti._z<<1) <= tf._z && tf._x==-1 ) ts.del(ix);
    }
    if( ts._len == 1 ) return es[0]; // A single result is always that result

    // Allow null & oop (no floats, exactly 0 integer, the rest are oops).
    // Tuples are OK, and Tuples can also be function pointers.
    int ifx = -1; // index of a null, if both fx and ix are null
    if( ox!= -1 ) {
      //if( ix!=-1 && es[ix].may_be_null() ) {
      //  ts.set(ix,  es[ix].get_null()); // Set to null (incase e.g. ~Number)
      //  ifx = ix;                 // Record index of null
      //  ix = -1;                  // Ignore null in the union
      //}
      //if( fx!=-1 && es[fx].may_be_null() ) {
      //  ts.set(fx,  es[fx].get_null());  // Set to null (incase e.g. ~flt32)
      //  fx = -1;                  // Ignore null in the union
      //} else ifx = -1;            // No float index
      throw AA.unimpl();
    }

    // Cannot mix functions and anything else, including null.
    // Function pointers (which are internally TypeTuples), are
    // just fine with nulls.
    if( (ux != -1 || rx != -1) && (fx!=-1 || ix!=-1 || ox!=-1) )
      return Type.SCALAR;
    if( ox != -1 && (fx!=-1 || ix!=-1) )
      return Type.SCALAR;       // Cannot mix oops and floats/ints
    if( ox != -1 && Type.SCALAR.isa(es[ox]) )
      return es[ox];

    if( fx != -1 && ix != -1 ) {// Fall to REAL if possible
      TypeInt ti = (TypeInt)es[ix].base();
      TypeFlt tf = (TypeFlt)es[fx].base();
      if( ti==TypeInt.INT64 && tf==TypeFlt.FLT64 )
        return Type.REAL;
      //assert (ti==TypeInt.INT64 && tf==TypeFlt.FLT64 && any) ||
      //  (ti==TypeInt.INT64.dual() && tf==TypeFlt.FLT64.dual() && !any);
    }
    if( ifx >= 0 ) ts.del(ifx); // Delete extra null

    // The set has to be ordered, to remove dups that vary only by order
    ts.sort_update(Comparator.comparingInt(e -> e._uid)); 
    return make(TypeTuple.make(any?TypeErr.ANY:TypeErr.ALL,TypeTuple.NOT_NIL,ts.asAry()),any);
  }

  private static int meet_dup( boolean any, Ary<Type> ts, int idx, int i ) {
    Type tx = ts._es[idx], ti = ts._es[i];
    Type tr = any ? tx.join(ti) : tx.meet(ti);
    ts._es[idx] = tr;
    ts.del(i);
    return i-1;
  }

  // Return true if this type MAY be a nil.
  @Override public boolean may_be_nil() {
    if( _any ) {                // Any null works
      for( Type t : _ts._ts ) if(  t.may_be_nil() ) return true;
      return false;
    } else {                    // All must be null
      for( Type t : _ts._ts ) if( !t.may_be_nil() ) return false;
      return true;
    }
  }
  // Same union, minus the null
  public Type remove_null() {
    //Ary<Type> ts = new Ary<>(new Type[1],0);
    //for( Type t : _ts._ts ) if( t!=TypeInt.NULL ) ts.add(t);
    //return make(_any,ts);
    throw AA.unimpl();
  }
  
  //static public final TypeUnion NC0 = (TypeUnion)make(false, TypeFlt.PI, TypeInt.NULL);
  static final TypeUnion[] TYPES = new TypeUnion[]{};

  @Override protected TypeUnion xdual() {
    // The obvious thing is to just ask _ts for it's dual(), but Tuples are not
    // sorted and Unions are.  The dual of the current _ts may not match the sort
    // criteria, and this will lead to equal Unions with 2 different layouts.
    // Re-sort after dual'ing the members.
    Type[] ts = ((TypeTuple)_ts.dual())._ts; // Dual-tuple array
    ts = Arrays.copyOf(ts,ts.length);        // Defensive copy
    Arrays.sort(ts, 0, ts.length, Comparator.comparingInt(e -> e._uid));
    TypeTuple stt = TypeTuple.make(!_any?TypeErr.ANY:TypeErr.ALL,TypeTuple.NOT_NIL,ts);
    return new TypeUnion(stt,!_any);
  }
  
  // TypeUnion can have any type on the right, including base types and another
  // TypeUnion.  Think of a TypeUnion as a list with either add/any/join/'+' or
  // mul/all/meet/'*' operations between elements; as is traditional, we use
  // juxtaposition for mul/all/meet/'*'.  xmeet() is a mul/meet operation
  // itself.  "this" is either [A+B] or [AB], and xmeet(t) computes [A+B]C or
  // [AB]C, where C might be any type including e.g. a union of either [C+D] or [CD].
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TERROR: return ((TypeErr)t)._all ? t : this;
    case TOOP:
      //return may_be_null() ? OOP0 : SCALAR;
      throw AA.unimpl();
    case TSTR:
    case TSTRUCT:
    case TTUPLE:
      //return t.may_be_null() ? meet(TypeInt.NULL) : SCALAR; // Mixing of int/flt or functions
      throw AA.unimpl();
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
      // Look for: "OOPa+? meet OOPb"; the standard ymeet will convert this to
      // "OOPa JOIN OOPb?" basically moving the null around and making no
      // progress.  Pick up this pattern and handle it separately
      Ary<Type> ts = new Ary<>(_ts._ts.clone()); // Defensive clone
      //if( _any && t.is_oop() )                   // X+Y meet OOP?
      //  for( int i=0; i<ts._len; i++ )
      //    if( ts.at(i)==TypeInt.NULL ) { // Find the null?
      //      ts.del(i);  break;           // Remove it: compute X meet OOP instead
      //    }
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

  // Union of the "idx"th argument.  Crash if the functions
  // do not all have such an argument.
  @Override public Type arg(int idx) {
    Ary<Type> args = new Ary<>(Type.class);
    for( int i=0; i<_ts._ts.length; i++ )
      args.add(((TypeFun)_ts._ts[i])._ts.at(idx));
    return make(false,full_simplify(args,_any));
  }
  @Override public Type ret() {
    Ary<Type> rets = new Ary<>(Type.class);
    for( int i=0; i<_ts._ts.length; i++ )
      rets.add(((TypeFun)_ts._ts[i])._ret);
    return make(_any,full_simplify(rets,_any));
  }
  @Override public boolean canBeConst() { return _any && _ts.canBeConst(); }
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
  }

  // Return non-zero if allowed to be infix
  @Override public byte op_prec() { return _ts.at(0).op_prec(); }
}
