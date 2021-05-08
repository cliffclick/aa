package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.function.Predicate;

import static com.cliffc.aa.AA.unimpl;

// A collection of top-level simple types, either a meet-of-joins or a join-of-
// meets, to make the lattice distributed.  A meet of ~Ctrl and ~Scalar will
// fall to... (~Ctrl meet ~Scalar) and not ALL.
public class TypeCombo extends Type<TypeCombo> {

  // True=join, False=meet
  boolean _any;
  // Local types, being joined or meeted
  Type[] _ts;

  // Combo-lattice descriptor; does not change in a meet.
  // Local bottom types of independent lattices; the meet of any two of these
  // will yield _bot, but any number of them can be joined accurately.
  // Last element is the meet of all member types.
  Type[] _bots;

  static final Type[] INTFLTS = new Type[]{Type.SCALAR,TypeInt.INT64,TypeFlt.FLT64};

  private TypeCombo( boolean any, Type[] ts, Type[] bots ) { super(TDIST); init(any,ts,bots); }
  private void init( boolean any, Type[] ts, Type[] bots ) { super.init(TDIST); assert bots.length==ts.length+1; _any=any; _ts = ts; _bots = bots; }
  // Hash does not depend on other types
  @Override int compute_hash() { return super.compute_hash()+(_any?0:1)+_ts[0]._hash+_bots[0]._hash; }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeCombo) ) return false;
    TypeCombo t2 = (TypeCombo)o;
    if( _ts!=t2._ts && _ts.length==t2._ts.length ) {
      boolean ok=false;
      for( int i=0; i<_ts.length; i++ )
        if( _ts[i]!=t2._ts[i] )
          { ok=true; break; }
      assert ok;
    }
    return super.equals(o) && _any==t2._any && _ts==t2._ts && _bots==t2._bots;
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }

  @Override public SB str( SB sb, VBitSet dups, TypeMem mem, boolean debug ) {
    sb.p('[');
    for( Type t : _ts )
      t.str(sb,dups,mem,debug).p(_any?" + " : " & ");
    return sb.unchar(2).p(']');
  }

  private static TypeCombo FREE=null;
  @Override protected TypeCombo free( TypeCombo ret ) { FREE=this; _ts=null; return ret; }
  private static TypeCombo make( boolean any, Type[] ts, Type[] bots ) {
    assert ts.length+1==bots.length;
    Type[] ts2 = Types.hash_cons(ts);
    TypeCombo t1 = FREE;
    if( t1 == null ) t1 = new TypeCombo(any,ts2,bots);
    else {  FREE = null;       t1.init (any,ts2,bots); }
    TypeCombo t2 = (TypeCombo)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }


  static Type make_intflts( TypeInt t0, TypeFlt t1 ) {
    if( t0==TypeInt.INT64.dual() && t1==TypeFlt.FLT64.dual() )
      //return make(false,Types.ts(TypeInt.INT64.dual(),TypeFlt.FLT64.dual()),INTFLTS);
    //if( t0.above_center() && t1.above_center() )
      //if( t0==TypeInt.INT64.dual() && t1==TypeFlt.FLT64.dual() )
      return make(false,Types.ts(t0,t1),INTFLTS);
    return Type.SCALAR;
  }

  static public final TypeCombo MEET_HI = (TypeCombo)make_intflts(TypeInt.INT64.dual(),TypeFlt.FLT64.dual());
  static final TypeCombo[] TYPES = new TypeCombo[]{MEET_HI};

  @Override protected TypeCombo xdual() {
    Type[] ts = Types.clone(_ts);
    for( int i=0; i<ts.length; i++ )
      ts[i] = _ts[i].dual();
    ts = Types.hash_cons(ts);
    return new TypeCombo(!_any,ts,_bots);
  }
  @Override protected Type xmeet( Type t ) {
    assert t != this;
    Type[] clat;
    int idx=-1;
    switch( t._type ) {
    case TINT:  clat = INTFLTS; idx=0; break;
    case TFLT:  clat = INTFLTS; idx=1; break;
    case TDIST: clat = ((TypeCombo)t)._bots; break;
    default: throw typerr(t);
    }
    // Mismatched combo lattices
    Type bot = _bots[_bots.length-1];
    if( _bots != clat ) return bot.meet(clat[clat.length-1]);
    // Two combos?
    if( idx==-1 ) {
      TypeCombo tc = (TypeCombo)t;
      // If both are high, keep meeting
      if( !_any || !tc._any  ) return bot;
      Type[] ts = Types.clone(_ts);
      for( int i=0; i<ts.length; i++ )
        ts[i] = _ts[i].meet(tc._ts[i]);
      return make(true,ts,_bots);
    }



    if( above_center() ) {
      return _ts[idx].meet(t);
    } else {
    //  if( t.above_center() ) {
    //    return t.dual();
    //  } else {
    //  }
    }
    throw unimpl();
  }

  @Override public boolean above_center() { return _any; }
  @Override void walk( Predicate<Type> p ) { p.test(this); }
}
