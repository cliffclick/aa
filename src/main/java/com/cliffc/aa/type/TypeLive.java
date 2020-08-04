package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.function.Predicate;

// Backwards liveness, used to gather forward use types in a reverse flow.
public class TypeLive extends TypeObj<TypeLive> {
  private int _flags;
  private TypeLive (boolean any, boolean esc, int flags ) { super(TLIVE,"",any,esc); init(any,esc,flags); }
  private void init(boolean any, boolean esc, int flags ) {
    super.init(TLIVE,"",any,esc);
    _flags = flags;
  }
  @Override int compute_hash() { return super.compute_hash() + _flags;  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeLive) || !super.equals(o) ) return false;
    return _flags==((TypeLive)o)._flags;
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( VBitSet dups) {
    if( _flags==  0 && !_any ) return "LIVE";
    if( _flags== -1 &&  _any ) return "~LIVE";
    SB sb = new SB();
    if( _any ) sb.p('~');
    if( (_flags&FLAG_ESCAPE)!=0 ) sb.p("ESCAPE");
    
    return sb.toString();
  }
  private static TypeLive FREE=null;
  @Override protected TypeLive free( TypeLive ret ) { FREE=this; return ret; }
  private static TypeLive make( boolean any, boolean esc, int flags ) {
    TypeLive t1 = FREE;
    if( t1 == null ) t1 = new TypeLive(any,esc,flags);
    else {   FREE = null;      t1.init(any,esc,flags); }
    TypeLive t2 = (TypeLive)t1.hashcons();
    if( t1!=t2 ) return t1.free(t2);
    return t1;
  }

  // Value is used as a call-argument, value-stored (address use is ok),
  // returned merged at a phi, folded into a funptr, etc.
  private static final int FLAG_ESCAPE=1;
  
  static final TypeLive BASIC  = make(false,true,0); // Basic alive
  static final TypeLive ESCAPE = make(false,true,FLAG_ESCAPE); // Used as a call argument
  static final TypeLive[] TYPES = new TypeLive[]{BASIC};

  @Override protected TypeLive xdual() { return new TypeLive(!_any,!_esc,~_flags); }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TLIVE:   break;
    case TSTR:
    case TSTRUCT:return OBJ.make_from_esc(_esc|((TypeObj)t)._esc);
    case TOBJ:   return t.xmeet(this);
    case TFUNSIG:
    case TTUPLE:
    case TFUNPTR:
    case TMEMPTR:
    case TFLT:
    case TINT:
    case TRPC:
    case TMEM:   return ALL;
    default: throw typerr(t);
    }
    TypeLive ts = (TypeLive)t;
    return make(_any&ts._any,_esc|ts._esc,_flags|ts._flags);
  }
  @Override protected TypeLive make_from_esc_impl( boolean esc) { return make(_any,esc,_flags); }
  @Override public TypeObj st_meet(TypeObj obj) { throw com.cliffc.aa.AA.unimpl(); }
  // Widen (loss info), to make it suitable as the default function memory.
  @Override public TypeObj crush() { return this; }

  @Override public boolean may_be_con() { return false; }
  @Override public boolean is_con() { return false; }
  @Override public Type meet_nil(Type t) { return this; }
  @Override void walk( Predicate<Type> p ) { p.test(this); }
}
