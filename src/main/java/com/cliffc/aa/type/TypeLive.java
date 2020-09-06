package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.function.Predicate;

// Backwards liveness, used to gather forward use types in a reverse flow.
public class TypeLive extends TypeObj<TypeLive> {
  int _flags;
  private TypeLive (boolean any, int flags ) { super     (TLIVE,"",any); init(any,flags); }
  private void init(boolean any, int flags ) { super.init(TLIVE,"",any); _flags = flags;  }
  @Override int compute_hash() { return super.compute_hash() + _flags;  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeLive) || !super.equals(o) ) return false;
    return _flags==((TypeLive)o)._flags;
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override public SB str( SB sb, VBitSet dups, TypeMem mem, boolean debug ) {
    if( _flags==  0 && !_any ) return sb.p( "LIVE");
    if( _flags== -1 &&  _any ) return sb.p("~LIVE");
    if( _any ) sb.p('~');
    if( (_flags&FLAG_ESCAPE)!=0 ) sb.p("ESCP");
    return sb;
  }
  
  private static TypeLive FREE=null;
  @Override protected TypeLive free( TypeLive ret ) { FREE=this; return ret; }
  private static TypeLive make( boolean any, int flags ) {
    TypeLive t1 = FREE;
    if( t1 == null ) t1 = new TypeLive(any,flags);
    else {   FREE = null;      t1.init(any,flags); }
    TypeLive t2 = (TypeLive)t1.hashcons();
    if( t1!=t2 ) return t1.free(t2);
    return t1;
  }

  // Value is used as a call-argument, value-stored (address use is ok),
  // returned merged at a phi, folded into a funptr, etc.
  private static final int FLAG_ESCAPE=1;
  public boolean is_escape() { return (_flags&FLAG_ESCAPE)!=0; }

  public static final TypeLive LIVE   = make(false,0); // Basic alive
  static final TypeLive ESCAPE = make(false,FLAG_ESCAPE); // Used as a call argument
  static final TypeLive LIVE_BOT=make(false,FLAG_ESCAPE);
  public static final TypeLive DEAD   = LIVE_BOT.dual();
  static final TypeLive[] TYPES = new TypeLive[]{LIVE,ESCAPE};

  @Override protected TypeLive xdual() { return new TypeLive(!_any,_flags); }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TLIVE:   break;
    case TARY:
    case TSTR:
    case TSTRUCT:return OBJ;
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
    boolean any = _any&ts._any;
    int f0 =    _any ? 0 :    _flags;
    int f1 = ts._any ? 0 : ts._flags;
    int flags = any ? (_flags&ts._flags) : (f0|f1);
    return make(any,flags);
  }
  private static final TypeLive[] LIVES = new TypeLive[]{LIVE,ESCAPE};
  public TypeLive lmeet( TypeLive lv ) {
    if( this.above_center() ) return lv.above_center() ? (TypeLive)xmeet(lv) : lv;
    if( lv  .above_center() ) return this;
    return LIVES[_flags|lv._flags];
  }
  @Override public TypeObj st_meet(TypeObj obj) { throw com.cliffc.aa.AA.unimpl(); }
  // Widen (loss info), to make it suitable as the default function memory.
  @Override public TypeObj crush() { return this; }

  @Override public boolean may_be_con() { return false; }
  @Override public boolean is_con() { return false; }
  @Override public Type meet_nil(Type t) { return this; }
  @Override void walk( Predicate<Type> p ) { p.test(this); }
}
