package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.function.Predicate;

// Backwards liveness, used to gather forward use types in a reverse flow.

// Liveness is passed in TypeMems, because we support precise memory liveness.
// - TypeMem.DEAD   - Value is dead
// - TypeMem.ALIVE  - Value is simple, and fully alive
// - TypeMem.ESCAPE - Value is simple, and fully alive, and "escapes" into memory or a call argument
// - TypeMem[#alias]- Value is complex memory, and partially alive based on alias# and fields.
// - TypeMem[#alias]._fld = Type.XSCALAR - This field is dead
// - TypeMem[#alias]._fld = Type. SCALAR - This field is fully alive
// - TypeMem[#alias]._fld = Type.NSCALR  - This field is partially alive: any display is dead, but all else is alive

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
    if( this==DEAD ) return sb.p("DEAD");
    if( _any ) sb.p('~');
    return sb.p(STRS[_flags]);
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
  // returned, merged at a phi, folded into a funptr, etc.
  private static final int FLAG_ESCAPE=1;
  public boolean is_escape() { return (_flags&FLAG_ESCAPE)!=0; }
  // Keeps all values alive
  private static final int FLAG_WITH_DISP=2;
  public boolean is_ret() { return (_flags&FLAG_WITH_DISP)!=0; }
  
  static final TypeLive NO_DISP= make(false,0 ); // no escape, no disp
  static final TypeLive ESC_DISP= make(false,FLAG_ESCAPE); // escape, no disp
  static final TypeLive LIVE   = make(false,FLAG_WITH_DISP); // Basic alive
  static final TypeLive ESCAPE = make(false,FLAG_ESCAPE+FLAG_WITH_DISP); // Used as a call argument
  
  public static final TypeLive LIVE_BOT=make(false,FLAG_ESCAPE+FLAG_WITH_DISP);
  public static final TypeLive DEAD   = LIVE_BOT.dual();

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
  private static final TypeLive[] LIVES = new TypeLive[]{NO_DISP,ESC_DISP,LIVE,ESCAPE};
  private static final String[] STRS = new String[]{"!dsp","esc!dsp","live","escp"};
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
