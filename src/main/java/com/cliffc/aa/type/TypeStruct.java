package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import java.util.Arrays;

/** A Tuple with named fields */
public class TypeStruct extends Type {
  private String[] _args;        // The field names
  private TypeTuple _tt;         // The field types
  private TypeStruct( String[] args, TypeTuple tt ) { super(TSTRUCT); init(args,tt); }
  private void init( String[] args, TypeTuple tt ) {
    assert args.length<=tt._ts.length;
    _args = args;
    _tt = tt;
  }
  
  @Override public int hashCode( ) { return _tt.hashCode();  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeStruct) ) return false;
    TypeStruct t = (TypeStruct)o;
    return _tt==t._tt && Arrays.equals(_args,t._args);
  }
  @Override public String toString() {
    SB sb = new SB().p("[");
    for( int i=0; i<_args.length; i++ )
      sb.p(_args[i]).p(':').p(_tt._ts[i].toString()).p(',');
    return sb.p(_tt._inf.toString()).p("...]").toString();
  }

  private static TypeStruct FREE=null;
  private TypeStruct free( TypeStruct f ) { FREE=f; return this; }
  public static TypeStruct make( String[] args, TypeTuple tt ) {
    TypeStruct t1 = FREE;
    if( t1 == null ) t1 = new TypeStruct(args,tt);
    else { FREE = null; t1.init(args,tt); }
    TypeStruct t2 = (TypeStruct)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }

  private static final TypeStruct POINT = make(new String[]{"x","y"},TypeTuple.FLT64_FLT64);
  private static final TypeStruct X     = make(new String[]{"x"},TypeTuple.FLT64);
  private static final TypeStruct A     = make(new String[]{"a"},TypeTuple.FLT64);
  static final TypeStruct[] TYPES = new TypeStruct[]{POINT,X,A};

  // No change on the arg names, but dual the type tuple
  @Override protected TypeStruct xdual() {
    TypeTuple xt = (TypeTuple)_tt.dual();
    return xt==_tt ? this : new TypeStruct(_args,xt);
  }

  // Standard Meet.
  @Override protected Type xmeet( Type t ) {
    String[] args;
    TypeTuple tt ;
    switch( t._type ) {
    case TSTRUCT: tt = ((TypeStruct)t)._tt; args = ((TypeStruct)t)._args; break;
    case TTUPLE : tt =  (TypeTuple )t     ; args = new String[0]        ; break;
    case TUNION:
    case TRPC:
    case TFLT:
    case TINT:
    case TSTR:
    case TFUN: return TypeErr.ALL;
    case TERROR: return ((TypeErr)t)._all ? t : this;
    default: throw typerr(t);   // All else should not happen
    }
    TypeTuple mtt = (TypeTuple)_tt.meet(tt); // Tuples just meet
    // Keep shorter (longer) set of matching arg names
    return _args.length < args.length ? xmeet1(_args, args,mtt) : xmeet1( args,_args,mtt);
  }
  
  private Type xmeet1(String[] amin, String[] amax, TypeTuple mtt ) {
    int i=0;
    for( ; i<amin.length; i++ )
      if( !amin[i].equals(amax[i]) )
        break;                  // Common prefix
    if( i==amin.length )        // Prefix was equal?  See if we can keep more names
      while( i<amax.length && mtt.at(i).above_center() )
        i++;             // Meet is "high", then keep longer
    if( i==0 ) return mtt;      // No names in common, fall to tuple
    if( i==amin.length ) return make(amin,mtt);
    if( i==amax.length ) return make(amax,mtt);
    return make( Arrays.copyOf(amax,i),mtt);
  }
  
  @Override public TypeTuple ret() { throw com.cliffc.aa.AA.unimpl(); }
  @Override public boolean above_center() { return false; }
  // True if all internals canBeConst
  @Override public boolean canBeConst() { return _tt.canBeConst(); }
  // True if all internals is_con
  @Override public boolean is_con() { return _tt.is_con(); }
}
