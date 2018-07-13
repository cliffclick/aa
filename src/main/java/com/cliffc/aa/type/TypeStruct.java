package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import java.util.Arrays;

/** A Tuple with named fields */
public class TypeStruct extends Type {
  public String[] _args;        // The field names
  public TypeTuple _tt;         // The field types
  private TypeStruct( String[] args, TypeTuple tt ) { super(TSTRUCT); init(args,tt); }
  private void init( String[] args, TypeTuple tt ) {
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
    SB sb = new SB().p("@{");
    for( int i=0; i<_args.length; i++ ) {
      sb.p(_args[i]==null ? "^" : (_args[i].isEmpty() ? "_" : _args[i]) );
      if( _tt.at(i) != TypeErr.ALL ) sb.p(':').p(_tt.at(i).toString());
      sb.p(',');
    }
    if( _tt._inf!=TypeErr.ALL ) sb.p(_tt._inf.toString()).p("...");
    return sb.p("}").toString();
  }

  private static TypeStruct FREE=null;
  private TypeStruct free( TypeStruct f ) { FREE=f; return this; }
  private static TypeStruct make1( String[] args, TypeTuple tt ) {
    TypeStruct t1 = FREE;
    if( t1 == null ) t1 = new TypeStruct(args,tt);
    else { FREE = null; t1.init(args,tt); }
    TypeStruct t2 = (TypeStruct)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }

  // Canonicalize.  Tuple will clean out trailing fields that match the _inf.
  // Similarly, clean out trailing args that match the tuple default.  If no
  // args remain, drop to a tuple.
  public static Type make( String[] args, TypeTuple tt ) {
    int i;
    for( i=args.length-1; i>=0; i-- ) {
      String darg = defarg(tt.at(i));
      if( args[i]==null ) { if( darg!=null ) break; }
      else if( !args[i].equals(darg) )       break;
    }
    if( i==args.length-1 ) return make1(args,tt);
    if( i== -1 ) return tt; // No args other than the default, so drop to a tuple
    return make1(Arrays.copyOf(args,i+1),tt);
  }

  private static final TypeStruct POINT = make1(new String[]{"x","y"},TypeTuple.FLT64_FLT64);
  public  static final TypeStruct X     = make1(new String[]{"x"},TypeTuple.FLT64);
  private static final TypeStruct A     = make1(new String[]{"a"},TypeTuple.FLT64);
  static         final TypeStruct C0    = make1(new String[]{"c"},TypeTuple.make_all(TypeInt.NULL)); // @{c:0}
  static         final TypeStruct D1    = make1(new String[]{"d"},TypeTuple.make_all(TypeInt.TRUE)); // @{d:1}
  static final TypeStruct[] TYPES = new TypeStruct[]{POINT,X,A,C0,D1};

  // Dual the args, dual the tuple
  @Override protected TypeStruct xdual() {
    String[] as = Arrays.copyOf(_args,_args.length);
    for( int i=0; i<as.length; i++ ) as[i]=sdual(as[i]);
    TypeTuple xt = (TypeTuple)_tt.dual();
    return xt==_tt && Arrays.equals(as,_args) ? this : new TypeStruct(as,xt);
  }

  // Standard Meet.  Tuple-meet-Tuple and arg-meet-arg.  Empty arg string
  // counts as bottom; null arg string counts as top.
  @Override protected Type xmeet( Type t ) {
    TypeTuple tt;  String[] args;
    switch( t._type ) {
    case TSTRUCT: {
      tt  = ((TypeStruct)t)._tt;
      args= ((TypeStruct)t)._args;
      break;
    }
    case TTUPLE : {
      // values above_center get a top-string; those below get a bottom-string
      tt = (TypeTuple)t;
      args = new String[tt._ts.length];
      for( int i=0; i<tt._ts.length; i++ ) args[i]=defarg(tt._ts[i]);
      break;
    }
    case TNAME:
    case TUNION: return t.xmeet(this); // Let TypeUnion decide
    case TSTR:   return Type.OOP;
    case TFLT:
    case TINT:   return t.may_be_null() && !(t instanceof TypeName) ? TypeUnion.make_null(this) : SCALAR;
    case TRPC: 
    case TFUN:   return TypeErr.SCALAR;
    case TERROR: return ((TypeErr)t)._all ? t : this;
    default: throw typerr(t);   // All else should not happen
    }
    TypeTuple mtt = (TypeTuple)_tt.meet(tt); // Tuples just meet
    return _args.length < args.length
      ? xmeet1(_args, _tt, args, mtt)
      : xmeet1( args,  tt,_args, mtt);
  }
  
  private Type xmeet1(String[] amin, TypeTuple ttmin, String[] amax, TypeTuple mtt ) {
    String argmin = defarg(ttmin._inf);
    String[] as = Arrays.copyOf(amax,amax.length);
    int i=0;
    for( ; i<amin.length; i++ ) as[i] = smeet(amax[i],amin[i]);
    for( ; i<amax.length; i++ ) as[i] = smeet(amax[i],argmin);
    return make(as, mtt);
  }
  // Default arg (top or bottom) if no arg is available
  static String defarg( Type t ) { return ((t.above_center() && t!=Type.XCTRL)) ? null : ""; }
  // String meet; empty string is bottom; null is top
  static String smeet( String s0, String s1 ) {
    if( s0==s1 ) return s0;
    if( s0==null ) return s1;
    if( s1==null ) return s0;
    if( s0.isEmpty() ) return s0;
    if( s1.isEmpty() ) return s1;
    if( s0.equals(s1) ) return s0;
    return "";
  }
  static String sdual( String s ) {
    if( s==null ) return "";
    if( s.isEmpty() ) return null;
    return s;
  }

  // Return the index of the matching field, or -1 if not found
  public int find( String fld ) {
    for( int i=0; i<_args.length; i++ )
      if( fld.equals(_args[i]) )
        return i;
    return -1;
  }
  
  @Override public boolean above_center() { return false; }
  // True if all internals canBeConst
  @Override public boolean canBeConst() { return _tt.canBeConst(); }
  // True if all internals is_con
  @Override public boolean is_con() { return _tt.is_con(); }
  @Override public boolean may_be_null() { return false; }
  @Override public String errMsg() { return _tt.errMsg(); }
}
