package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.SB;

import java.util.Arrays;
import java.util.BitSet;

/** A Tuple with named fields */
public class TypeStruct extends TypeTuple<TypeStruct> {
  // Fields are named in-order and aligned with the Tuple values.  Field names
  // are never null, and never zero-length.  If the 1st char is a '^' the field
  // is Top; a '.' is Bot; all other values are valid field names.
  public String[] _args;        // The field names
  private TypeStruct( boolean any, Type[] ts, Type inf, String[] args ) { super(TSTRUCT, any, ts,inf); init(any,ts,inf,args); }
  private void init ( boolean any, Type[] ts, Type inf, String[] args ) {
    super.init(TSTRUCT, any, ts,inf);
    _args=args;
  }
  
  @Override public int hashCode( ) { return super.hashCode() + Arrays.hashCode(_args);  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    return o instanceof TypeStruct && eq((TypeStruct)o) && Arrays.equals(_args,((TypeStruct)o)._args);
  }
  String str( BitSet dups) {
    SB sb = new SB();
    if( _any ) sb.p('~');
    sb.p('@').p('{');
    for( int i=0; i<_args.length; i++ ) {
      sb.p(_args[i]);
      if( at(i) != ALL ) sb.p(':').p(at(i).str(dups));
      sb.p(',');
    }
    if( _inf!=ALL ) sb.p(_inf.str(dups)).p("...");
    sb.p('}');
    return sb.toString();
  }

  private static TypeStruct FREE=null;
  @Override protected TypeStruct free( TypeStruct ret ) { FREE=this; return ret; }
  private static TypeStruct make1( boolean any, Type[] ts, Type inf, String[] args ) {
    TypeStruct t1 = FREE;
    if( t1 == null ) t1 = new TypeStruct(any,ts,inf,args);
    else { FREE = null; t1.init(any,ts,inf,args); }
    TypeStruct t2 = (TypeStruct)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  // Canonicalize.  Tuple will clean out trailing fields that match the _inf.
  // Similarly, clean out trailing args that match the tuple default.  If no
  // args remain, drop to a tuple.
  private static TypeTuple makeS( boolean any, Type[] ts, Type inf, String[] args ) {
    // Remove trailing duplicates of inf
    int len = ts.length;
    while( len > 0 && ts[len-1] == inf ) len--;
    if( len < ts.length ) ts = Arrays.copyOf(ts,len);
    // Remove trailing default args
    String ttarg = sarg(inf);    // default arg from tuple is either top or bottom
    int i;
    for( i=args.length-1; i>=0; i-- )
      if( !args[i].equals(ttarg) )
        break;
    if( i== -1 ) return make(inf,1.0f,ts); // No args other than the default, so drop to a tuple
    return make1(any,ts,inf, i==args.length-1 ? args : Arrays.copyOf(args,i+1));
  }
  private static String[] flds(String... fs) { return fs; }
  public  static TypeStruct makeX(String[] flds, Type... ts ) { return (TypeStruct)makeS(false,ts,SCALAR,flds); }
  public  static TypeStruct makeA(String[] flds, Type... ts ) { return (TypeStruct)makeS(false,ts,ALL   ,flds); }

  private static final TypeStruct POINT = makeA(flds("x","y"),TypeFlt.FLT64,TypeFlt.FLT64);
  public  static final TypeStruct X     = makeX(flds("x"),TypeFlt.FLT64); // @{x:flt,~Scalar...}
  private static final TypeStruct A     = makeX(flds("a"),TypeFlt.FLT64);
  private static final TypeStruct C0    = makeA(flds("c"),TypeNil.SCALAR); // @{c:0}
  private static final TypeStruct D1    = makeA(flds("d"),TypeInt.TRUE ); // @{d:1}
  static final TypeStruct[] TYPES = new TypeStruct[]{POINT,X,A,C0,D1};

  // Dual the args, dual the tuple
  @Override protected TypeStruct xdual() {
    String[] as = new String[_args.length];
    for( int i=0; i<as.length; i++ ) as[i]=sdual(_args[i]);
    Type  [] ts = new Type  [_ts  .length];
    for( int i=0; i<ts.length; i++ ) ts[i] = _ts[i].dual();
    return new TypeStruct(!_any,ts,_inf.dual(),as);
  }

  // Standard Meet.  Tuple-meet-Tuple and arg-meet-arg.  Empty arg string
  // counts as bottom; null arg string counts as top.
  @Override protected Type xmeet( Type t ) {
    TypeTuple tt;   String[] args;
    switch( t._type ) {
    case TSTRUCT:  args= ((TypeStruct)t)._args;  tt=(TypeTuple)t;  break;
    case TTUPLE :  args= new String[0];          tt=(TypeTuple)t;  break;
    case TSTR:   return OOP;
    case TFLT:
    case TINT:
    case TFUNPTR:
    case TFUN:
    case TRPC:   return SCALAR;
    case TOOP:
    case TNIL:
    case TNAME:  return t.xmeet(this); // Let other side decide
    default: throw typerr(t);   // All else should not happen
    }

    Type inf = _inf.meet(tt._inf);
    int max = Math.max(Math.max(_args.length,args.length),Math.max(_ts.length,tt._ts.length));
    String[] as = new String[max];
    Type  [] ts = new Type  [max];
    for( int i=0; i<max; i++ ) {
      ts[i] = at(i).meet(tt.at(i));
      as[i] = smeet(sat(_args,i,this),sat(args,i,tt));
    }
    return makeS(_any&&tt._any,ts,inf,as);
  }
  
  static private boolean argTop( String s ) { return s.charAt(0)=='^'; }
  static private boolean argBot( String s ) { return s.charAt(0)=='.'; }
  // Return field name, using the default from the field type if no field name
  // is available.
  private static String sat( String[] args, int i, TypeTuple tt ) {
    return i < args.length ? args[i] : sarg(tt._inf);
  }
  // Default arg (top or bottom) if no arg is available
  private static String sarg( Type t ) { return ((t.above_center() && t!=XCTRL)) ? "^" : "."; }
  // String meet
  private static String smeet( String s0, String s1 ) {
    if( argTop(s0) ) return s1;
    if( argTop(s1) ) return s0;
    if( argBot(s0) ) return s0;
    if( argBot(s1) ) return s1;
    if( s0.equals(s1) ) return s0;
    return "."; // argBot
  }
  private static String sdual( String s ) {
    if( argTop(s) ) return ".";
    if( argBot(s) ) return "^";
    return s;
  }

  // Return the index of the matching field, or -1 if not found
  public int find( String fld ) {
    for( int i=0; i<_args.length; i++ )
      if( fld.equals(_args[i]) )
        return i;
    return -1;
  }

  // True if isBitShape on all bits
  @Override public byte isBitShape(Type t) {
    if( isa(t) ) return 0; // Can choose compatible format
    if( t instanceof TypeName ) return 99; // Cannot pick up a name, requires user converts
    throw AA.unimpl();
  }
}
