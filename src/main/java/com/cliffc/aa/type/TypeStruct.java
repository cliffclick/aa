package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;

import java.util.BitSet;
import java.util.function.Consumer;

/** A memory-based Tuple with optionally named fields.  This is a recursive
 *  type, only produced by NewNode and structure or tuple constants.
 */
public class TypeStruct extends TypeOop<TypeStruct> {
  // Fields are named in-order and aligned with the Tuple values.  Field names
  // are never null, and never zero-length.  If the 1st char is a '^' the field
  // is Top; a '.' is Bot; all other values are valid field names.
  public String[] _args;        // The field names
  public Type[] _ts;            // Matching field types
  // If NewNode UID is present, then this type may be self-recursive, and is
  // updated in-place at every new call to NewNode value.  If nuid is zero,
  // then this type is NOT self-recursive but has been explicitly declared.
  // Note that TypeName may include a non-self-recursive Struct but the
  // TypeName itself IS recursive.
  int _nuid;         // Always unique by node-id
  private int _hash; // Hash pre-computed to avoid large computes duing interning
  private TypeStruct( boolean any, String[] args, Type[] ts, int nuid ) { super(TSTRUCT, any); init(any,args,ts,nuid); }
  private void init ( boolean any, String[] args, Type[] ts, int nuid ) {
    super.init(TSTRUCT, any);
    _args=args;
    _ts=ts;
    _nuid=nuid;
    int sum=super.hashCode();
    for( Type t : ts ) sum += t.hashCode();
    _hash=nuid==0?sum:nuid;
  }
  
  @Override public int hashCode( ) { return _hash; }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeStruct) ) return false;
    TypeStruct t = (TypeStruct)o;
    if( _nuid !=0 || t._nuid != 0 ) // Only matching on nuid, if present
      return _nuid == t._nuid && _any==t._any; 
    if( _any!=t._any || _hash != t._hash || _ts.length != t._ts.length )
      return false;
    if( _ts == t._ts && _args == t._args ) return true;
    for( int i=0; i<_ts.length; i++ )
      if( _ts[i]!=t._ts[i] || !_args[i].equals(t._args[i]) )
        return false;
    return true;
    
  }
  String str( BitSet dups) {
    if( _nuid != 0 ) {          // Only for recursive-structs
      if( dups == null ) dups = new BitSet();
      else if( dups.get(_uid) ) return "*"; // Break recursive cycle
      dups.set(_uid);
    }
    SB sb = new SB();
    if( _any ) sb.p('~');
    boolean is_tup = _args.length==0 || argTop(_args[0]) || argBot(_args[0]);
    if( !is_tup ) sb.p('@');
    sb.p(is_tup ? '(' : '{');
    for( int i=0; i<_args.length; i++ ) {
      if( !is_tup ) sb.p(_args[i]);
      if( !is_tup && at(i) != SCALAR ) sb.p(':');
      if( at(i) != SCALAR ) sb.p(at(i).str(dups));
      if( i<_args.length-1 ) sb.p(',');
    }
    sb.p(!is_tup ? '}' : ')');
    return sb.toString();
  }

  // Unlike other types, TypeStruct never makes dups - instead it might make
  // cyclic types for which a DAG-like bottom-up-remove-dups approach cannot work.
  private static TypeStruct FREE=null;
  @Override protected TypeStruct free( TypeStruct ret ) { FREE=this; return ret; }
  private static TypeStruct make1( int nuid, boolean any, String[] args, Type[] ts ) {
    TypeStruct t1 = FREE;
    if( t1 == null ) t1 = new TypeStruct(any,args,ts,nuid);
    else { FREE = null; t1.init(any,args,ts,nuid); }
    TypeStruct t2 = (TypeStruct)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  // Default tuple field names
  private static final String[] FLD0={};
  private static final String[] FLD1={"."};
  private static final String[] FLD2={".","."};
  private static final String[] FLD3={".",".","."};
  private static final String[][] FLDS={FLD0,FLD1,FLD2,FLD3};
  public  static       String[] FLDS( int len ) { return FLDS[len]; }
  private static String[] flds(String... fs) { return fs; }
  private static Type[] ts(Type... ts) { return ts; }
  public  static TypeStruct make(int nuid, Type... ts               ) { return make1(nuid,false,FLDS[ts.length],ts); }
  public  static TypeStruct make(int nuid, String[] flds, Type... ts) { return make1(nuid,false,flds           ,ts); }

  private static final TypeStruct POINT = make(0,flds("x","y"),ts(TypeFlt.FLT64,TypeFlt.FLT64));
  public  static final TypeStruct X     = make(0,flds("x"),ts(TypeFlt.FLT64 )); // @{x:flt}
  public  static final TypeStruct TFLT64= make(0          ,ts(TypeFlt.FLT64 )); //  (  flt)
  private static final TypeStruct A     = make(0,flds("a"),ts(TypeFlt.FLT64 ));
  private static final TypeStruct C0    = make(0,flds("c"),ts(TypeNil.SCALAR)); // @{c:0}
  private static final TypeStruct D1    = make(0,flds("d"),ts(TypeInt.TRUE  )); // @{d:1}
  static final TypeStruct[] TYPES = new TypeStruct[]{POINT,X,A,C0,D1};

  // Making a (potentially) recursive type
  public static TypeStruct make_recursive(int nuid, String[] flds, Type... ts ) {
    assert nuid !=0;
    boolean eq=true;
    TypeStruct tstr = make(nuid,flds,ts);
    for( int i=0; i<ts.length; i++ )
      if( tstr._ts[i]!=ts[i] )
        { eq=false; break; }
    if( eq ) return tstr;
    // Update the TypeStruct in-place, which definitely changes it identity,
    // and would change the hash if the hash depended on it's contents.  Since
    // this is a recursive structure, the hash is only based on the unique
    // NewNode id.
    for( int i=0; i<ts.length; i++ )
      tstr._ts[i] = tstr._ts[i].meet(ts[i]);
    return tstr;
  }
  
  // Dual the args, dual the tuple
  @Override protected TypeStruct xdual() {
    String[] as = new String[_args.length];
    for( int i=0; i<as.length; i++ ) as[i]=sdual(_args[i]);
    Type  [] ts = new Type  [_ts  .length];
    for( int i=0; i<ts.length; i++ ) ts[i] = _ts[i].dual();
    return new TypeStruct(!_any,as,ts,_nuid);
  }

  // Standard Meet.  Types-meet-Types and arg-meet-arg.  Arg strings can be
  // top/bottom (for tuples).
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TSTRUCT:break;
    case TTUPLE :
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

    // If unequal length; then if short is low it "wins" (result is short) else
    // short is high and it "loses" (result is long).
    TypeStruct tt = (TypeStruct)t;
    return _ts.length < tt._ts.length ? xmeet1(tt) : tt.xmeet1(this);
  }
  
  // Meet 2 structs, shorter is 'this'
  private TypeStruct xmeet1( TypeStruct tmax ) {
    int len = _any ? tmax._ts.length : _ts.length;
    // Meet of common elements
    String[] as = new String[len];
    Type  [] ts = new Type  [len];
    for( int i=0; i<_ts.length; i++ ) {
      as[i] = smeet(_args[i],tmax._args[i]);
      ts[i] = _ts[i].meet(tmax._ts[i]);
    }
    // Elements only in the longer tuple
    for( int i=_ts.length; i<len; i++ ) {
      as[i] = tmax._args[i];
      ts[i] = tmax._ts[i];
    }
    // nuid: a "low" 0 wins, and a "high" 0 loses, and if they are equal then
    // thats the answer.
    int nuid = _nuid;
    if( nuid!=tmax._nuid ) {
      if( nuid!=0 && tmax._nuid!=0 ) {
        nuid = 0;
      } else {
        // Exactly one is zero
        if( _nuid==0 ) {
          nuid = _any ? tmax._nuid : 0; // if high 0, take the other side
        } else {
          nuid = tmax._any ? _nuid : 0; // if high 0, take the other side
        }
      }
    }
    return make1(nuid,_any&tmax._any,as,ts);
  }

  static private boolean argTop( String s ) { return s.charAt(0)=='^'; }
  static private boolean argBot( String s ) { return s.charAt(0)=='.'; }
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

  public Type at( int idx ) { return _ts[idx]; }

  // True if isBitShape on all bits
  @Override public byte isBitShape(Type t) {
    if( isa(t) ) return 0; // Can choose compatible format
    if( t.isa(this) ) return 0; // TODO: really: test same args, each arg isBitShape
    if( t instanceof TypeName ) return 99; // Cannot pick up a name, requires user converts
    return 99;
  }
  @Override TypeStruct make_recur(TypeName tn, int d, BitSet bs ) {
    boolean eq = true;
    for( Type t : _ts )
      eq = eq && t.make_recur(tn,d,bs)==t;
    if( eq ) return this;
    // Build a depth-limited version of the same struct
    Type[] ts = new Type[_ts.length];
    for( int i=0; i<_ts.length; i++ )
      ts[i] = _ts[i].make_recur(tn,d,bs);
    return make(_nuid,_args,ts);
  }
  // Iterate over any nested child types
  @Override public void iter( Consumer<Type> c ) { for( Type t : _ts) c.accept(t); }
}
