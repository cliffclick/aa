package com.cliffc.aa.type;

import com.cliffc.aa.util.Ary;
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
  private int _hash; // Hash pre-computed to avoid large computes duing interning
  private TypeStruct _recursive;        // Only set during recursive-meets
  private TypeStruct     ( boolean any, String[] args, Type[] ts ) { super(TSTRUCT, any); init(any,args,ts); }
  private TypeStruct init( boolean any, String[] args, Type[] ts ) {
    super.init(TSTRUCT, any);
    _args=args;
    _ts=ts;
    int sum=super.hashCode();
    for( String fld : _args ) sum += fld.hashCode();
    _hash= sum;
    return this;
  }

  private static Ary<TypeStruct> CYCLES = new Ary<>(new TypeStruct[0]);
  private TypeStruct find_other() {
    int idx = CYCLES.find(this);
    return idx != -1 ? CYCLES.at(idx^1) : null;
  }
  
  @Override public int hashCode( ) { return _hash; }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeStruct) ) return false;
    TypeStruct t = (TypeStruct)o;
    if( _any!=t._any || _hash != t._hash || _ts.length != t._ts.length )
      return false;
    if( _ts == t._ts && _args == t._args ) return true;
    for( int i=0; i<_ts.length; i++ )
      if( !_args[i].equals(t._args[i]) )
        return false;

    // Unlike all other non-cyclic structures which are built bottom-up, cyclic
    // types have to be built all-at-once, and thus hash-cons and equality-
    // tested with a cyclic-aware equals check.
    return cycle_equals(t);
  }
  @Override public boolean cycle_equals( Type o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeStruct) ) return false;
    TypeStruct t = (TypeStruct)o;
    TypeStruct t2 = find_other();
    if( t2 !=null ) return t2==t; // Already in cycle report equals or not
    TypeStruct t3 = t.find_other();
    if( t3 !=null ) return t3==this;// Already in cycle report equals or not
    if( _any!=t._any || _hash != t._hash || _ts.length != t._ts.length )
      return false;
    if( _ts == t._ts && _args == t._args ) return true;
    for( int i=0; i<_ts.length; i++ )
      if( !_args[i].equals(t._args[i]) )
        return false;
    
    int len = CYCLES._len;
    CYCLES.add(this).add(t);
    boolean eq=cycle_equals0(t);
    CYCLES.remove(len);
    CYCLES.remove(len);
    return eq;
  }
  private boolean cycle_equals0( TypeStruct t ) {
    for( int i=0; i<_ts.length; i++ )
      if( _ts[i]!=t._ts[i] &&   // Normally suffices to test ptr-equals only
          !_ts[i].cycle_equals(t._ts[i]) ) // Must do a full cycle-check
        return false;
    return true;
  }

  
  String str( BitSet dups) {
    if( dups == null ) dups = new BitSet();
    else if( dups.get(_uid) ) return "*"; // Break recursive cycle
    dups.set(_uid);

    SB sb = new SB();
    if( _any ) sb.p('~');
    boolean is_tup = _args.length==0 || argTop(_args[0]) || argBot(_args[0]);
    if( !is_tup ) sb.p('@');
    sb.p(is_tup ? '(' : '{');
    for( int i=0; i<_args.length; i++ ) {
      if( !is_tup ) sb.p(_args[i]);
      Type t = at(i);
      if( !is_tup && t != SCALAR ) sb.p(':');
      if( t != SCALAR ) sb.p(t==null ? "!" : t.str(dups));
      if( i<_args.length-1 ) sb.p(',');
    }
    sb.p(!is_tup ? '}' : ')');
    return sb.toString();
  }

  // Unlike other types, TypeStruct never makes dups - instead it might make
  // cyclic types for which a DAG-like bottom-up-remove-dups approach cannot work.
  private static TypeStruct FREE=null;
  @Override protected TypeStruct free( TypeStruct ret ) { FREE=this; return ret; }
  private static TypeStruct malloc( boolean any, String[] args, Type[] ts ) {
    if( FREE == null ) return new TypeStruct(any,args,ts);
    TypeStruct t1 = FREE;  FREE = null;
    return t1.init(any,args,ts);
  }
  private TypeStruct hashcons_free() { TypeStruct t2 = (TypeStruct)hashcons();  return this==t2 ? this : free(t2);  }

  // Default tuple field names - all bottom-field names
  private static final String[] FLD0={};
  private static final String[] FLD1={"."};
  private static final String[] FLD2={".","."};
  private static final String[] FLD3={".",".","."};
  private static final String[][] FLDS={FLD0,FLD1,FLD2,FLD3};
  public  static       String[] FLDS( int len ) { return FLDS[len]; }
  private static String[] flds(String... fs) { return fs; }
  private static Type[] ts(Type... ts) { return ts; }
  public  static TypeStruct make(Type... ts               ) { return malloc(false,FLDS[ts.length],ts).hashcons_free(); }
  public  static TypeStruct make(String[] flds, Type... ts) { return malloc(false,flds,ts).hashcons_free(); }

  public  static final TypeStruct POINT = make(flds("x","y"),ts(TypeFlt.FLT64,TypeFlt.FLT64));
  public  static final TypeStruct X     = make(flds("x"),ts(TypeFlt.FLT64 )); // @{x:flt}
  public  static final TypeStruct TFLT64= make(          ts(TypeFlt.FLT64 )); //  (  flt)
  private static final TypeStruct A     = make(flds("a"),ts(TypeFlt.FLT64 ));
  public  static final TypeStruct C0    = make(flds("c"),ts(TypeNil.SCALAR)); // @{c:0}
  private static final TypeStruct D1    = make(flds("d"),ts(TypeInt.TRUE  )); // @{d:1}
  static final TypeStruct[] TYPES = new TypeStruct[]{POINT,X,A,C0,D1};

  // Dual the args, dual the tuple
  @Override protected TypeStruct xdual() {
    if( _recursive!=null ) return _recursive; // Recursive meets pre-computed the xdual
    String[] as = new String[_args.length];
    for( int i=0; i<as.length; i++ ) as[i]=sdual(_args[i]);
    Type  [] ts = new Type  [_ts  .length];
    for( int i=0; i<ts.length; i++ ) ts[i] = _ts[i].dual();
    return new TypeStruct(!_any,as,ts);
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
    TypeStruct tt = (TypeStruct)t;

    // If a recursive meet is in-progress then return the (being computed) result
    if( _recursive!=null ) {
      assert tt._recursive==_recursive || tt._recursive==null;
      return _recursive;
    }
    if( tt._recursive!=null )
      return tt._recursive;
    
    // If unequal length; then if short is low it "wins" (result is short) else
    // short is high and it "loses" (result is long).
    return _ts.length < tt._ts.length ? xmeet1(tt) : tt.xmeet1(this);
  }
  
  // Meet 2 structs, shorter is 'this'.  Can be recursive.  Flag each of the 2
  // types involved as being part of a recursive-meet.  During the meet, if
  // either shows up again return the new Type (which is not yet built).
  private TypeStruct xmeet1( TypeStruct tmax ) {
    int len = _any ? tmax._ts.length : _ts.length;
    // Meet of common elements
    String[] as = new String[len], das = new String[len];
    Type  [] ts = new Type  [len], dts = new Type  [len];
    for( int i=0; i<_ts.length; i++ ) {
      das[i] = sdual( as[i] = smeet(_args[i],tmax._args[i]) );
      // No recursive meet... yet
      //dts[i] = ( ts[i] = _ts[i].meet(tmax._ts[i]) ).dual();
    }
    // Elements only in the longer tuple
    for( int i=_ts.length; i<len; i++ ) {
      das[i] = sdual( as[i] = tmax._args[i] );
      dts[i] = ( ts[i] = tmax._ts[i] ).dual();
    }

    // Recursive meet: make the returned structure before any meets.  Then do
    // the meets... flagged as recursive.  If either this or tmax shows up
    // recursively we'll return the rez result which will form a loop in the
    // type structures.  Notice that the recursive dual has to be computed in
    // parallel, since it will also be used in the dual internal structures.
    TypeStruct  rez= malloc(_any&tmax._any, as, ts);
    TypeStruct drez= malloc(!rez._any     ,das,dts);
    rez._dual=drez;             // Pre-compute the dual, since its needed recursively
    drez._dual=rez;
    tmax._recursive = _recursive = rez; // If either this or tmax, instead use rez
    for( int i=0; i<_ts.length; i++ ) 
      dts[i] = (ts[i] = _ts[i].meet(tmax._ts[i])).dual();
    tmax._recursive = _recursive = null;
    rez._recursive = drez; // If interning, take the computed dual directly.  See xdual
    drez._dual= null;      // Pass interning asserts
    TypeStruct tstr = rez.hashcons_free();
    rez._recursive = _recursive = null;
    return tstr;
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
  // Build a depth-limited named type
  @Override TypeStruct make_recur(TypeName tn, int d, BitSet bs ) {
    // Mid-construction recursive types are always self-type
    for( Type t : _ts )  if( t == null )  return this;
    boolean eq = true;
    Type[] ts = new Type[_ts.length];
    for( int i=0; i<_ts.length; i++ )
      eq &= (ts[i] = _ts[i].make_recur(tn,d,bs))==_ts[i];
    return eq ? this : make(_args,ts);
  }

  // Iterate over any nested child types
  @Override public void iter( Consumer<Type> c ) { for( Type t : _ts) c.accept(t); }


  // Recursive-cyclic meet: given 2 (potentially) cyclic structures do a
  // general-purpose meet preserving the largest cycles possible.  This is NOT
  // the general case of looking for equality amongst general graphs as the
  // out-edges are ordered.  Instead the problem devolves to looking at cycles
  // involving a single edge-number, counting the depth and taking e.g. the GCD
  // or LCM as the new cycle depth.  Taking the LCM allows the structure to
  // grow much more, while keeping more precision.  The cycles along each edge
  // are independent.  Non-cyclic edges use the usual MEET.
  //
  // Example:  edge0, a 1-cycle meets a 1-cycle:
  //    A->A->
  //    B->B->...
  // GCD, LCM is 1 {AB}->...
  // 
  // Example:  edge0, a 2-cycle meets a 1-cycle:
  //    A->B->A->B->...
  //    C->C->C->C->...
  // GCD is 1 {ABC}->...
  // LCM is 2 {AC}->{BC}->...
  // 
  // Example:  edge0, a 3-cycle meets a 2-cycle:
  //    A->B->C->A->B->C->
  //    D->E->D->E->D->E->
  // GCD is 1 {ABCDE}->...
  // LCM is 6 {AD}->{BE}->{CD}->{AE}->{BD}->{CE}->
  // 
  // Example:  edge0, a 4-cycle meets a 2-cycle:
  //    A->B->C->D->A->B->C->D->...
  //    E->F->E->F->...
  // GCD is 2 {ACE}->{BDF}->...
  // LCM is 4 {AE}->{BF}->{CE}->{DF}->
  //
  // NOTE: Most data structures the limit is depth 1 or at most 2.  No need to
  // solve the general case.

  
}
