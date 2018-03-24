package com.cliffc.aa;

import java.util.Arrays;
import java.util.HashMap;

/** an implementation of language AA
 */

// C2-style type system, with Meet & Dual.  Symmetric around the centerline of
// constants.  Fixed height, so a finite count of Meet stablizes; a unique All
// (Bottom; no known value) and due to symmetry a unique Any (Top, all values
// simultaneously).  Support function types, various kinds of numeric ranges,
// null and a Object Oriented single-inheritance hierarchy.
//
// During program typing, always keeping the "loosest" possible program and if
// this program still types as 'Any' then the program is ambiguious.  'All'
// represents a type conflict.
//
// During parsing, we come to places where conversions *may* be added - to
// allow for matching primitives.  We add all possible overloaded function
// combinations to get the "loosest" program (i.e., both +:Flt and +:Int).

public class Type {
  static private int CNT=1;
  final int _uid=CNT++; // Unique ID, will have gaps, used to uniquely order Types in Unions
  protected byte _type; // Simple types use a simple enum
  private Type _dual;   // All types support a dual notion, lazily computed and cached here

  protected Type(byte type) { _type=type; }
  @Override public int hashCode( ) { return _type; }
  // Is anything equals to this?
  @Override public boolean equals( Object o ) {
    assert isBaseType();      // Overridden in subclasses
    if( this == o ) return true;
    return (o instanceof Type) ? _type==((Type)o)._type : false;
  }
  @Override public String toString() { return STRS[_type]; }

  // Object Pooling to handle frequent (re)construction of temp objects being
  // interned.  One-entry pool for now.
  private static Type FREE=null;
  private Type free( Type f ) { FREE=f; return this; }
  static Type make( byte type ) {
    Type t1 = FREE;
    if( t1 == null ) t1 = new Type(type);
    else { FREE = null; t1._type = type; }
    Type t2 = t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }
  // Hash-Cons - all Types are interned in this hash table.  Thus an equality
  // check of a (possibly very large) Type is always a simple pointer-equality
  // check, except during construction and intern'ing.
  private static HashMap<Type,Type> INTERN = new HashMap<>();
  protected Type hashcons() {
    Type t2 = INTERN.get(this); // Lookup
    if( t2!=null ) {            // Found prior
      assert t2._dual != null;  // Prior is complete with dual
      assert t2 != this;        // Not hash-consing twice
      return t2;                // Return prior
    }
    // Not in type table
    _dual = null;                // No dual yet
    INTERN.put(this,this);       // Put in table without dual
    Type d = _dual = xdual();    // Compute dual without requiring table lookup
    if( this==d ) return d;      // Self-symmetric?  Dual is self
    assert !equals(d);           // If self symmetric then returned self
    assert d._dual==null;        // Else dual-dual not computed yet
    assert INTERN.get(d)==null;
    d._dual = this;
    INTERN.put(d,d);
    return this;
  }

  static final byte TBAD    =-1; // Type check
  // Implemented fully here
  static final byte TALL    = 0; // Bottom; all possible types Meet together
  static final byte TANY    = 1; // Top; dual of All
  static final byte TSCALAR = 2; // Scalars; all possible finite types; includes pointers (functions, structs), ints, floats; excludes state of Memory.  
  static final byte TXSCALAR= 3; // Invert scalars
  static final byte TNUM    = 4; // Number and all derivitives (Complex, Rational, Int, Float, etc)
  static final byte TXNUM   = 5; // Any Numbers; dual of NUM
  static final byte TREAL   = 6; // All Real Numbers
  static final byte TXREAL  = 7; // Any Real Numbers; dual of REAL
  static final byte TBASE   = 8; // End of the Base Types; Not a Type
  private static final String[] STRS = new String[]{"All","Any","Scalar","~Scalar","Number","~Number","Real","~Real"};
  // Implemented in subclasses
  static final byte TUNION  = 9; // Union types (finite collections of unrelated types Meet together); see TypeUnion
  static final byte TTUPLE  =10; // Tuples; finite collections of unrelated Types, kept in parallel
  static final byte TFUN    =11; // Functions; both domain and range are a Tuple; see TypeFun                            
  static final byte TFLT    =12; // All IEEE754 Float Numbers; 32- & 64-bit, and constants and duals; see TypeFlt
  static final byte TINT    =13; // All Integers, including signed/unsigned and various sizes; see TypeInt
  static final byte TLAST   =14; // Type check
  
  static final Type ALL    = make(TALL    ); // Bottom
  static final Type ANY    = make(TANY    ); // Top
  static final Type  SCALAR= make( TSCALAR); // ptrs, ints, flts; things that fit in a machine register
  static final Type XSCALAR= make(TXSCALAR); // ptrs, ints, flts; things that fit in a machine register
  static final Type  NUM   = make( TNUM   );
  static final Type XNUM   = make(TXNUM   );
  static final Type  REAL  = make( TREAL  );
  static final Type XREAL  = make(TXREAL  );

  // Collection of sample types for checking type lattice properties.
  // Ordered so dual can be computed by flipping pairs.
  static final Type[] TYPES = new Type[]{ALL,ANY,SCALAR,XSCALAR,NUM,XNUM,REAL,XREAL};
  
  byte base() { assert TBAD < _type && _type < TLAST; return _type; }
  
  // Return cached dual
  public final Type dual() { return _dual; }
  
  // Compute dual right now.  Overridden in subclasses.
  protected Type xdual() {
    assert isBaseType(); // Should be overridden in subclass
    assert TBAD < _type && _type < TBASE;
    return new Type((byte)(_type^1));
  }

  public final Type meet( Type t ) {
    Type mt = xmeet0(t);
    //assert check_commute  (t,mt);
    //assert check_symmetric(t,mt);
    return mt;
  }
  private Type xmeet0( Type t ) {
    if( t == this ) return this;
    if(_type != TUNION &&
       ( _type >  TBASE  && t._type <  TBASE || // Reverse; xmeet 2nd arg is never <TBASE
         t._type == TUNION ))   // Reverse: always TypeUnion decides
      return t.xmeet(this);
    return xmeet(t);            // Do not reverse
  }
  
  // Compute meet right now.  Overridden in subclasses.
  // Handles cases where 'this._type' < TBASE.
  // Subclassed xmeet calls can assert that '!t.isBase()'.
  protected Type xmeet(Type t) {
    // 'this' is not Tuple, Union, Fun, Flt nor Int
    assert isBaseType() && t._type != TUNION; // Should be overridden in subclass
    // Bottom meet anything is Bottom
    if( _type == TALL || t._type == TALL ) return ALL;
    // Top meet anything is that thing
    if(   _type == TANY ) return t   ;
    if( t._type == TANY ) return this;

    // The rest of these choices are various scalars, which do not match well
    // with any tuple.
    if( t._type == TTUPLE ) return ALL;

    // Scalar is close to bottom: everything falls to SCALAR, except Bottom
    // (handled above) and multi-types like Tuples
    if( _type == TSCALAR || t._type == TSCALAR )  return SCALAR;
    
    // ~Scalar is close to Top: it falls to anything, except multi-types like Tuples.
    if(   _type == TXSCALAR ) return t   ;
    if( t._type == TXSCALAR ) return this;

    // The rest of these choices are various numbers, which do not match well
    // with any function - but all are scalars, so make a union.
    if( t._type == TFUN ) return SCALAR; // return TypeUnion.make(false,this,t);
    
    // Numeric; same pattern as ANY/ALL, or SCALAR/XSCALAR
    if( _type == TNUM || t._type == TNUM ) return NUM;
    if(   _type == TXNUM ) return t   ;
    if( t._type == TXNUM ) return this;

    // Real; same pattern as ANY/ALL, or SCALAR/XSCALAR
    if( _type == TREAL || t._type == TREAL ) return REAL;
    if(   _type == TXREAL ) return t   ;
    if( t._type == TXREAL ) return this;

    throw AA.unimpl();          // Need nice printout
  }

  // By design in meet, args are already flipped to order _type, which forces
  // symmetry for things with badly ordered _type fields.  The question is
  // still interesting for other orders.
  private boolean check_commute( Type t, Type mt ) {
    if( t==this ) return true;
    if( _type <  TBASE  && t._type >  TBASE  ) return true; // By design, flipped the only allowed order
    if( _type == TUNION && t._type != TUNION ) return true; // By design, flipped the only allowed order
    Type mt2 = t.xmeet(this);   // Reverse args and try again
    if( mt==mt2 ) return true;
    System.out.println("Meet not commutative: "+this+".meet("+t+")="+mt+", but "+t+".meet("+this+")="+mt2);
    return false;
  }
  private boolean check_symmetric( Type t, Type mt ) {
    if( t==this ) return true;
    Type ta = mt._dual.xmeet0(t._dual);
    Type tb = mt._dual.xmeet0(  _dual);
    if( ta==t._dual && tb==_dual ) return true;
    System.out.print("("+this+"&"+t+")="+mt+"; but ("+mt._dual+"&");
    if( ta!=t._dual ) System.out.println(t._dual+")=="+ta+" which is not "+t._dual);
    else              System.out.println(  _dual+")=="+tb+" which is not "+  _dual);
    return false;
  }
  
  Type join( Type t ) { return dual().meet(t.dual()).dual(); }

  static boolean check_startup() {
    Type[] ts =    Type     .TYPES ;
    ts = concat(ts,TypeInt  .TYPES);
    ts = concat(ts,TypeFlt  .TYPES);
    ts = concat(ts,TypeTuple.TYPES);
    ts = concat(ts,TypeFun  .TYPES);
    ts = concat(ts,Prim     .TYPES);
    ts = concat(ts,TypeUnion.TYPES);
    
    // Confirm commutative & complete
    for( Type t0 : ts )
      for( Type t1 : ts ) {
        Type mt = t0.meet(t1);
        assert t0.check_commute  (t1,mt);
        assert t0.check_symmetric(t1,mt);
      }
    
    // Confirm associative
    int errs=0;
    for( Type t0 : ts )
      for( Type t1 : ts )
        for( Type t2 : ts ) {
          Type t01   = t0 .meet(t1 );
          Type t12   = t1 .meet(t2 );
          Type t01_2 = t01.meet(t2 );
          Type t0_12 = t0 .meet(t12);
          if( t01_2 != t0_12 && errs++ < 10 )
            System.err.println("("+t0+"&"+t1+") & "+t2+" == "+t0+" & ("+t1+" & "+t2+"); "+
                               "("+t01      +") & "+t2+" == "+t0+" & ("+t12        +"); "+
                               t01_2                  +" == "+t0_12);
        }
    assert errs==0 : "Found "+errs+" non-associative-type errors";
    return true;
  }
  private static Type[] concat( Type[] ts0, Type[] ts1 ) {
    Type[] ts = Arrays.copyOf(ts0,ts0.length+ts1.length);
    System.arraycopy(ts1,0,ts,ts0.length,ts1.length);
    return ts;
  }
  
  // True if 'this' isa/subtypes 't2'.  E.g. Int32-isa-Int64, but not vice-versa
  boolean isa( Type t ) { return meet(t)==t; }
  // True if 'this' isa SCALAR, without the cost of a full 'meet()'
  final boolean isa_scalar() {
    return _type != TALL && _type != TANY && _type != TUNION && _type != TTUPLE;
  }
  
  // Return any "return type" of the Meet of all function types
  protected Type ret() { return null; }
  // Return a long   from a TypeInt constant; assert otherwise.
  protected long   getl() { throw AA.unimpl(); }
  // Return a double from a TypeFlt constant; assert otherwise.
  protected double getd() { throw AA.unimpl(); }
  // Function name
  protected String funame() { return ""; }
  // True if value is higher-equal to SOME constant.
  protected boolean canBeConst() {
    switch( _type ) {
    case TALL:
    case TSCALAR:
    case TNUM:
    case TREAL:
      return false;             // These all include not-constant things
    case TXREAL:
    case TXNUM:
    case TXSCALAR:
    case TANY:
      return true;              // These all include some constants
      
    case TFUN:                  // Overridden in subclass
    case TUNION:                // Overridden in subclass
    case TTUPLE:                // Overridden in subclass
    case TFLT:                  // Overridden in subclass
    case TINT:                  // Overridden in subclass
    default: throw AA.unimpl();
    case TBASE: throw typerr(null);
    }
  }
  protected boolean is_con() {
    switch( _type ) {
    case TALL:
    case TSCALAR:
    case TNUM:
    case TREAL:
    case TXREAL:
    case TXNUM:
    case TXSCALAR:
    case TANY:
    case TUNION:                // Overridden in subclass
      return false;             // Not exactly a constant
    case TFUN:                  // Always exactly 1 function choice
      return true;
    case TTUPLE:                // Overridden in subclass
    case TFLT:                  // Overridden in subclass
    case TINT:                  // Overridden in subclass
    default: throw AA.unimpl();
    case TBASE: throw typerr(null);
    }
  }
  // -1 for non-functions; 0 to 9; 9 binds more tightly than 0
  int op_prec() { return -1; }
  protected boolean is_pure() { return false; }
  protected Type remove_choice( Prog[] args ) { return null; }
  protected boolean isBitShape(Type t) { throw typerr(t); } // Overridden in subtypes
  // True if a base type
  private boolean isBaseType() { return getClass().getSimpleName().equals("Type"); }
  
  public RuntimeException typerr(Type t) {
    throw new RuntimeException("Should not reach here: internal type system error with "+this+(t==null?"":(" and "+t)));
  }
}
