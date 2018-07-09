package com.cliffc.aa.type;

import com.cliffc.aa.AA;
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
  byte _type;           // Simple types use a simple enum
  private Type _dual;   // All types support a dual notion, lazily computed and cached here

  protected Type(byte type) { _type=type; }
  @Override public int hashCode( ) { return _type; }
  // Is anything equals to this?
  @Override public boolean equals( Object o ) {
    assert is_simple();         // Overridden in subclasses
    if( this == o ) return true;
    return (o instanceof Type) && _type==((Type)o)._type;
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
  Type hashcons() {
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

  // Simple types are implemented fully here
  static final byte TCTRL   = 0; // Ctrl flow bottom
  static final byte TXCTRL  = 1; // Ctrl flow top (mini-lattice: any-xctrl-ctrl-all)
  static final byte TSCALAR = 2; // Scalars; all possible finite types; includes pointers (functions, structs), ints, floats; excludes state of Memory and Ctrl.
  static final byte TXSCALAR= 3; // Invert scalars
  static final byte TOOP    = 4; // Includes all GC ptrs; structs, arrays, strings.  Excludes functions, ints, floats
  static final byte TXOOP   = 5; // Invert oops
  static final byte TNUM    = 6; // Number and all derivitives (Complex, Rational, Int, Float, etc)
  static final byte TXNUM   = 7; // Any Numbers; dual of NUM
  static final byte TREAL   = 8; // All Real Numbers
  static final byte TXREAL  = 9; // Any Real Numbers; dual of REAL
  static final byte TSIMPLE =10; // End of the Simple Types
  private static final String[] STRS = new String[]{"Ctrl","~Ctrl","Scalar","~Scalar","OOP","~OOP","Number","~Number","Real","~Real"};
  // Implemented in subclasses
  static final byte TERROR  =11; // ALL/ANY TypeErr types
  static final byte TUNION  =12; // Union types (finite collections of unrelated types Meet together); see TypeUnion
  static final byte TNAME   =13; // Union types (finite collections of unrelated types Meet together); see TypeUnion
  static final byte TTUPLE  =14; // Tuples; finite collections of unrelated Types, kept in parallel
  static final byte TSTRUCT =15; // Structs; tuples with named fields
  static final byte TFUN    =16; // Functions; both domain and range are a Tuple; see TypeFun                            
  static final byte TRPC    =17; // Return PCs; Continuations; call-site return points; see TypeRPC
  static final byte TFLT    =18; // All IEEE754 Float Numbers; 32- & 64-bit, and constants and duals; see TypeFlt
  static final byte TINT    =19; // All Integers, including signed/unsigned and various sizes; see TypeInt
  static final byte TSTR    =20; // String type
  static final byte TLAST   =21; // Type check
  
  public  static final Type CTRL   = make( TCTRL  ); // Ctrl
  public  static final Type XCTRL  = make(TXCTRL  ); // Ctrl
  public  static final Type  SCALAR= make( TSCALAR); // ptrs, ints, flts; things that fit in a machine register
  public  static final Type XSCALAR= make(TXSCALAR); // ptrs, ints, flts; things that fit in a machine register
  public  static final Type  OOP   = make( TOOP   ); // ptrs subject to GC (excludes e.g. function pointers)
  public  static final Type XOOP   = make(TXOOP   ); // ptrs subject to GC
  public  static final Type  NUM   = make( TNUM   );
  public  static final Type XNUM   = make(TXNUM   );
  public  static final Type  REAL  = make( TREAL  );
  private static final Type XREAL  = make(TXREAL  );

  // Collection of sample types for checking type lattice properties.
  private static final Type[] TYPES = new Type[]{CTRL,XCTRL,SCALAR,XSCALAR,OOP,XOOP,NUM,XNUM,REAL,XREAL};
  
  // The complete list of primitive types that are disjoint and also is-a
  // SCALAR; nothing else is a SCALAR except what is on this list (or
  // subtypes).  Useful when type-specializing functions to break SCALAR args
  // into a concrete list of specific types.  Specifically excludes e.g.
  // TypeTuple - these may be passed as a scalar reference type in the future
  // but for now Tuples explicitly refer to multiple values, and a SCALAR is
  // exactly 1 value.  
  static /*final*/ Type[] SCALAR_PRIMS;
  
  private boolean is_simple() { return _type < TSIMPLE; }
  // Strip off any subclassing just for names
  private byte simple_type() {
    Type t = this;
    while( t._type == TNAME ) t = ((TypeName)t)._t;
    return t._type;
  }
  public  boolean is_oop() { byte t = simple_type();  return t == TOOP || t == TXOOP || t == TSTR || t == TSTRUCT || t == TTUPLE; }
  private boolean is_num() { byte t = simple_type();  return t == TNUM || t == TXNUM || t == TREAL || t == TXREAL || t == TINT || t == TFLT; }
  // True if 'this' isa SCALAR, without the cost of a full 'meet()'
  final boolean isa_scalar() { return _type != TERROR && _type != TCTRL && _type != TXCTRL; }
  
  // Return cached dual
  public final Type dual() { return _dual; }
  
  // Compute dual right now.  Overridden in subclasses.
  protected Type xdual() {
    assert is_simple();
    return new Type((byte)(_type^1));
  }

  public final Type meet( Type t ) {
    Type mt = xmeet0(t);
    // Expensive asserts in an common place, turn off when stable
    //assert check_commute  (t,mt);
    //assert check_symmetric(t,mt);
    return mt;
  }
  private Type xmeet0( Type t ) {
    if( t == this ) return this;
    // Reverse; xmeet 2nd arg is never <TSIMPLE
    return !is_simple() && t.is_simple() ? t.xmeet(this) : xmeet(t);
  }
  
  // Compute meet right now.  Overridden in subclasses.
  // Handles cases where 'this.is_simple()' and unequal to 't'.
  // Subclassed xmeet calls can assert that '!t.is_simple()'.
  protected Type xmeet(Type t) {
    assert is_simple(); // Should be overridden in subclass
    // ANY meet anything is thing; thing meet ALL is ALL
    if( t==TypeErr.ANY ) return this;
    if( t==TypeErr.ALL ) return    t;
    // Errors "win" over everything else
    if( t instanceof TypeErr ) return t.above_center() ? this : t;

    // Ctrl can only meet Ctrl, XCtrl or Top
    byte type = (byte)(_type|t._type); // the OR is low if both are low
    if(  type <= TXCTRL ) return _type==TXCTRL && t._type==TXCTRL ? XCTRL : CTRL;
    if( _type <= TXCTRL || t._type <= TXCTRL ) return TypeErr.ALL;

    // Scalar is close to bottom: nearly everything falls to SCALAR, except
    // Bottom (already handled) and Control (error; already handled).
    if( _type == TSCALAR || t._type == TSCALAR ) return SCALAR;

    // ~Scalar is close to Top: it falls to nearly anything.
    if(   _type == TXSCALAR ) return t   ;
    if( t._type == TXSCALAR ) return this;

    // Scalar values break out into: nums(reals (int,flt)), GC-ptrs (structs(tuples), arrays(strings)), fun-ptrs, RPC

    if( t._type == TFUN ) return SCALAR; // If 't' is a FUN and 'this' is not a FUN (because not equal to 't')
    if( t._type == TRPC ) return SCALAR; // If 't' is a RPC and 'this' is not a RPC (because not equal to 't')
    // Union of functions or numbers or whatever: let Union sort it out
    if( t._type == TUNION ) return t.xmeet(this);

    boolean that_oop = t.is_oop();
    boolean that_num = t.is_num();
    assert !(that_oop&&that_num);
    
    if( is_oop() ) { // Only simple OOPish type
      if( !that_oop ) return t.isa(TypeInt.NULL) ? TypeUnion.make_null(this) : SCALAR;
      return _type == TOOP ? OOP : t;
    }

    if( is_num() ) {
      if( that_oop ) return isa(TypeInt.NULL) ? TypeUnion.make_null(t) : SCALAR;
      if( !that_num ) throw AA.unimpl();
      
      // Numeric; same pattern as ANY/ALL, or SCALAR/XSCALAR
      if( _type == TNUM || t._type == TNUM ) return NUM;
      if(   _type == TXNUM ) return t   ;
      if( t._type == TXNUM ) return this;
      
      // Real; same pattern as ANY/ALL, or SCALAR/XSCALAR
      if( _type == TREAL || t._type == TREAL ) return REAL;
      if(   _type == TXREAL ) return t   ;
      if( t._type == TXREAL ) return this;
      throw AA.unimpl();        // Need nice printout
    }
    throw AA.unimpl();          // Need nice printout
  }

  // By design in meet, args are already flipped to order _type, which forces
  // symmetry for things with badly ordered _type fields.  The question is
  // still interesting for other orders.
  private boolean check_commute( Type t, Type mt ) {
    if( t==this ) return true;
    if( is_simple() && !t.is_simple() ) return true; // By design, flipped the only allowed order
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
    System.err.print("("+this+"&"+t+")="+mt+"; but ("+mt._dual+"&");
    if( ta!=t._dual ) System.err.println(t._dual+")=="+ta+" which is not "+t._dual);
    else              System.err.println(  _dual+")=="+tb+" which is not "+  _dual);
    return false;
  }
  
  public Type join( Type t ) { return dual().meet(t.dual()).dual(); }

  public static void init0( HashMap<String,Type> types ) {
    TypeTuple.init1();
    types.put("real",REAL);
    TypeInt.init1(types);
    TypeFlt.init1(types);
    TypeStr.init1(types);
  }
  
  public static boolean check_startup() {
    Type[] ts =    Type      .TYPES ;
    ts = concat(ts,TypeErr   .TYPES);
    ts = concat(ts,TypeInt   .TYPES);
    ts = concat(ts,TypeFlt   .TYPES);
    ts = concat(ts,TypeStr   .TYPES);
    ts = concat(ts,TypeTuple .TYPES);
    ts = concat(ts,TypeStruct.TYPES);
    ts = concat(ts,TypeFun   .TYPES);
    ts = concat(ts,TypeRPC   .TYPES);
    ts = concat(ts,TypeUnion .TYPES);
    ts = concat(ts,TypeName  .TYPES);
    
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

    // Check scalar primitives; all are SCALARS and none sub-type each other.
    SCALAR_PRIMS = new Type[] { TypeInt.INT64, TypeFlt.FLT64, Type.OOP, TypeFun.make_generic() };
    for( Type t : SCALAR_PRIMS ) assert t.isa(SCALAR);
    for( int i=0; i<SCALAR_PRIMS.length; i++ ) 
      for( int j=i+1; j<SCALAR_PRIMS.length; j++ )
        assert !SCALAR_PRIMS[i].isa(SCALAR_PRIMS[j]);
    
    return true;
  }
  private static Type[] concat( Type[] ts0, Type[] ts1 ) {
    Type[] ts = Arrays.copyOf(ts0,ts0.length+ts1.length);
    System.arraycopy(ts1,0,ts,ts0.length,ts1.length);
    return ts;
  }
  
  // True if 'this' isa/subtypes 't'.  E.g. Int32-isa-Int64, but not vice-versa
  // E.g. ANY-isa-XSCALAR; XSCALAR-isa-XREAL; XREAL-isa-Int(Any); Int(Any)-isa-Int(3)
  public boolean isa( Type t ) { return meet(t)==t; }

  // True if value is above the centerline (no real value)
  public boolean above_center() {
    switch( _type ) {
    case TSCALAR:
    case TNUM:
    case TREAL:
      return false;             // These are all below center
    case TXREAL:
    case TXNUM:
    case TXSCALAR:
      return true;              // These are all above center
    case TERROR:
    case TFUN:
    case TRPC:
    case TUNION:
    case TTUPLE:
    case TSTRUCT:
    case TFLT:
    case TINT:
    default: throw AA.unimpl(); // Overridden in subclass
    case TSIMPLE: throw typerr(null);
    }
  }
  // True if value is higher-equal to SOME constant.
  public boolean canBeConst() {
    switch( _type ) {
    case TSCALAR:
    case TOOP:
    case TNUM:
    case TREAL:
    case TCTRL:
      return false;             // These all include not-constant things
    case TXREAL:
    case TXNUM:
    case TXOOP:
    case TXSCALAR:
    case TXCTRL:
      return true;              // These all include some constants
    default: throw AA.unimpl();
    }
  }
  public boolean is_con() {
    switch( _type ) {
    case TERROR:
    case TCTRL:
    case TSCALAR:
    case TNUM:
    case TREAL:
    case TXCTRL:
    case TXREAL:
    case TXNUM:
    case TXSCALAR:
    case TUNION:                // Overridden in subclass
      return false;             // Not exactly a constant
    default: throw AA.unimpl();
    }
  }
  // Return the argument type of idxth argument.  Error for everybody except
  // TypeFun and a TypeUnion of TypeFuns
  public Type arg(int idx) { throw AA.unimpl(); }
  // Return any "return type" of the Meet of all function types
  public Type ret() { return null; }
  // Return true if this is a function pointer (return type from EpilogNode)
  public boolean is_fun_ptr() { return false; }
  // Return true if this is a forward-ref function pointer (return type from EpilogNode)
  public boolean is_forward_ref() { return false; }
  // Return a long   from a TypeInt constant; assert otherwise.
  public long   getl() { throw AA.unimpl(); }
  // Return a double from a TypeFlt constant; assert otherwise.
  public double getd() { throw AA.unimpl(); }
  // Return a String from a TypeStr constant; assert otherwise.
  public String getstr() { throw AA.unimpl(); }

  // Lattice of conversions:
  // -1 unknown; top; might fail, might be free (Scalar->Int); Scalar might lift
  //    to e.g. Float and require a user-provided rounding conversion from F64->Int.
  //  0 requires no/free conversion (Int8->Int64, F32->F64)
  // +1 requires a bit-changing conversion (Int->Flt)
  // 99 Bottom; No free converts; e.g. Flt->Int requires explicit rounding
  public byte isBitShape(Type t) {
    if( above_center() && isa(t) ) return 0; // Can choose compatible format
    if( _type == t._type ) return 0; // Same type is OK
    if( t._type==TSCALAR ) return 0; // Generic function arg never requires a conversion
    if( _type == TSCALAR ) return -1; // Scalar has to resolve
    if( _type == TREAL && t.is_num() ) return -1; // Real->Int/Flt has to resolve
    if( is_fun_ptr() ) return (byte)(t == OOP ? 0 : 99);

    throw typerr(t);  // Overridden in subtypes
  }
  // "widen" a narrow type for primitive type-specialization.
  // e.g. "3" becomes "int64".
  public Type widen() { return this; } // Overridden in subclasses
  // Operator precedence
  public byte op_prec() { return -1; } // Overridden in subclasses
  // Contains an error type string, perhaps embedded in some subtype
  public String errMsg() { return null; }
  
  RuntimeException typerr(Type t) {
    throw new RuntimeException("Should not reach here: internal type system error with "+this+(t==null?"":(" and "+t)));
  }
}
