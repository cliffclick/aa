package com.cliffc.aa.type;

// Base class for Types which can be nil
public abstract class TypeNullable extends Type {
  // There are 4 combos:
  public static final byte  IS_NIL=0; //      nil;
  public static final byte NOT_NIL=1; //  OOP    ; all the OOPs, never nil
  public static final byte  OR_NIL=2; //  OOP+nil; or choice of nil
  public static final byte AND_NIL=3; //  OOP&nil; and also nil
  static final String[] TSTRS=new String[]{"0","%s","%s+0","%s?"};
  // map 0->0, 1->1, 2->3; 3->2;
  byte xdualnil() { return (byte)(_nil<=1 ? _nil : 5-_nil); }
  public byte _nil;
  
  TypeNullable( byte type, byte nil ) { super(type); init(nil); }
  protected void init(byte nil) { _nil=nil; }
  @Override public int hashCode( ) { return (_type<<8)+_nil; }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    return o instanceof TypeNullable && eq((TypeNullable)o);
  }
  boolean eq( TypeNullable to ) { return _type==to._type && _nil==to._nil; }

  // Meet in a nil
  @Override public Type meet_nil() { return make_nil(nmeet(IS_NIL)); }
  
  // Make a subtype with a given nil choice
  abstract public Type make_nil(byte nil);

  // Meet "nullable" notions
  byte nmeet(byte nil) {
    if( _nil==OR_NIL ) return  nil; // OR loses to the other side
    if(  nil==OR_NIL ) return _nil; // OR loses to the other side
    if( _nil==   nil ) return _nil; // Equals returns either
    return AND_NIL;                 // Everything else has a nil
  }

  // True if value is higher-equal to SOME constant.
  @Override public boolean may_be_con() { return may_be_nil(); }
  // True if this OOP is a nil (the only constant)
  @Override public boolean is_con() { return _nil==IS_NIL; }
  // True if this OOP may BE a nil (as opposed to: may have a nil)
  @Override public boolean may_be_nil() { return _nil==IS_NIL || _nil==OR_NIL; }
  // Return true if this type may HAVE a null: includes any nullable type with
  // "AND_NIL" or "IS_NIL", or int types at or below the constant 0.
  @Override public boolean may_have_nil() { return _nil==IS_NIL || _nil==AND_NIL; }
}
