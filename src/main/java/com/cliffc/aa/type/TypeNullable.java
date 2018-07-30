package com.cliffc.aa.type;

import com.cliffc.aa.AA;

// Base class for Types which can be nil
public abstract class TypeNullable extends Type {
  // There are 4 combos:
  static public final byte  IS_NIL=0; //      nil;
  static public final byte NOT_NIL=1; //  OOP    ; all the OOPs, never nil
  static public final byte  OR_NIL=2; //  OOP+nil; or choice of nil
  static public final byte AND_NIL=3; //  OOP&nil; and also nil
  protected static final String[] TSTRS=new String[]{"0","%s","%s+0","%s&0"};
  // map 0->0, 1->1, 2->3; 3->2;
  byte xdualnil() { return (byte)(_nil<=1 ? _nil : 5-_nil); }

  byte _nil;
  protected TypeNullable(byte type, byte nil ) { super(type); init(nil); }
  protected void init(byte nil) { _nil=nil; }
  @Override public int hashCode( ) { return (_type<<8)+_nil; }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    return o instanceof TypeOop && eq((TypeOop)o);
  }
  public boolean eq( TypeNullable to ) { return _type==to._type && _nil==to._nil; }

  // Meet "nullable" notions
  byte nmeet(TypeNullable n) {
    if(   _nil==OR_NIL ) return n._nil; // OR loses to the other side
    if( n._nil==OR_NIL ) return   _nil; // OR loses to the other side
    if(   _nil==n._nil ) return   _nil; // Equals returns either
    return AND_NIL;                     // Everything else has a nil
  }
  
  // True if this OOP may BE a nil (as opposed to: may have a nil)
  public boolean may_be_nil() { return _nil==IS_NIL || _nil==OR_NIL; }
}
