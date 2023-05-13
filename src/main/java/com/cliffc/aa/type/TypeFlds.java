package com.cliffc.aa.type;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.Util;

// An AryI generified to TypeFld
public class TypeFlds extends AryI<TypeFld> {
  private static final TypeFlds TYPEFLDS = new TypeFlds(-1);
  @Override Ary<AryI<TypeFld>> clinit() { return new Ary<>(new TypeFlds[1],0); }
  @Override TypeFlds make_holder(int len) { return new TypeFlds(len); }
  @Override TypeFld[] make_ary(int len) { return new TypeFld[len]; }
  @Override TypeFld[][] make_arys(int len) { return new TypeFld[len][]; }
  @Override int _compute_hash(TypeFld[] ts) {
    for( TypeFld t : ts ) Util.add_hash( t._hash );
    return (int)Util.get_hash();
  }
  TypeFlds(int len) { super(len); }
  // Static forwards
  public static TypeFld[] get(int len) { return TYPEFLDS._get(len); }
  public static boolean   interned (TypeFld[] ts) { return TYPEFLDS._interned (ts); }
  public static void free(TypeFld[] ts) { TYPEFLDS._free(ts); }
  public static TypeFld[] make(TypeFld t0) { return hash_cons(TYPEFLDS._ts(t0)); }
  public static TypeFld[] make(TypeFld t0, TypeFld t1) { return hash_cons(TYPEFLDS._ts(t0,t1)); }
  public static TypeFld[] make(TypeFld t0, TypeFld t1, TypeFld t2) { return hash_cons(TYPEFLDS._ts(t0,t1,t2)); }
  public static TypeFld[] ts(TypeFld t0, TypeFld t1) { return TYPEFLDS._ts(t0,t1); }
  public static TypeFld[] clone(TypeFld[] ts) { return TYPEFLDS._clone(ts); }
  public static TypeFld[] copyOf(TypeFld[] ts, int len) { return TYPEFLDS._copyOf(ts,len); }

  public static TypeFld[] hash_cons(TypeFld[] ts) {
    // Delayed hash-consing during RECURSIVE_MEET install
    if( Type.RECURSIVE_MEET > 0 ) {
      if( !check(ts) ) return ts; // Cannot intern yet
    } else assert check(ts);
    return TYPEFLDS._hash_cons(ts);
  }
  private static boolean check(TypeFld[]ts) {
    for( TypeFld fld : ts )
      if( fld.un_interned() )
        return false;
    return true;
  }  
  
  public static final TypeFld[] EMPTY = hash_cons(get(0));

  // Are the fields in order?
  public static boolean sbefore(String s0, String s1) {
    if( Util.eq(s0,"^") ) return true;
    if( Util.eq(s1,"^") ) return false;
    return s0.compareTo(s1) < 0;
  }

  // Change a field.  Preserves the original.  Does not hash-cons
  public static TypeFld[] make_from(TypeFld[] flds, int idx, TypeFld fld) {
    TypeFld[] tfs = clone(flds);
    tfs[idx] = fld;
    return tfs;
  }

  // Append a field.  Preserve alpha order.  Does not hash-cons.
  // Does not free the original (in case it was interned).
  public static TypeFld[] add_sort(TypeFld[] flds, TypeFld fld) {
    TypeFld[] fs = copyOf(flds,flds.length+1);
    fs[flds.length]=fld;
    int i=0;
    while( i<flds.length && sbefore(flds[i]._fld,fld._fld) ) i++;
    fs[i]=fld;
    System.arraycopy(flds,i,fs,i+1,flds.length-i);
    return fs;
  }

  // Pop the last field.  Defensive copy, hash_consed
  public static TypeFld[] pop( TypeFld[] flds ) {
    return hash_cons(copyOf(flds,flds.length-1));
  }
  // Remove the ith field; defensive copy, hash_consed
  public static TypeFld[] remove( TypeFld[] flds, int idx ) {
    TypeFld[] fs = get(flds.length-1);
    if( idx >= 0 ) System.arraycopy(flds, 0, fs, 0, idx);
    for( int i=idx+1; i<flds.length; i++ ) fs[i-1] = flds[i];
    return hash_cons(fs);
  }

}
