package com.cliffc.aa.type;

import com.cliffc.aa.util.*;
import java.util.Arrays;

// An AryI generified to Type
public class Types extends AryI<Type> {
  private static final Types TYPES = new Types(-1);
  @Override Ary<AryI<Type>> clinit() { return new Ary<>(new Types[1],0); }
  @Override Types make_holder(int len) { return new Types(len); }
  @Override Type[] make_ary(int len) { return new Type[len]; }
  @Override Type[][] make_arys(int len) { return new Type[len][]; }
  @Override int _compute_hash(Type[] ts) {
    for( Type t : ts ) Util.add_hash( t._hash );
    return (int)Util.get_hash();
  }
  Types(int len) { super(len); }
  // Static forwards
  public static Type[] get(int len) { return TYPES._get(len); }
  public static Type[] hash_cons(Type[]ts) { return TYPES._hash_cons(ts); }
  public static Type[] ts(Type t0) { return TYPES._ts(t0); }
  public static Type[] ts(Type t0, Type t1) { return TYPES._ts(t0,t1); }
  public static Type[] ts(Type t0, Type t1, Type t2) { return TYPES._ts(t0,t1,t2); }
  public static Type[] ts(Type t0, Type t1, Type t2, Type t3) { return TYPES._ts(t0,t1,t2,t3); }
  public static Type[] ts(Type t0, Type t1, Type t2, Type t3, Type t4) { return TYPES._ts(t0,t1,t2,t3,t4); }
  public static Type[] ts(Type t0, Type t1, Type t2, Type t3, Type t4, Type t5) { return TYPES._ts(t0,t1,t2,t3,t4,t5); }
  public static Type[] clone(Type[] ts) { return TYPES._clone(ts); }
  public static Type[] copyOf(Type[] ts, int len) { return TYPES._copyOf(ts,len); }
  public static void free(Type[] ts) { TYPES._free(ts); }
}
