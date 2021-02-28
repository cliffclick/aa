package com.cliffc.aa.util;

import java.util.BitSet;

public class VBitSet extends BitSet {
  // Cannot override 'set' to return a value... :-P
  public boolean tset(int idx) { boolean b = get(idx); set(idx); return b; }
  public boolean test(int idx) { return get(idx); }
  public VBitSet clr() { clear(); return this; }
}
