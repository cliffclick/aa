package com.cliffc.aa.util;

// Simple sparse bitset, with a test-and-set.
public class BitSetSparse {
  NonBlockingHashMapLong<String> _set = new NonBlockingHashMapLong<>();
  public boolean tset(int b0, int b1) { return tset(((long)b0<<32)|b1); }
  public boolean tset(long b) { return _set.put(b,"")!=null; }
  public void clear() { _set.clear(); }
}
