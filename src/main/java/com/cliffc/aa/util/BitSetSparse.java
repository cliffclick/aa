package com.cliffc.aa.util;

// Simple sparse bitset, with a test-and-set.
public class BitSetSparse {
  NonBlockingHashMapLong<String> _set = new NonBlockingHashMapLong<>();
  public boolean tset(int b0, int b1) { return tset(((long)b0<<32)|b1); }
  public boolean clr (int b0, int b1) { return clr (((long)b0<<32)|b1); }
  public boolean tset(long b) { return _set.put(b,"")!=null; }
  public boolean clr (long b) { return _set.remove(b)!=null; }
  public boolean test(long b) { return _set.get(b)!=null; }
  public void clear() { _set.clear(true); }
  public int cardinality() { return _set.size(); }
  @Override public String toString() {
    if( _set.size()==0 ) return "[]";
    SB sb = new SB().p('[');
    for( long i : _set.keySetLong() )
      if( i >= (1L<<32) ) sb.p('(').p(i>>32).p(',').p(i&0xFFFFFFFFL).p(')').p(',');
      else sb.p(i).p(',');
    return sb.unchar().p(']').toString();
  }
}
