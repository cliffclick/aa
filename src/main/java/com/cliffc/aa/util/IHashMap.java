package com.cliffc.aa.util;

import java.util.Set;

@SuppressWarnings("unchecked")
public class IHashMap {
  private final NonBlockingHashMap _map = new NonBlockingHashMap();
  public <T> T put(T kv) { _map.put(kv,kv); return kv; }
  public <T> T put(T k, T v) { _map.put(k,v); return v; }
  public <T> T get(T key) { return (T)_map.get(key); }
  public void remove(Object key) { _map.remove(key); }
  public void clear() { _map.clear(true); }
  public boolean isEmpty() { return _map.isEmpty(); }
  public <T> Set<T> keySet() { return _map.keySet(); }
}
