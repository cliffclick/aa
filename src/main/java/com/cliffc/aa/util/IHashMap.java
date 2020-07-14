package com.cliffc.aa.util;

import java.util.HashMap;
import java.util.Set;

@SuppressWarnings("unchecked")
public class IHashMap {
  private final HashMap _map = new HashMap();
  public <T> T put(T kv) { _map.put(kv,kv); return kv; }
  public <T> T put(T k, T v) { _map.put(k,v); return v; }
  public <T> T get(T key) { return (T)_map.get(key); }
  public void remove(Object key) { _map.remove(key); }
  public void clear() { _map.clear(); }
  public boolean isEmpty() { return _map.isEmpty(); }
  public <T> Set<T> keySet() { return _map.keySet(); }
}
