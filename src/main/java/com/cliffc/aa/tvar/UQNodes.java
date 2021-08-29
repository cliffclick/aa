package com.cliffc.aa.tvar;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.util.*;
import java.util.HashMap;

// Unique immutable lazy-defined sets of Nodes.
public class UQNodes extends NonBlockingHashMapLong<Node> {
  private static final NonBlockingHashMap<UQNodes,UQNodes> UQSETS = new NonBlockingHashMap<>();
  private static UQNodes KEY = new UQNodes();
  private int _hash;


  private static UQNodes intern() {
    KEY.setHash();
    UQNodes uqset = UQSETS.get(KEY);
    if( uqset==null ) {
      UQSETS.put(uqset=KEY,KEY);
      KEY=new UQNodes();
    } else {
      KEY.clear();
      KEY._hash=0;
    }
    return uqset;
  }

  // Make a unique set of 1 node
  public static UQNodes make( Node tn ) {
    assert !tn.is_dead();
    assert KEY.isEmpty();
    KEY.put(tn._uid,tn);
    return intern();
  }

  // Add a node to a unique-set: copy, insert key, re-hash/intern.
  public UQNodes add( Node tn ) {
    assert KEY.isEmpty();
    if( tn==null ) return this;
    assert !tn.is_dead();
    if( get(tn._uid)!=null ) return this; // Already in there
    // Fold them together
    for( Node n : values() ) if( !n.is_dead() ) KEY.put(n._uid,n);
    KEY.put(tn._uid,tn);
    return intern();
  }

  // Combine two unique-sets & return the result.  Lazy remove dead nodes.
  public UQNodes addAll( UQNodes uq ) {
    assert KEY.isEmpty();
    if( uq==null ) return this;

    // Get smaller in uq0
    UQNodes uq0 = this;
    UQNodes uq1 = uq;
    if( uq1.size() < uq0.size() ) { uq0=uq; uq1=this; }
    // See if all of smaller is in larger
    boolean progress=false;
    for( Node n : uq0.values() )
      if( !n.is_dead() && uq1.get(n._uid)!=n )
        { progress = true; break; }
    if( !progress ) return uq1;

    // Fold them together
    for( Node n : uq0.values() ) if( !n.is_dead() ) KEY.put(n._uid,n);
    for( Node n : uq1.values() ) if( !n.is_dead() ) KEY.put(n._uid,n);

    return intern();
  }

  // Replace via the map
  public UQNodes rename(HashMap<Node,Node> map) {
    assert KEY.isEmpty();
    for( Node n : values() )
      if( !n.is_dead() ) {
        Node c = map.get(n);
        if( c==null ) c = n;
        KEY.put(c._uid,c);
      }
    return intern();
  }

  private void setHash() {
    long hash=0;
    for( Node n : values() )
      hash = hash^System.identityHashCode(n);
    if( hash==0 ) hash=1;
    _hash = (int)hash;
  }
  @Override public int hashCode() { assert _hash!=0; return _hash; }
  @Override public boolean equals( Object o ) {
    if( !(o instanceof UQNodes) ) return false;
    UQNodes uq = (UQNodes)o;
    assert _hash!=0 && uq._hash!=0;
    if( _hash!=uq._hash ) return false;
    if( size() != uq.size() ) return false;
    for( Node n : values() )
      if( n!=uq.get(n._uid) )
        return false;
    return true;
  }

}

