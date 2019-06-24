package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

import java.util.Arrays;

// Make a new object of given type.  Returns both the pointer and the memory
// state, so the output is similar to standard Call.
public class NewNode extends Node {
  private final String[] _names; // Field names
  private final byte[] _finals;  // Final field booleans
  // Unique alias class, one class per unique memory allocation site.
  // Only effectively-final, because the copy/clone sets a new alias value.
  private int _alias;            // Alias class
  private boolean _dead;         // No users of the address
  public NewNode( Node[] flds, String[] names ) { this(flds,names,finals(names.length)); }
  public NewNode( Node[] flds, String[] names, byte[] finals ) {
    super(OP_NEW,flds);
    assert flds[0]==null;       // no ctrl field
    assert def_idx(names .length)==flds.length;
    assert def_idx(finals.length)==flds.length;
    _names = names;
    _finals= finals;
    _alias = BitsAlias.new_alias(BitsAlias.REC,type());
  }
  private static byte[] finals(int len) { byte[] bs = new byte[len]; Arrays.fill(bs,(byte)1); return bs; }
  private int def_idx(int fld) { return fld+1; }
  private Node fld(int fld) { return in(def_idx(fld)); }
  boolean is_dead_address() { return _dead; }  
  String xstr() { return is_dead_address() ? "New#dead" : ("New#"+_alias); } // Self short name
  String  str() { return xstr(); } // Inline short name
  @Override public Node ideal(GVNGCM gvn) {
    // If the address is dead, then the object is unused and can be nuked.
    // Check for 1 user, and its the memory proj not the ptr proj.
    if( _uses.len()==1 && ((ProjNode)_uses.at(0))._idx==0 ) {
      _dead = true;
      for( int i=0; i<_names.length; i++ )
        set_def(def_idx(i),null,gvn); // Kill contents of memory
    }
    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    // If the address is dead, then the object is unused and can be nuked
    if( is_dead_address() )
      return TypeTuple.make(TypeMem.XMEM,TypeMemPtr.make(_alias));
    Type[] ts = new Type[_names.length];
    for( int i=0; i<_names.length; i++ ) {
      Type t = gvn.type(fld(i));
      // Limit to Scalar results
      if(  t.isa(Type.XSCALAR) ) t = Type.XSCALAR;
      if( !t.isa(Type. SCALAR) ) t = Type. SCALAR;
      ts[i] = t;
    }
    TypeStruct newt = TypeStruct.make(_names,ts,_finals);
    // Get the existing type, without installing if missing because blows the
    // "new newnode" assert if this node gets replaced during parsing.
    Type oldnnn = gvn.self_type(this);
    Type oldt= oldnnn instanceof TypeTuple ? ((TypeTuple)oldnnn).at(0) : newt;
    TypeStruct apxt= approx(newt,oldt); // Approximate infinite types
    Type ptr = TypeMemPtr.make(_alias);
    Type mem1 = TypeMem.make(_alias,apxt);
    return TypeTuple.make(mem1,ptr);
  }
  
  // NewNodes can participate in cycles, where the same structure is appended
  // to in a loop until the size grows without bound.  If we detect this we
  // need to approximate a new cyclic type.
  private final static int CUTOFF=5; // Depth of types before we start forcing approximations
  public static TypeStruct approx(TypeStruct newt, Type oldt) {
    if( !(oldt instanceof TypeStruct) ) return newt;
    if( newt == oldt ) return newt;
    if( !newt.contains(oldt) ) return newt;
    if( oldt.depth() <= CUTOFF ) return newt;
    TypeStruct tsa = newt.approx((TypeStruct)oldt);
    return (TypeStruct)(tsa.meet(oldt));
  }

  // Worse-case type for this Node
  TypeStruct type() {
    Type[] ts = new Type[_names.length];
    Arrays.fill(ts,Type.SCALAR);
    return TypeStruct.make(_names,ts,_finals);
  };
  @Override public Type all_type() {
    return is_dead_address()
      ? TypeTuple.make(TypeMem.XMEM, TypeMemPtr.make(_alias))
      : TypeTuple.make(TypeMem.make(_alias,type()), TypeMemPtr.make(_alias));
  }
  
  // Clones during inlining all become unique new sites
  @Override NewNode copy(GVNGCM gvn) {
    NewNode nnn = (NewNode)super.copy(gvn);
    nnn._alias = BitsAlias.new_alias(_alias,type()); // Children alias classes, split from parent
    return nnn;
  }

  @Override public int hashCode() { return super.hashCode()+ Arrays.hashCode(_names); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof NewNode) ) return false;
    NewNode nnn = (NewNode)o;
    return Arrays.equals(_names,nnn._names);
  }
}
