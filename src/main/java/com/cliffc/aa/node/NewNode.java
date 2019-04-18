package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

import java.util.Arrays;

// Make a new object of given type.  Returns both the pointer and the memory
// state, so the output is similar to standard Call.
public class NewNode extends Node {
  // Unique dense alias number, one number per unique memory allocation site.
  // Note that the _uid could serve the same purpose, except its not very dense
  // (ratio of NewNodes to all nodes).  
  private final String[] _names; // Field names
  private final byte[] _finals;  // Final fields
  int _alias;                    // Alias number, or -1 if dead
  public NewNode( Node[] flds, String[] names ) { this(flds,names,bs(names.length)); }
  public NewNode( Node[] flds, String[] names, byte[] finals ) {
    super(OP_NEW,flds);
    assert flds[0]==null;       // no ctrl field
    assert names .length==flds.length-1;
    assert finals.length==flds.length-1;
    _names = names;
    _finals= finals;
    _alias = TypeMem.new_alias();
  }
  private static byte[] bs(int len) { byte[] bs = new byte[len]; Arrays.fill(bs,(byte)1); return bs; }
  String xstr() { return "New#"+_alias; } // Self short name
  String  str() { return _alias==-1 ? "New#dead" : xstr(); } // Inline short name
  @Override public Node ideal(GVNGCM gvn) {
    // If the address is dead, then the object is unused and can be nuked
    if( _uses.len()==1 && ((ProjNode)_uses.at(0))._idx==0 ) {
      for( int i=0; i<_defs.len(); i++ )
        set_def(i,null,gvn);
      _alias = -1;              // Flag as dead
    }
    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    // If the address is dead, then the object is unused and can be nuked
    if( _alias == -1 )
      return TypeTuple.make(TypeMem.XMEM,TypeMemPtr.OOP0.dual());
    Type[] ts = new Type[_defs._len-1];
    for( int i=0; i<ts.length; i++ ) {
      Type t = gvn.type(in(i+1));
      // Limit to Scalar results
      if(  t.isa(Type.XSCALAR) ) t = Type.XSCALAR;
      if( !t.isa(Type. SCALAR) ) t = Type. SCALAR;
      ts[i] = t;
    }
    TypeStruct newt = TypeStruct.make(_names,ts,_finals);
    // Get the existing type, without installing if missing because blows the
    // "new newnode" assert if this node gets replaced during parsing.
    Type oldnnn = gvn.self_type(this);
    Type oldt= oldnnn instanceof TypeTuple ? ((TypeTuple)oldnnn).at(1) : newt;
    TypeStruct apxt= approx(newt,oldt); // Approximate infinite types
    Type ptr = TypeMemPtr.make(_alias);
    Type mem = TypeMem.make(_alias,apxt);
    return TypeTuple.make(mem,ptr);
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
  @Override public Type all_type() {
    if( _alias == -1 )
      return TypeTuple.make(TypeMem.XMEM,TypeMemPtr.OOP0.dual());
    return TypeTuple.make(TypeMem.MEM,TypeMemPtr.make(_alias));
  }
  
  // Clones during inlining all become unique new sites
  @Override NewNode copy(GVNGCM gvn) {
    NewNode nnn = super.copy(gvn);
    nnn._alias = BitsAlias.split(_alias);
    //return nnn;
    throw com.cliffc.aa.AA.unimpl();
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
