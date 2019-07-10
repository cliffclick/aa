package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

// Store a value into a named struct field.  Does it's own nil-check and value
// testing; also checks final field updates.
public class StoreNode extends Node {
  private final String _fld;
  private final int _fld_num;
  private final String _badfld;
  private final String _badnil;
  private final String _badfin;
  private StoreNode( Node ctrl, Node mem, Node adr, Node val, String fld, int fld_num, Parse bad ) {
    super(OP_STORE,ctrl,mem,adr,val);
    _fld = fld;
    _fld_num = fld_num;
    // Tests can pass a null, but nobody else does
    _badfld = bad==null ? null : bad.errMsg("Unknown field '."+fld+"'");
    _badnil = bad==null ? null : bad.errMsg("Struct might be nil when writing field '."+fld+"'");
    _badfin = bad==null ? null : bad.errMsg("Cannot re-assign final field '."+fld+"'");
  }
  public StoreNode( Node ctrl, Node mem, Node adr, Node val, String fld , Parse bad ) { this(ctrl,mem,adr,val,fld,-1,bad); }
  public StoreNode( Node ctrl, Node mem, Node adr, Node val, int fld_num, Parse bad ) { this(ctrl,mem,adr,val,null,fld_num,bad); }
  String xstr() { return "."+(_fld==null ? ""+_fld_num : _fld)+"="; } // Self short name
  String  str() { return xstr(); }      // Inline short name

  Node ctl() { return in(0); }
  Node mem() { return in(1); }
  Node adr() { return in(2); }
  Node val() { return in(3); }
  
  @Override public Node ideal(GVNGCM gvn) {
    return null;
  }

  @Override public Type value(GVNGCM gvn) {
    final Type  M = TypeMem.MEM;
    final Type XM = TypeMem.XMEM;
    Type adr = gvn.type(adr()).base();
    if( adr.isa(TypeMemPtr.OOP0.dual()) ) return XM; // Very high address; might fall to any valid address
    if( adr.must_nil() ) return M;           // Not provable not-nil, so fails
    if( TypeMemPtr.OOP0.isa(adr) ) return M; // Very low, might be any address
    if( !(adr instanceof TypeMemPtr) )
      return adr.above_center() ? XM : M;

    Type mem = gvn.type(mem());     // Memory
    if( !(mem instanceof TypeMem) ) // Nothing sane
      return mem.above_center() ? XM : M;

    Type val = gvn.type(val());     // Value
    if( !val.isa_scalar() )         // Nothing sane
      val = val.above_center() ? Type.XSCALAR : Type.SCALAR; // Pin to scalar for updates
    // Compute an updated memory state
    TypeMem mem2 = ((TypeMem)mem).st((TypeMemPtr)adr, _fld, _fld_num, val);
    
    return mem2;
  }

  @Override public String err(GVNGCM gvn) {
    Type t = gvn.type(adr());
    while( t instanceof TypeName ) t = ((TypeName)t)._t;
    if( t.may_nil() ) return _badnil;
    if( !(t instanceof TypeMemPtr) ) return _badfld; // Too low, might not have any fields
    if( !(((TypeMemPtr)t)._obj instanceof TypeStruct) ) return _badfld;
    TypeStruct ts = (TypeStruct)((TypeMemPtr)t)._obj;
    int fnum = ts.find(_fld,_fld_num);
    if( fnum == -1 )
      return _badfld;
    if( ts._finals[fnum] == 1 ) return _badfin; // Trying to over-write a final
    return null;
  }
  @Override public Type all_type() { return TypeMem.MEM; }
  @Override public int hashCode() { return super.hashCode()+(_fld==null ? _fld_num : _fld.hashCode()); }
  // Stores are never CSE/equal lest we force a partially-execution to become a
  // total execution (require a store on some path it didn't happen).  Stores
  // that are common in local SESE regions can be optimized with local peepholes.
  @Override public boolean equals(Object o) { return this==o; }
}
