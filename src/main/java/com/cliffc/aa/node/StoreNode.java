package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

// Store a value into a named struct field.  Does it's own nil-check and value
// testing; also checks final field updates.
public class StoreNode extends Node {
  final String _fld;
  final int _fld_num;
  private final byte _fin;    // TypeStruct.ffinal or TypeStruct.frw
  private final boolean _xmem;// True if TypeMem only, False if TypeObj only
  private final Parse _bad;
  private StoreNode( Node ctrl, Node mem, Node adr, Node val, byte fin, String fld, int fld_num, Parse bad, boolean xmem ) {
    super(OP_STORE,ctrl,mem,adr,val);
    _fld = fld;
    _fld_num = fld_num;
    _fin = fin;
    _xmem = xmem;
    _bad = bad;    // Tests can pass a null, but nobody else does
  }
  public StoreNode( Node ctrl, Node mem, Node adr, Node val, byte fin, String fld , Parse bad ) { this(ctrl,mem,adr,val,fin,fld ,  -1   ,bad,true); }
  public StoreNode( Node ctrl, Node mem, Node adr, Node val, byte fin, int fld_num, Parse bad ) { this(ctrl,mem,adr,val,fin,null,fld_num,bad,true); }
  private StoreNode( StoreNode st, Node mem, Node adr ) { this(st.in(0),mem,adr,st.val(),st._fin,st._fld,st._fld_num,st._bad,false); }

  String xstr() { return "."+(_fld==null ? ""+_fld_num : _fld)+"="; } // Self short name
  String  str() { return xstr(); }      // Inline short name

  Node mem() { return in(1); }
  Node adr() { return in(2); }
  Node val() { return in(3); }

  @Override public Node ideal(GVNGCM gvn) {
    Node mem = mem();
    Node adr = adr();
    MemMergeNode mmem;
    if( mem instanceof MemMergeNode && (mmem=((MemMergeNode)mem)).obj().in(0) == adr.in(0) && mem._uses._len == 1 ) {
      assert adr.in(0) instanceof NewNode;
      Node st = gvn.xform(new StoreNode(this,mmem.obj(),adr));
      return new MemMergeNode(mmem.mem(),st);
    }
    return null;
  }

  @Override public Type value(GVNGCM gvn) {
    final Type  M = _xmem ? TypeMem. MEM : TypeObj. OBJ;
    final Type XM = _xmem ? TypeMem.XMEM : TypeObj.XOBJ;

    Type adr = gvn.type(adr()).base();
    if( adr.isa(TypeMemPtr.OOP0.dual()) ) return XM; // Very high address; might fall to any valid address
    if( adr.must_nil() ) return M;           // Not provable not-nil, so fails
    if( TypeMemPtr.OOP0.isa(adr) ) return M; // Very low, might be any address
    if( !(adr instanceof TypeMemPtr) )
      return adr.above_center() ? XM : M;

    Type val = gvn.type(val());     // Value
    if( !val.isa_scalar() )         // Nothing sane
      val = val.above_center() ? Type.XSCALAR : Type.SCALAR; // Pin to scalar for updates

    // Compute an updated memory state
    Type mem = gvn.type(mem());     // Memory
    if( mem().in(0) == adr().in(0) && mem().in(0) instanceof NewNode )
      // No aliasing, even if the NewNode is called repeatedly
      return ((TypeObj)mem).st(_fin, _fld, _fld_num, val);
    if( _xmem && !(mem instanceof TypeMem) ||
       !_xmem && !(mem instanceof TypeObj) )
      return mem.above_center() ? XM : M;
    return _xmem                // Object or Memory update
      ? ((TypeMem)mem).update(_fin, _fld, _fld_num, val, (TypeMemPtr)adr )
      : ((TypeObj)mem).update(_fin, _fld, _fld_num, val);
  }

  @Override public String err(GVNGCM gvn) {
    Type t = gvn.type(adr());
    while( t instanceof TypeName ) t = ((TypeName)t)._t;
    if( t.may_nil() ) return bad("Struct might be nil when writing");
    if( !(t instanceof TypeMemPtr) ) return bad("Unknown"); // Too low, might not have any fields
    TypeMemPtr tptr = (TypeMemPtr)t;
    Type mem = gvn.type(mem());
    TypeObj tobj = _xmem
      ? ((TypeMem)mem).ld(tptr) // Load object from generic pre-store memory
      : ((TypeObj)mem);         // Else handed object directly
    if( !tobj.can_update(_fld,_fld_num) || !tptr._obj.can_update(_fld,_fld_num) )
      return bad("Cannot re-assign read-only");
    return null;
  }
  private String bad( String msg ) {
    String f = _fld==null ? ""+_fld_num : _fld;
    return _bad.errMsg(msg+" field '."+f+"'");
  }
  @Override public Type all_type() { return _xmem ? TypeMem.MEM : TypeObj.OBJ; }
  @Override public int hashCode() { return super.hashCode()+(_fld==null ? _fld_num : _fld.hashCode()); }
  // Stores are never CSE/equal lest we force a partially-execution to become a
  // total execution (require a store on some path it didn't happen).  Stores
  // that are common in local SESE regions can be optimized with local peepholes.
  @Override public boolean equals(Object o) { return this==o; }
}
