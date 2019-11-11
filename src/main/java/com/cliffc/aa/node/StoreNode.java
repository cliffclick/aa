package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.*;

// Store a value into a named struct field.  Does it's own nil-check and value
// testing; also checks final field updates.
public class StoreNode extends Node {
  final String _fld;
  final int _fld_num;
  private final byte _fin;    // TypeStruct.ffinal or TypeStruct.frw
  private final boolean _xmem;// True if TypeMem only, False if TypeObj only
  private final boolean _cast;// True if upcast post-If; never changes memory value, never emits code, just acts as a memory-upcast
  private final Parse _bad;
  private StoreNode( Node ctrl, Node mem, Node adr, Node val, byte fin, String fld, int fld_num, Parse bad, boolean xmem, boolean cast ) {
    super(OP_STORE,ctrl,mem,adr,val);
    assert xmem ? Env.GVN.type(mem) instanceof TypeMem : Env.GVN.type(mem) instanceof TypeObj;
    _fld = fld;
    _fld_num = fld_num;
    _fin = fin;
    _xmem = xmem;
    _cast = cast;
    _bad = bad;    // Tests can pass a null, but nobody else does
  }
  public StoreNode( Node ctrl, Node mem, Node adr, Node val, byte fin, String fld , Parse bad ) { this(ctrl,mem,adr,val,fin,fld ,  -1   ,bad,true,false); }
  public StoreNode( Node ctrl, Node mem, Node adr, Node val, byte fin, int fld_num, Parse bad ) { this(ctrl,mem,adr,val,fin,null,fld_num,bad,true,false); }
  private StoreNode( StoreNode st, Node mem, Node adr, boolean xmem ) { this(st.in(0),mem,adr,st.val(),st._fin,st._fld,st._fld_num,st._bad,xmem,false); }
  public  StoreNode( StoreNode st, Node ctr, Node mem, Node adr, Node val, boolean cast ) { this(ctr,mem,adr,val,st._fin,st._fld,st._fld_num,st._bad,st._xmem,cast); }

  String xstr() { return "."+(_fld==null ? ""+_fld_num : _fld)+"="; } // Self short name
  String  str() { return xstr(); }      // Inline short name

  Node ctl() { return in(0); }
  Node mem() { return in(1); }
  Node adr() { return in(2); }
  Node val() { return in(3); }

  @Override public Node ideal(GVNGCM gvn) {
    Node ctl = ctl();
    Node mem = mem();
    Node adr = adr();
    // Top-level control can be ignored, as it gates nothing
    if( ctl == Env.CTL_0 ) return set_def(0,null,gvn);

    MemMergeNode mmem;
    // If the Store by a Merge with unrelated aliasing, bypass.
    if( mem instanceof MemMergeNode ) {
      mmem=(MemMergeNode)mem;
      Type ta = gvn.type(adr);
      if( ta instanceof TypeMemPtr ) {
        Node zmem = mmem.split_memory_use(gvn,((TypeMemPtr)ta)._aliases);
        if( zmem != null ) {
          boolean xmem = zmem==mmem.in(0); // true is phat memory, false is skinny
          Node st = gvn.xform(new StoreNode(this,zmem,adr,xmem));
          return xmem
            ? new MemMergeNode(st,mmem.in(1))
            : new MemMergeNode(mmem.in(0),st);
        }
      }
    }

    // If Store is by a New, fold into the New.
    NewNode nnn;
    if( mem instanceof OProjNode && mem.in(0) instanceof NewNode && (nnn=(NewNode)mem.in(0)) == adr.in(0) &&
        ctl() == nnn.in(0) && nnn._ts.can_update(_fld,_fld_num) && !val().is_forward_ref() ) {
      nnn.update(_fld,_fld_num,val(),gvn,_fin);
      // As part of the local xform rule, the memory & ptr outputs of the
      // NewNode need to update their types directly.  This Store pts at
      // the OProj, and when it folds it can set the NewNode mutable bit
      // to e.g. final.  The OProj type needs to also reflect final.  This
      // is because we have an Ideal rule allowing a Load to bypass a
      // Store that is not in-error, but back-to-back final stores can
      // temporarily be not-in-error if the OProj does not reflect final.
      gvn.setype(nnn,nnn.value(gvn));
      for( Node use : nnn._uses ) gvn.setype(use,use.value(gvn));
      return mem;
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
    if( err(gvn) != null ) return M; // Store is in-error (probably store-after-final-store)

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
    if( _cast ) return null;    // Ignore re-assign check, since upcast never alters memory
    if( !tobj.can_update(_fld,_fld_num) || !tptr._obj.can_update(_fld,_fld_num) )
      return adr() instanceof ProjNode && adr().in(0) instanceof NewNode && ((NewNode)adr().in(0))._is_closure
        ? bad("Cannot re-assign final val '")
        : bad("Cannot re-assign read-only field '.");
    return null;
  }
  private String bad( String msg ) {
    String f = _fld==null ? ""+_fld_num : _fld;
    return _bad.errMsg(msg+f+"'");
  }
  @Override public Type all_type() { return _xmem ? TypeMem.MEM : TypeObj.OBJ; }
  @Override public int hashCode() { return super.hashCode()+(_fld==null ? _fld_num : _fld.hashCode()); }
  // Stores are never CSE/equal lest we force a partial execution to become a
  // total execution (require a store on some path it didn't happen).  Stores
  // that are common in local SESE regions can be optimized with local peepholes.
  @Override public boolean equals(Object o) { return this==o; }
  // Split this node into a set returning 'bits' and the original which now
  // excludes 'bits'.  Return null if already making a subset of 'bits'.
  Node split_memory_use( GVNGCM gvn, BitsAlias bits ) {
    TypeMemPtr tmp = (TypeMemPtr)gvn.type(adr());
    if( tmp._aliases == bits ) return null; // No progress, got the right memory alias

    // Special case of no overlap: both bits have only 1 bit, and neither is
    // the parent of the other.  If either is the parent, the meet will be the
    // parent.
    int b0 = bits.abit();
    int b1 = tmp._aliases.abit();
    if( b0 != -1 && b1 != -1 ) {
      BitsAlias bx = bits.meet(tmp._aliases);
      if( bx.test(b0) && bx.test(b1) )
        // Just a bypass; 'this' continues to produce the full memory mem(),
        // although at least one user of alias 'bits' goes away.  No
        // implication that all users of 'bits' go away.
        return mem(); 
    }

    // TODO: A much stronger version is to check that 'tmp._aliases' and 'bits'
    // are disjoint.  A way to do this is to lift all bits in both sets to the
    // same tree depth, then verify that the bitsets are disjoint.
    return null;                // No progress
  }
}
