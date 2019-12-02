package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.*;

// Store a value into a named struct field.  Does it's own nil-check and value
// testing; also checks final field updates.
public class StoreNode extends Node {
  final String _fld;        // Field being updated
  private final byte _fin;  // TypeStruct.ffinal or TypeStruct.frw
  private final Parse _bad;
  public StoreNode( Node ctrl, Node mem, Node adr, Node val, byte fin, String fld, Parse bad ) {
    super(OP_STORE,ctrl,mem,adr,val);
    _fld = fld;
    _fin = fin;
    _bad = bad;    // Tests can pass a null, but nobody else does
  }
  private StoreNode( StoreNode st, Node mem, Node adr ) { this(st.in(0),mem,adr,st.val(),st._fin,st._fld,st._bad); }
  //public  StoreNode( StoreNode st, Node ctr, Node mem, Node adr, Node val ) { this(ctr,mem,adr,   val  ,st._fin,st._eqv,st._bad); }

  String xstr() { return _fld+"="; } // Self short name
  String  str() { return xstr(); }   // Inline short name

  Node ctl() { return in(0); }
  Node mem() { return in(1); }
  Node adr() { return in(2); }
  Node val() { return in(3); }

  @Override public Node ideal(GVNGCM gvn) {
    Node ctl = ctl();
    Node mem = mem();
    Node adr = adr();

    // Stores bypass a Merge to the specific alias
    Type ta = gvn.type(adr);
    if( ta instanceof TypeMemPtr && mem instanceof MemMergeNode )
      return new StoreNode(this,((MemMergeNode)mem).obj((TypeMemPtr)ta,gvn),adr);

    // Stores bypass a ObjMerge to the specific alias
    if( ta instanceof TypeMemPtr && mem instanceof ObjMergeNode ) {
      gvn.unreg(mem);        // Stretch the incoming ObjMerge for the new field
      int idx = ((ObjMergeNode)mem).fld_idx(_fld,gvn);
      // Store on the other side of ObjMerge
      Node st = gvn.xform(new StoreNode(this,mem.in(idx),adr));
      // Update and return ObjMerge
      mem.set_def(idx,st,gvn);
      gvn.rereg(mem,mem.value(gvn));
      return mem;
    }
    
    // If Store is by a New, fold into the New.
    NewNode nnn;  int idx;
    if( mem instanceof OProjNode && mem.in(0) instanceof NewNode && (nnn=(NewNode)mem.in(0)) == adr.in(0) &&
        ctl == nnn.in(0) && !val().is_forward_ref() && (idx=nnn._ts.find(_fld))!= -1 && nnn._ts.can_update(idx) ) {
      // As part of the local xform rule, the memory & ptr outputs of the
      // NewNode need to update their types directly.  This Store pts at
      // the OProj, and when it folds it can set the NewNode mutable bit
      // to e.g. final.  The OProj type needs to also reflect final.  This
      // is because we have an Ideal rule allowing a Load to bypass a
      // Store that is not in-error, but back-to-back final stores can
      // temporarily be not-in-error if the OProj does not reflect final.
      nnn.update(idx,val(),_fin,gvn);
      gvn.setype(nnn,nnn.value(gvn));
      for( Node use : nnn._uses ) gvn.setype(use,use.value(gvn));
      return mem;
    }
    return null;
  }

  @Override public Type value(GVNGCM gvn) {
    Type adr = gvn.type(adr()).base();
    if( adr.isa(TypeMemPtr.OOP0.dual()) ) return TypeObj.XOBJ; // Very high address; might fall to any valid address
    if( adr.must_nil() ) return TypeObj.OBJ;           // Not provable not-nil, so fails
    if( TypeMemPtr.OOP0.isa(adr) ) return TypeObj.OBJ; // Very low, might be any address
    if( !(adr instanceof TypeMemPtr) )
      return adr.above_center() ? TypeObj.XOBJ : TypeObj.OBJ;
    TypeMemPtr tmp = (TypeMemPtr)adr;

    Type val = gvn.type(val());     // Value
    if( !val.isa_scalar() )         // Nothing sane
      val = val.above_center() ? Type.XSCALAR : Type.SCALAR; // Pin to scalar for updates

    // Compute an updated memory state
    Type tmem = gvn.type(mem());     // Memory
    // Not updating a struct?
    if( !(tmem instanceof TypeStruct) )
      return TypeObj.make0(tmem.above_center(),tmp._aliases);
    // Missing the field to update, or storing to a final?
    TypeStruct ts = (TypeStruct)tmem;
    int idx = ts.find(_fld);
    if( idx == -1 || (ts._finals[idx]==TypeStruct.ffinal() || ts._finals[idx]==TypeStruct.fro()) )
      return TypeObj.make0(tmem.above_center(),tmp._aliases);
    // Updates to a NewNode are precise, otherwise aliased updates
    if( mem().in(0) == adr().in(0) && mem().in(0) instanceof NewNode )
      // No aliasing, even if the NewNode is called repeatedly
      return ((TypeObj)tmem).st(_fin, _fld, val);
    return ((TypeObj)tmem).update(_fin, _fld, val);
  }

  @Override public String err(GVNGCM gvn) {
    String msg = err0(gvn);
    if( msg == null ) return null;
    return _bad.errMsg(msg+_fld+"'");
  }
  private String err0(GVNGCM gvn) {
    Type t = gvn.type(adr());
    while( t instanceof TypeName ) t = ((TypeName)t)._t;
    if( t.may_nil() ) return "Struct might be nil when writing";
    if( !(t instanceof TypeMemPtr) ) return "Unknown"; // Too low, might not have any fields
    Type mem = gvn.type(mem());
    if( mem == Type.ANY ) return null;
    if( !(mem instanceof TypeStruct) ) return "No such field '";
    TypeStruct ts = (TypeStruct)mem;
    int idx = ts.find(_fld);
    if( idx == -1 )  return "No such field '";
    if( ts._finals[idx]==TypeStruct.ffinal() || ts._finals[idx]==TypeStruct.fro() ) {
      String fstr = TypeStruct.fstring(ts._finals[idx]);
      String ftype = adr() instanceof ProjNode && adr().in(0) instanceof NewNode && ((NewNode)adr().in(0))._is_closure ? "val '" : "field '.";
      return "Cannot re-assign "+fstr+" "+ftype;
    }
    return null;
  }
  @Override public Type all_type() { return TypeObj.OBJ; }
  @Override public int hashCode() { return super.hashCode()+_fld.hashCode()+_fin; }
  // Stores are never CSE/equal lest we force a partial execution to become a
  // total execution (require a store on some path it didn't happen).  Stores
  // that are common in local SESE regions can be optimized with local peepholes.
  @Override public boolean equals(Object o) { return this==o; }
}
