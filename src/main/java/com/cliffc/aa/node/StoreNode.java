package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
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

    // Stores bypass stores to unrelated fields
    //if( mem instanceof StoreNode && !Util.eq(_fld,((StoreNode)mem)._fld) )
    //  return set_def(1,((StoreNode)mem).mem(),gvn);

    // If Store is by a New, fold into the New.
    NewObjNode nnn;  int idx;
    if( mem instanceof OProjNode && mem.in(0) instanceof NewObjNode && (nnn=(NewObjNode)mem.in(0)) == adr.in(0) &&
        ctl == nnn.in(0) && !val().is_forward_ref() && !nnn._captured && (idx=nnn._ts.find(_fld))!= -1 && nnn._ts.can_update(idx) ) {
      // The OProj type needs to reflect final.  This is because we have an
      // Ideal rule allowing a Load to bypass a Store that is not in-error, but
      // back-to-back final stores can temporarily be not-in-error if the OProj
      // does not reflect final.

      // As part of the local xform rule, the memory & ptr outputs of the
      // NewNode need to update their types directly.  This Store points at the
      // OProj, and when it folds it can set the NewNode mutable bit to final -
      // which strictly runs downhill.  However, iter() calls must strictly run
      // uphill, so we have to expand the changed region to cover all the
      // "downhilled" parts and "downhill" them to match.  Outside of the
      // "downhilled" region, the types are unchanged.
      nnn.update_mod(idx,_fin,val(),gvn); // Update final field, if needed.  Runs nnn "downhill"
      for( Node use : nnn._uses ) {
        gvn.setype(use,use.value(gvn)); // Record "downhill" type for OProj, DProj
        gvn.add_work(use);              // After this is just the StoreNode, being replaced
        for( Node useuse : use._uses ) gvn.add_work(useuse);
      }
      return mem;
    }
    return null;
  }

  @Override public Type value(GVNGCM gvn) {
    if( gvn.type(ctl()) != Type.CTRL ) return TypeObj.XOBJ; // Not executed
    // Pointer is sane
    Type adr = gvn.type(adr());
    if( adr.isa(TypeMemPtr.OOP0.dual()) ) return TypeObj.XOBJ; // Very high address; might fall to any valid address
    if( adr.must_nil() ) return TypeObj.OBJ;           // Not provable not-nil, so fails
    if( TypeMemPtr.OOP0.isa(adr) ) return TypeObj.OBJ; // Very low, might be any address
    if( !(adr instanceof TypeMemPtr) )
      return adr.above_center() ? TypeObj.XOBJ : TypeObj.OBJ;
    TypeMemPtr tmp = (TypeMemPtr)adr;
    // Value is sane
    Type val = gvn.type(val());     // Value
    if( !val.isa_scalar() )         // Nothing sane
      val = val.above_center() ? Type.XSCALAR : Type.SCALAR; // Pin to scalar for updates
    // Memory is sane
    Type tmem = gvn.type(mem());     // Memory
    TypeObj tobj;
    if( tmem instanceof TypeMem )
      tobj = ((TypeMem)tmem).ld(tmp); // Get approx object being updated
    else if( tmem instanceof TypeObj )
      tobj = (TypeObj)tmem;   // Object being updated
    else                      // Else dunno what is being updated
      return TypeObj.make0(tmem.above_center());

    // Not updating a struct?
    if( !(tobj instanceof TypeStruct) )
      return TypeObj.make0(tmem.above_center());

    // Missing the field to update, or storing to a final?
    TypeStruct ts = (TypeStruct)tobj;
    int idx = ts.find(_fld);
    if( idx == -1 || (ts._finals[idx]==TypeStruct.ffinal() || ts._finals[idx]==TypeStruct.fro()) )
      return TypeObj.make0(tobj.above_center());
    // Updates to a NewNode are precise, otherwise aliased updates
    if( mem().in(0) == adr().in(0) && mem().in(0) instanceof NewNode )
      // No aliasing, even if the NewNode is called repeatedly
      return tobj.st(_fin, _fld, val);
    return tobj.update(_fin, _fld, val);
  }

  @Override public String err(GVNGCM gvn) {
    String msg = err0(gvn);
    if( msg == null ) return null;
    return _bad.errMsg(msg+_fld+"'");
  }
  private String err0(GVNGCM gvn) {
    Type t = gvn.type(adr());
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
      String ftype = adr() instanceof ProjNode && adr().in(0) instanceof NewObjNode && ((NewObjNode)adr().in(0))._is_closure ? "val '" : "field '.";
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
