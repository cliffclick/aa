package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

// Store a value into a named struct field.  Does it's own nil-check and value
// testing; also checks final field updates.
public class StoreNode extends Node {
  final String _fld;        // Field being updated
  private final byte _fin;  // TypeStruct.ffinal or TypeStruct.frw
  private final Parse _bad;
  public StoreNode( Node mem, Node adr, Node val, byte fin, String fld, Parse bad ) {
    super(OP_STORE,null,mem,adr,val);
    _fld = fld;
    _fin = fin;
    _bad = bad;    // Tests can pass a null, but nobody else does
  }
  private StoreNode( StoreNode st, Node mem, Node adr ) { this(mem,adr,st.val(),st._fin,st._fld,st._bad); }
  //public  StoreNode( StoreNode st, Node ctr, Node mem, Node adr, Node val ) { this(ctr,mem,adr,   val  ,st._fin,st._eqv,st._bad); }

  String xstr() { return "."+_fld+"="; } // Self short name
  String  str() { return xstr(); }   // Inline short name

  Node mem() { return in(1); }
  Node adr() { return in(2); }
  Node val() { return in(3); }

  @Override public Node ideal(GVNGCM gvn, int level) {
    Node mem = mem();
    Node adr = adr();
    Type ta = gvn.type(adr);
    TypeMemPtr tmp = ta instanceof TypeMemPtr ? (TypeMemPtr)ta : null;

    // Stores bypass a Merge to the specific alias
    int alias;
    if( tmp !=null && mem instanceof MemMergeNode &&
        (alias=tmp._aliases.strip_nil().abit()) != -1 )
      return new StoreNode(this,((MemMergeNode)mem).obj(alias,gvn),adr);

    // Stores bypass a Split.
    if( mem instanceof MProjNode && mem.in(0) instanceof MemSplitNode ) {
      return set_def(1,mem.in(0).in(0),gvn);
    }

    // If Store is by a New and no other Stores, fold into the New.
    NewObjNode nnn;  int idx;
    if( mem instanceof OProjNode &&
        mem.in(0) instanceof NewObjNode && (nnn=(NewObjNode)mem.in(0)) == adr.in(0) &&
        mem._uses._len==2 && !val().is_forward_ref() && !DefMemNode.CAPTURED.get(nnn._alias) &&
        (idx=nnn._ts.find(_fld))!= -1 && nnn._ts.can_update(idx) ) {
      // Update the value, and perhaps the final field
      nnn.update(idx,_fin,val(),gvn);
      return mem;               // Store is replaced by using the New directly.
    }

    return null;
  }

  // StoreNode needs to return a TypeObj for the Parser.
  @Override public TypeObj value(GVNGCM gvn) {
    Type adr = gvn.type(adr());
    if( !(adr instanceof TypeMemPtr) ) return adr.oob(TypeStruct.ALLSTRUCT);
    TypeMemPtr tmp = (TypeMemPtr)adr;
    Type val = gvn.type(val());   // Value

    // Convert from memory to the struct being updated
    Node mem = mem();
    Type tmem = gvn.type(mem);
    TypeObj tobj;
    if( tmem instanceof TypeMem )
      tobj = ((TypeMem)tmem).ld(tmp); // Get approx object being updated
    else if( tmem instanceof TypeObj )
      tobj = (TypeObj)tmem;   // Object being updated
    else                      // Else dunno what is being updated
      return tmem.oob(TypeStruct.ALLSTRUCT);

    // Not updating a struct?
    if( !(tobj instanceof TypeStruct) )
      // Updating XOBJ means updating any choice, and we choose no-change.
      // Updating  OBJ means we're already as low as we can go.
      return tobj.oob(TypeStruct.ALLSTRUCT);

    // Update the field.  Illegal updates make no changes.
    TypeStruct ts = (TypeStruct)tobj;
    // Updates to a NewNode are precise, otherwise aliased updates
    if( mem().in(0) == adr().in(0) && mem().in(0) instanceof NewNode && !adr.must_nil())
      // No aliasing, even if the NewNode is called repeatedly
      return ts.st(_fin, _fld, val);
    // Imprecise update
    return ts.update(_fin, _fld, val);
  }

  // Compute the liveness local contribution to def's liveness.  Ignores the
  // incoming memory types, as this is a backwards propagation of demanded
  // memory.
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) {
    if( _live==TypeMem.DEAD ) return TypeMem.DEAD;
    if( def==mem() ) return _live; // Pass full liveness along
    if( def==adr() ) return TypeMem.ALIVE; // Basic aliveness
    if( def==val() ) return TypeMem.ESCAPE;// Value escapes
    throw com.cliffc.aa.AA.unimpl();       // Should not reach here
  }

  @Override public String err(GVNGCM gvn) {
    String msg = err0(gvn);
    if( msg == null ) return null;
    return _bad.errMsg(msg+_fld+"'");
  }
  private String err0(GVNGCM gvn) {
    Type t = gvn.type(adr());
    if( t.must_nil() ) return "Struct might be nil when writing '";
    if( t==Type.ANY ) return null;
    if( !(t instanceof TypeMemPtr) ) return "Unknown"; // Too low, might not have any fields
    Type mem = gvn.type(mem());
    if( mem == Type.ANY ) return null;
    if( mem instanceof TypeMem )
      mem = ((TypeMem)mem).ld((TypeMemPtr)t);
    if( !(mem instanceof TypeStruct) ) return "No such field '";
    TypeStruct ts = (TypeStruct)mem;
    int idx = ts.find(_fld);
    if( idx == -1 )  return "No such field '";
    if( !ts.can_update(idx) ) {
      String fstr = TypeStruct.fstring(ts.fmod(idx));
      String ftype = adr() instanceof ProjNode && adr().in(0) instanceof NewObjNode && ((NewObjNode)adr().in(0))._is_closure ? "val '" : "field '.";
      return "Cannot re-assign "+fstr+" "+ftype;
    }
    return null;
  }
  @Override public int hashCode() { return super.hashCode()+_fld.hashCode()+_fin; }
  // Stores are never CSE/equal lest we force a partial execution to become a
  // total execution (require a store on some path it didn't happen).  Stores
  // that are common in local SESE regions can be optimized with local peepholes.
  @Override public boolean equals(Object o) { return this==o; }
}
