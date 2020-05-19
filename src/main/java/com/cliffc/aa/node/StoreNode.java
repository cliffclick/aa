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

    // Stores bypass a Merge to the specific alias
    Type ta = gvn.type(adr);
    int alias;
    if( ta instanceof TypeMemPtr && mem instanceof MemMergeNode &&
        (alias=((TypeMemPtr)ta)._aliases.strip_nil().abit()) != -1 )
      return new StoreNode(this,((MemMergeNode)mem).obj(alias,gvn),adr);

    // Stores bypass stores to unrelated fields.  TODO: Cannot really do this -
    // need parallel field updates.
    //if( mem instanceof StoreNode && !Util.eq(_fld,((StoreNode)mem)._fld) )
    //  return set_def(1,((StoreNode)mem).mem(),gvn);

    // If Store is by a New and no other Stores, fold into the New.
    NewObjNode nnn;  int idx;
    if( mem instanceof OProjNode &&
        mem.in(0) instanceof NewObjNode && (nnn=(NewObjNode)mem.in(0)) == adr.in(0) &&
        mem._uses._len==1 && !val().is_forward_ref() && !DefMemNode.CAPTURED.get(nnn._alias) &&
        (idx=nnn._ts.find(_fld))!= -1 && nnn._ts.can_update(idx) ) {
      // Update the value, and perhaps the final field
      nnn.update(idx,_fin,val(),gvn);
      return mem;               // Store is replaced by using the New directly.
    }

    // Store can bypass a Call, if the memory is not returned from the call,
    // This optimization is specifically targeting simple recursive functions.
    //if( ta instanceof TypeMemPtr && mem instanceof MProjNode && mem.in(0) instanceof CallEpiNode ) {
    //  TypeMemPtr tmp = (TypeMemPtr)ta;
    //  CallEpiNode cepi = (CallEpiNode)mem.in(0);
    //  TypeMem retmem = (TypeMem)((TypeTuple)gvn.type(cepi)).at(3);
    //  if( !cepi.is_copy() && retmem.is_clean(tmp.aliases(),_fld) )
    //    return set_def(1,cepi.call().mem(),gvn);
    //}

    // Store can bypass a Call, if the memory is not returned from the call,
    // and the pointer predates the call.  This optimization is specifically
    // targeting simple recursive functions.
    //Node pre_call_mem = bypass_call(gvn);
    //if( pre_call_mem != null )  // Use memory before the call instead of after
    //  return set_def(1,pre_call_mem,gvn);

    return null;
  }

  @Override public Type value(GVNGCM gvn) {
    Type adr = gvn.type(adr());
    if( adr.isa(TypeMemPtr.OOP0.dual()) ) return TypeStruct.ANYSTRUCT; // Very high address; might fall to any valid address
    if( TypeMemPtr.OOP0.isa(adr) ) return TypeStruct.ALLSTRUCT; // Very low, might be any address
    if( !(adr instanceof TypeMemPtr) )
      return adr.above_center() ? TypeStruct.ANYSTRUCT : TypeStruct.ALLSTRUCT;
    TypeMemPtr tmp = (TypeMemPtr)adr;
    // Value is sane
    Type val = gvn.type(val());     // Value
    if( !val.isa_scalar() )         // Nothing sane
      val = val.above_center() ? Type.XSCALAR : Type.SCALAR; // Pin to scalar for updates

    // Store can bypass a Call, if the memory is not returned from the call.
    // This optimization is specifically targeting simple recursive functions.
    Node mem = mem();
    //if( mem instanceof MProjNode && mem.in(0) instanceof CallEpiNode ) {
    //  CallEpiNode cepi = (CallEpiNode)mem.in(0);
    //  TypeMem retmem = (TypeMem)((TypeTuple)gvn.type(cepi)).at(3);
    //  if( !cepi.is_copy() && retmem.is_clean(tmp.aliases(),_fld) )
    //    mem = cepi.call().mem();
    //}
    // Store can bypass a Call, if the memory is not returned from the call,
    // and the pointer predates the call.  This optimization is specifically
    // targeting simple recursive functions.
    //Node pre_call_mem = bypass_call(gvn);
    //if( pre_call_mem != null )  // Use memory before the call instead of after
    //  mem = pre_call_mem;

    // Convert from memory to the struct being updated
    Type tmem = gvn.type(mem);
    TypeObj tobj;
    if( tmem instanceof TypeMem )
      tobj = ((TypeMem)tmem).ld(tmp); // Get approx object being updated
    else if( tmem instanceof TypeObj )
      tobj = (TypeObj)tmem;   // Object being updated
    else                      // Else dunno what is being updated
      return tmem.above_center() ? TypeStruct.ANYSTRUCT : TypeStruct.ALLSTRUCT;

    // Not updating a struct?
    if( !(tobj instanceof TypeStruct) )
      // Updating XOBJ means updating any choice, and we choose no-change.
      // Updating  OBJ means we're already as low as we can go.
      return tobj.above_center() ? TypeStruct.ANYSTRUCT : TypeStruct.ALLSTRUCT;

    // Update the field.  Illegal updates make no changes (except clear 'clean' bit).
    TypeStruct ts = (TypeStruct)tobj;
    // Updates to a NewNode are precise, otherwise aliased updates
    if( mem().in(0) == adr().in(0) && mem().in(0) instanceof NewNode && !adr.must_nil())
      // No aliasing, even if the NewNode is called repeatedly
      return ts.st(_fin, _fld, val);
    // Imprecise update
    return ts.update(_fin, _fld, val);
  }

  // Returns pre_call_mem if Store can bypass Call memory.
  private Node bypass_call(GVNGCM gvn) {
    // Store can bypass a Call, if the memory is not returned from the call,
    // and the pointer predates the call.  This optimization is specifically
    // targeting simple recursive functions.

    // Store memory not after a call
    Node mem = mem();
    if( !(mem instanceof MProjNode) || !(mem.in(0) instanceof CallEpiNode) ) return null;
    CallEpiNode cepi = (CallEpiNode)mem.in(0);
    if( cepi.is_copy() ) return null; // Call is collapsing
    Type tadr = gvn.type(adr());
    if( !(tadr instanceof TypeMemPtr) ) return null; // Address is bad
    int alias = ((TypeMemPtr)tadr).aliases().abit();
    if( alias == -1 ) return null;  // Address not-nil already, and a single alias
    // Address must predate the call, and is not passed into the call, so the
    // Store cannot be storing any Call result.
    Node pctrl = adr();         // Find address control
    while( (tadr=gvn.type(pctrl)) != Type.CTRL && tadr!=Type.XCTRL )
      pctrl = pctrl.in(0);
    // Address control dominates call control
    CallNode call = cepi.call();
    final Node fpctrl = pctrl;
    if( call.walk_dom_last(n -> n==fpctrl) == null ) return null;

    TypeTuple tcall = (TypeTuple)gvn.type(call);
    TypeMem tcm = (TypeMem)tcall.at(1);
    Node pre_call_mem = call.mem();
    if( tcm.at(alias).above_center() ) // Call does not produce the memory
      return pre_call_mem;
    if( pre_call_mem instanceof MemMergeNode &&
        ((MemMergeNode)pre_call_mem).alias2idx(alias) != 0 )
      return pre_call_mem;
    // Call produces memory into function, or call-leading MemMerge not precise
    // about alias... so we assume it goes into the call.
    return null;
  }


  // Compute the liveness local contribution to def's liveness.  Ignores the
  // incoming memory types, as this is a backwards propagation of demanded
  // memory.
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) {
    if( mem()!=def ) return _live == TypeMem.DEAD ? TypeMem.DEAD : TypeMem.EMPTY; // Non-memory use basic liveness
    // Pass the liveness along
    return _live;
  }
  // Liveness is specific to the stored-aliases
  @Override public boolean basic_liveness() { return false; }

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
