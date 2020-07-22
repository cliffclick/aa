package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeMemPtr;
import com.cliffc.aa.type.TypeStruct;
import com.cliffc.aa.util.IBitSet;

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
  @Override boolean is_mem() { return true; }

  Node mem() { return in(1); }
  Node adr() { return in(2); }
  Node val() { return in(3); }

  @Override public Node ideal(GVNGCM gvn, int level) {
    Node mem = mem();
    Node adr = adr();
    Type ta = gvn.type(adr);
    TypeMemPtr tmp = ta instanceof TypeMemPtr ? (TypeMemPtr)ta : null;

    // If Store is by a New and no other Stores, fold into the New.
    NewObjNode nnn;  int idx;
    if( mem instanceof MProjNode &&
        mem.in(0) instanceof NewObjNode && (nnn=(NewObjNode)mem.in(0)) == adr.in(0) &&
        mem._uses._len==2 && !val().is_forward_ref() &&
        (idx=nnn._ts.find(_fld))!= -1 && nnn._ts.can_update(idx) ) {
      // Update the value, and perhaps the final field
      nnn.update(idx,_fin,val(),gvn);
      return mem;               // Store is replaced by using the New directly.
    }

    // If Store is of a memory-writer, and the aliases do not overlap, make parallel with a Join
    if( tmp != null && mem.is_mem() && mem.check_solo_mem_writer(this) ) {
      IBitSet esc2 = mem.escapees(gvn);
      if( !tmp._aliases.overlaps(esc2) ) {
        Node head;
        if( mem instanceof StoreNode ) head=mem;
        else if( mem instanceof MProjNode && mem.in(0) instanceof NewNode ) head=mem.in(0);
        else throw com.cliffc.aa.AA.unimpl(); // Break out another SESE split
        // head is the 1 memory writer after head.in
        if( head.in(1).check_solo_mem_writer(head) &&
            // Cannot have any Loads following mem; because after the split
            // they will not see the effects of previous stores that also move
            // into the split.  However, a Load-after-Store will fold anyways.
            ((mem._uses._len==1) ||
             (mem._uses._len==2 && mem._uses.find(Env.DEFMEM)!= -1 ) ) ) {
          Node st2 = gvn.xform(new StoreNode(this,mem,adr).keep());
          MemSplitNode msp = (MemSplitNode)gvn.xform(new MemSplitNode(st2.unhook()).keep());
          MProjNode mprj = (MProjNode)gvn.xform(new MProjNode(msp,0));
          MemJoinNode mjn = new MemJoinNode(mprj);
          set_def(1,null,gvn);                // Remove extra mem-writer
          mjn.add_alias_above(gvn,msp.mem()); // Move 'this' clone st2 into Split
          mjn.add_alias_above(gvn,head);      // Move from 'mem' to 'head' into Split
          msp.unhook();
          // Reverse propagate new live info
          mjn._live = _live;
          for( Node x : new Node[]{mprj,st2,st2.in(1),mem,head,head.in(1),msp} )
            x._live = x.live(gvn);
          return mjn;
        }
      }
    }

    // If Store is of a MemJoin and it can enter the split region, do so.
    if( _keep==0 && tmp != null && mem instanceof MemJoinNode && mem.check_solo_mem_writer(this) ) {
      Node memw = get_mem_writer();
      // Check the address does not have a memory dependence on the Join.
      // TODO: This is super conservative
      if( memw != null && adr instanceof ProjNode && adr.in(0) instanceof NewNode ) {
        MemJoinNode mjn = (MemJoinNode)mem;
        StoreNode st = (StoreNode)gvn.xform(new StoreNode(keep(),mem,adr).keep());
        mjn.add_alias_below(gvn,st,st.unhook(),memw);
        unhook();
        gvn.setype(st ,st .value(gvn));
        gvn.setype(mjn,mjn.value(gvn));
        mjn._live = mjn.live(gvn);
        st._live = st.live(gvn);
        st.mem()._live = st.mem().live(gvn);
        gvn.add_work_defs(mjn);
        return mjn;
      }
    }

    return null;
  }

  // StoreNode needs to return a TypeObj for the Parser.
  @Override public TypeMem value(GVNGCM gvn) {
    Type mem = gvn.type(mem());
    Type adr = gvn.type(adr());
    Type val = gvn.type(val());   // Value
    if( !(mem instanceof TypeMem   ) ) return mem.oob(TypeMem.ALLMEM);
    if( !(adr instanceof TypeMemPtr) ) return adr.oob(TypeMem.ALLMEM);
    TypeMem    tmem= (TypeMem   )mem;
    TypeMemPtr tmp = (TypeMemPtr)adr;

    return tmem.update(tmp._aliases,_fin,_fld,val);
  }
  @Override IBitSet escapees(GVNGCM gvn) {
    Type adr = gvn.type(adr());
    if( !(adr instanceof TypeMemPtr) ) return adr.above_center() ? IBitSet.EMPTY : IBitSet.FULL;
    return ((TypeMemPtr)adr)._aliases.bitset();
  }

  @Override public boolean basic_liveness() { return false; }
  // Compute the liveness local contribution to def's liveness.  Ignores the
  // incoming memory types, as this is a backwards propagation of demanded
  // memory.
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) {
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
