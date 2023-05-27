package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.unimpl;
import static com.cliffc.aa.AA.MEM_IDX;
import static com.cliffc.aa.AA.CTL_IDX;

// Store a value into a named struct field.  Does it's own nil-check and value
// testing; also checks final field updates.
public class StoreNode extends Node {
  private final Parse _bad;
  public StoreNode( Node mem, Node adr, Node val, Parse bad ) {
    super(OP_STORE,null,mem,adr,val);
    _bad = bad;    // Tests can pass a null, but nobody else does
  }
  private StoreNode( StoreNode st, Node mem, Node adr ) { this(mem,adr,st.rez(),st._bad); }

  @Override public boolean is_mem() { return true; }

  Node mem() { return in(1); }
  Node adr() { return in(2); }
  Node rez() { return in(3); }

  @Override public Type value() {
    Node mem = mem(), adr = adr(), rez = rez();
    Type tmem = mem._val;
    Type tadr = adr._val;
    Type tval = rez==null ? Type.ANY : rez._val;  // Value
    if( !(tmem instanceof TypeMem    tm ) ) return tmem .oob(TypeMem.ALLMEM);
    if( !(tadr instanceof TypeMemPtr tmp) ) return tadr .oob(TypeMem.ALLMEM);
    TypeStruct tvs = tval instanceof TypeStruct ? (TypeStruct)tval : tval.oob(TypeStruct.ISUSED);
    if( tmp.above_center() ) tvs = TypeStruct.UNUSED;

    // Precise update
    if( adr instanceof NewNode nnn ) {
      assert Math.abs(tmp._aliases.abit())==nnn._alias;
      return tm.set(nnn._alias,tvs);
    }
    
    // Meet no aliases into memory
    if( tmp.above_center() || tmp._aliases.is_empty() )
      return tm;

    // Must be empty or below center.  Meet into the aliases
    return tm.update(tmp._aliases,tvs,false);
  }

  // Compute the liveness local contribution to def's liveness.  Turns around
  // value into live: if values are ANY then nothing is demand-able.
  @Override public Type live_use( int i ) {
    Node def = in(i);
    // Liveness as a TypeMem
    TypeMem live = _live== Type.ALL ? RootNode.def_mem(def) : (TypeMem)_live;
    // Input memory as a TypeMem
    Type mem0 = mem()._val;
    TypeMem mem = mem0== Type.ANY ? TypeMem.ANYMEM
      : (mem0== Type.ALL ? TypeMem.ALLMEM
         : (TypeMem)mem0);
    TypeMemPtr tmp = adr()._val instanceof TypeMemPtr tmp0 ? tmp0 : adr()._val.oob(TypeMemPtr.ISUSED);

    // Liveness for memory?
    if( i==MEM_IDX ) {
      adr().deps_add(def);
      // Assume all above center aliases kill everything (will optimistically
      // kill what we need) to make uses go away
      if( tmp._aliases.above_center() ) {
        for( int alias : tmp._aliases )
          live = live.set(alias,TypeStruct.UNUSED);
        return live;
      }
      mem().deps_add(def);
      // Precise update if it's a single alias, and no value at alias is
      // arriving here OR directly storing from the NewNode.
      Node adr = adr();
      if( adr instanceof FreshNode frsh ) adr = frsh.id();
      int alias = tmp._aliases.abit();
      if( adr instanceof NewNode nnn && (tmp._aliases.is_empty() || nnn._alias==alias) )
        return live.set(nnn._alias,TypeStruct.UNUSED); // Precise set, no longer demanded

      // Since empty can fall to any single precise alias, we need to assume
      // all things are not demanded until one or more aliases show up.
      if( tmp._aliases.is_empty() ) {
        for( int ax=1; ax<mem.len(); ax++ )
          if( mem.at(ax).above_center() )
            live = live.set(ax,TypeStruct.UNUSED);
      } else {
        if( alias!=-1 && mem.at(alias).above_center() )
          return live.set(alias,TypeStruct.UNUSED); // Precise set, no longer demanded
      }
      // Imprecise update, cannot dataflow kill alias going backwards
      return live;
    }
    // Address changes liveness, the rez can be more live
    if( rez()!=null ) adr().deps_add(rez());

    // Demanded struct; if ptr just any/all else demand struct
    TypeStruct ts = live.ld(tmp);
    return i==CTL_IDX ? ts.oob() : ts;
  }

  @Override public Node ideal_reduce() {
    if( is_prim() ) return null;
    if( _live == Type.ANY ) return null; // Dead from below; nothing fancy just await removal
    Node mem = mem();
    Node adr = adr();
    Type ta = adr._val;
    TypeMemPtr tmp = ta instanceof TypeMemPtr ? (TypeMemPtr)ta : null;

    // Is this Store dead from below?
    if( mem==this ) return null; // Dead self-cycle
    if( tmp!=null && mem._val instanceof TypeMem ) {
      // Address is high, do not bother storing.  Kill stored thing.
      // Keep the store op until values are monotonic.
      if( tmp.above_center() && rez() != null )
        return Env.GVN.add_reduce(set_def(3,null)); // Try again
      // Same/same up/down, or no value readers
      if( _live.isa(mem._live) && (_uses._len==1 || mem._val == _val) ) {
        // If dead from either above or below, we can remove
        if( tmp.above_center() ) return mem;
        TypeStruct ts0 = (_live instanceof TypeMem tm ? tm : _live.oob(TypeMem.ALLMEM)).ld(tmp);
        if( ts0==TypeStruct.UNUSED ) {
          if( mem._val == _val ) return mem; // Same/same or no readers, just delete
          //if( _uses._len==1 )
          //  return mem;
          if( rez()!=null )
            return Env.GVN.add_reduce(set_def(3,null)); // Don't store, keep until monotonic
        }
      }
      mem.deps_add(this);   // Input address changes, check reduce
      deps_add(this);       // Our   address changes, check reduce
    }

    // Store of a Store, same address
    if( mem instanceof StoreNode st ) {
      Node adr0 = st.adr();
      if( adr  instanceof FreshNode f ) adr  = f.id();
      if( adr0 instanceof FreshNode f ) adr0 = f.id();
      if( adr == adr0 ) {
        // Do not bypass a parallel writer
        if( st.check_solo_mem_writer(this) &&
            // And liveness aligns
            st._live.isa(st.mem()._live) ) {
          // Storing same-over-same, just use the first store
          if( rez()==st.rez() ) return st;
          // If not wiping out an error, wipe out the first store
          if( st.rez()==null || st.rez().err(true)==null ) {
            set_def(1,st.mem());
            return this;
          }
        } else {
          mem.deps_add(this);    // If become solo writer, check again
        }
      } else {
        st.adr().deps_add(this);      // If address changes, check again
      }
    }

    // Store of a Load
    if( rez() instanceof LoadNode ld && ld.adr()==adr && ld.mem()==mem )
      return mem;

    //// Escape a dead MemSplit
    //if( mem instanceof MProjNode && mem.in(0) instanceof MemSplitNode msp &&
    //    msp.join()==null ) {
    //  set_def(1,msp.mem());
    //  xval();                   // Update memory state to include all the default memory
    //  return this;
    //}

    //
    //// If Store is of a MemJoin and it can enter the split region, do so.
    //// Requires no other memory *reader* (or writer), as the reader will
    //// now see the Store effects as part of the Join.
    //if( tmp != null && mem instanceof MemJoinNode && mem._uses._len==1 ) {
    //  Node memw = _uses._len==0 ? this : get_mem_writer(); // Zero or 1 mem-writer
    //  // Check the address does not have a memory dependence on the Join.
    //  // TODO: This is super conservative
    //  if( adr instanceof FreshNode ) adr = ((FreshNode)adr).id();
    //  if( memw != null && adr instanceof ProjNode && adr.in(0) instanceof NewNode )
    //    return ((MemJoinNode)mem).add_alias_below_new(new StoreNode(this,mem,adr()),this);
    //}
    //
    return null;
  }

  // Recursively collapse a set of SetFields into a single-use StructNode
  static StructNode _fold(Node rez) {
    if( rez instanceof StructNode st ) return st;
    if( rez instanceof LoadNode ) return null;
    SetFieldNode sfn = (SetFieldNode)rez;
    StructNode st = _fold(sfn.in(0));
    if( st==null || !st.set_fld(sfn._fld,sfn._fin,sfn.in(1),false) )
      return null;
    return st;
  }


  @Override public Node ideal_grow() {
    Node mem = mem();
    Node adr = adr();

    // If Store is of a memory-writer, and the aliases do not overlap, make parallel with a Join
    if( adr._val instanceof TypeMemPtr tmp &&
        mem.is_mem() && mem.check_solo_mem_writer(this) ) {
      Node head2=null;
      if( mem instanceof StoreNode ) head2=mem;
      else if( mem instanceof MProjNode ) {
        if( mem.in(0) instanceof CallEpiNode cepi && !cepi._is_copy ) head2 = cepi.call();
        else if( mem.in(0) instanceof NewNode nnn ) head2 = nnn;
      }
      // Check no extra readers/writers at the split point
      if( head2 != null ) {
        // && MemSplitNode.check_split(this,escapees(),mem) ) {
      //  MemSplitNode.insert_split(this, escapees(), this, mem, head2);
      //  assert _uses._len==1 && _uses.at(0) instanceof MemJoinNode;
      //  return _uses.at(0); // Return the mem join
        return null;  // TODO: Turn back on
      }
    }
    return null;
  }

  // Given a tptr, trez:
  //    ptr.load().unify(rez)
  @Override public boolean has_tvar() { return true; }
  @Override public TV3 _set_tvar() {
    assert rez()!=null;         // Should have cleared out during iter
    TV3 adr = adr().set_tvar();
    TV3 rez = rez().set_tvar();
    TVStruct stz;
    if( rez instanceof TVStruct stz0 ) stz = stz0;
    else  // Open empty struct
      rez.unify(stz = new TVStruct(true),false);

    if( adr instanceof TVPtr ptr ) ptr.load().unify(stz,false);
    else adr.unify(new TVPtr(BitsAlias.EMPTY,stz),false);
    return null;
  }

  @Override public boolean unify( boolean test ) { return false; }

  @Override public ErrMsg err( boolean fast ) {
    Type tadr = adr()._val;
    Type tmem = mem()._val;
    if( tadr.above_center() ) return null;
    if( tmem.above_center() ) return null;
    if( !(tadr instanceof TypeMemPtr ptr) )
      return bad("Unknown",fast,null); // Not a pointer nor memory, cannot store a field
    if( !(tmem instanceof TypeMem) ) return bad("Unknown",fast,null);
    if( ptr.must_nil() ) return fast ? ErrMsg.FAST : ErrMsg.niladr(_bad,"Struct might be nil when writing",null);
    return null;
  }
  private ErrMsg bad( String msg, boolean fast, TypeStruct to ) {
    if( fast ) return ErrMsg.FAST;
    //boolean is_closure = adr() instanceof NewNode nnn && nnn._is_closure;
    //return ErrMsg.field(_bad,msg,_fld,is_closure,to);
    throw unimpl();
  }

}
