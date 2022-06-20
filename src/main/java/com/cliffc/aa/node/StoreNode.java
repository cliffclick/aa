package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.unimpl;

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
    Type tval = rez._val;  // Value
    if( !(tmem instanceof TypeMem    tm ) ) return tmem .oob(TypeMem.ALLMEM);
    if( !(tadr instanceof TypeMemPtr tmp) ) return tadr .oob(TypeMem.ALLMEM);
    TypeStruct tvs = tval instanceof TypeStruct ? (TypeStruct)tval : tval.oob(TypeStruct.ISUSED);

    // Struct is dead from below?  Value is always ANY.
    TypeStruct live = _live instanceof TypeMem tlive ? tlive.ld(tmp) : _live.oob(TypeStruct.ISUSED);
    Node str = LoadNode.find_previous_struct(mem, adr, tmp._aliases, false );
    boolean precise = adr.in(0) instanceof NewNode nnn && (nnn.rec()==str); // Precise is replace, imprecise is MEET
    return tm.update(tmp._aliases,tvs,precise,live);
  }
  // For most memory-producing Nodes, exactly 1 memory producer follows.
  private Node get_mem_writer() {
    for( Node use : _uses ) if( use.is_mem() ) return use;
    return null;
  }

  // Compute the liveness local contribution to def's liveness.  Ignores the
  // incoming memory types, as this is a backwards propagation of demanded
  // memory.
  @Override public Type live_use( Node def ) {
    if( def==mem() ) return _live; // Pass full liveness along
    assert def==adr() || def==rez();
    // If this alias is not alive, then neither the address nor value are alive.
    if( !(_live instanceof TypeMem tmem) ) return _live.oob();
    Type adr = adr()._val;
    if( !(adr instanceof TypeMemPtr tmp ) ) return adr.oob();
    TypeStruct ts = tmem.ld(tmp);
    if( def==adr() ) return ts.oob(); // Live-use for the adr(), which is a Type.ANY/ALL
    return ts;                  // Live-use for the rez() which is a TypeStruct liveness
  }

  @Override public void add_flow_use_extra(Node chg) {
    if( chg==adr() && !chg._val.above_center() ) // Address becomes alive, implies rez is more alive
      Env.GVN.add_flow(rez());
  }

  // Liveness changes, check if reduce
  @Override public void add_flow_extra(Type old) {
    Env.GVN.add_reduce(this); // Args can be more-alive
    if( old.above_center() && !_live.above_center() ) Env.GVN.add_flow(this);
  }

  @Override public Node ideal_reduce() {
    if( _live == Type.ANY ) return null; // Dead from below; nothing fancy just await removal
    Node mem = mem();
    Node adr = adr();
    Type ta = adr._val;
    TypeMemPtr tmp = ta instanceof TypeMemPtr ? (TypeMemPtr)ta : null;

    // Is this Store dead from below?
    if( mem==this ) return null; // Dead self-cycle
    if( ta.above_center() ) return mem; // All memory is high, so dead
    if( tmp!=null && mem._val instanceof TypeMem ) {
      TypeStruct ts0 = (_live instanceof TypeMem tm ? tm : _live.oob(TypeMem.ALLMEM)).ld(tmp);
      if( ts0.above_center() )  // Dead from below
        return mem;
    }

    // No need for 'Fresh' address, as Stores have no TVar (produce memory not a scalar)
    if( adr() instanceof FreshNode )
      return set_def(2,((FreshNode)adr()).id());

    // Escape a dead MemSplit
    if( mem instanceof MProjNode && mem.in(0) instanceof MemSplitNode msp &&
        msp.join()==null ) {
      set_def(1,msp.mem());
      xval();                   // Update memory state to include all the default memory
      return this;
    }

    //// If Store is into a value New, fold into the New.
    //// Happens inside value constructors.
    //if( adr instanceof NewNode nnn && nnn._is_val && _fold(nnn) )
    //  return mem;

    // Store into a NewNode, same memory and address
    if( mem instanceof MProjNode && adr instanceof ProjNode && mem.in(0) == adr.in(0) && mem.in(0) instanceof NewNode nnn &&
        // Do not bypass a parallel writer
        mem.check_solo_mem_writer(this) ) {
      StructNode st = _fold(rez());
      Env.GVN.revalive(st,mem.in(0),mem);
      return st==null ? null : mem;
    }
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
        if( mem.in(0) instanceof CallEpiNode cepi ) head2 = cepi.call();
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
  // If changing an input or value allows the store to no longer be in-error,
  // following Loads can collapse
  @Override public void add_reduce_extra() {
    for( Node use : _uses )
      if( use instanceof LoadNode )
        Env.GVN.add_mono(Env.GVN.add_reduce(use));
  }

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

  @Override public boolean has_tvar() { return false; }

  @Override public boolean unify( boolean test ) {
    TV2 ptr = adr().tvar();
    TV2 rez = rez().tvar();
    return ptr.unify(rez,test);
  }

  @Override public void add_work_hm() {
    Env.GVN.add_flow(adr());
    Env.GVN.add_flow(rez());
  }

}
