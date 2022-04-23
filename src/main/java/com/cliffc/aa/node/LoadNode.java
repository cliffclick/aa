package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.*;

// Load a struct from memory.  Does it's own nil-check testing.
public class LoadNode extends Node {
  private final Parse _bad;

  public LoadNode( Node mem, Node adr, Parse bad ) {
    super(OP_LOAD,null,mem,adr);
    _bad = bad;
  }
  Node mem() { return in(MEM_IDX); }
  Node adr() { return in(DSP_IDX); }
  private Node set_mem(Node a) { return set_def(MEM_IDX,a); }
  //public TypeFld find(TypeStruct ts) { return ts.get(_fld); }

  @Override public Type value() {
    Type tadr = adr()._val;
    Type tmem = mem()._val;       // Memory
    // We allow Loads against Clazz types
    if( tadr instanceof TypeStruct ts ) {
      String tname = ts.clz().substring(0,ts.clz().length()-1);
      StructNode clz = Env.PROTOS.get(tname);
      if( clz != null ) return clz._val;
    }
    if( !(tadr instanceof TypeMemPtr tmp) ) return tadr.oob();
    if( !(tmem instanceof TypeMem    tm ) ) return tmem.oob(); // Nothing sane
    return tm.ld(tmp);
  }

  @Override public void add_flow_use_extra(Node chg) {
    if( chg==adr() ) { Env.GVN.add_flow(mem()); Env.GVN.add_reduce(this); } // Address into a Load changes, the Memory can be more alive, or this not in Error
    if( chg==mem() ) Env.GVN.add_flow(mem());  // Memory value lifts to ANY, memory live lifts also.
    if( chg==mem() ) Env.GVN.add_flow(adr());  // Memory value lifts to an alias, address is more alive
    // Memory improves, perhaps Load can bypass Call
    if( chg==mem() && mem().in(0) instanceof CallEpiNode ) Env.GVN.add_reduce(this);
  }

  // The only memory required here is what is needed to support the Load.
  // If the Load is alive, so is the address.

  // If the Load computes a constant, the address live-ness is determined how
  // Combo deals with constants, and not here.
  @Override public Type live_use(Node def ) {
    if( def==adr() ) return Type.ALL;
    Type mem = mem()._val;
    Type ptr = adr()._val;
    if( !(mem instanceof TypeMem tmem) ) return mem.oob(TypeMem.ALLMEM); // Not a memory?
    if( ptr instanceof TypeStruct ) return ptr.oob(TypeMem.ALLMEM); // Loading from a clazz
    if( !(ptr instanceof TypeMemPtr tptr) ) return ptr.oob(TypeMem.ALLMEM); // Not a pointer?
    if( tptr.above_center() ) return TypeMem.ANYMEM; // Loaded from nothing
    // Only the named aliases is live.
    return tmem.remove_no_escapes(tptr._aliases);
  }

  // Standard memory unification; the Load unifies with the loaded field.
  @Override public boolean unify( boolean test ) {
    //TV2 self = tvar();
    //TV2 rec = adr().tvar();
    //rec.push_dep(this);
    //
    //TV2 fld = rec.arg(_fld);
    //if( fld!=null )           // Unify against a pre-existing field
    //  return fld.unify(self, test);
    //
    //// Add struct-ness if possible
    //if( !rec.is_obj() && !rec.is_nil() )
    //  rec.make_open_struct();
    //// Add the field
    //if( rec.is_obj() && rec.is_open() ) {
    //  rec.add_fld(_fld,self);
    //  return true;
    //}
    //// Closed/non-record, field is missing
    //if( self._err!=null ) return false;
    //self._err = "Missing field "+_fld;
    //return true;
    throw unimpl();
  }
  public void add_work_hm() {
    super.add_work_hm();
    Env.GVN.add_flow(adr());
  }

  // Strictly reducing optimizations
  @Override public Node ideal_reduce() {
    Node adr = adr();
    Type tadr = adr._val;
    // We allow Loads against Clazz types
    if( tadr instanceof TypeStruct ts ) {
      assert !ts.clz().isEmpty();
      return adr();
    }
    if( !(tadr instanceof TypeMemPtr tmp) ) return null;
    // If we can find an exact previous store, fold immediately to the value.
    Node ps = find_previous_struct(mem(),adr,tmp._aliases,true);
    if( ps!=null ) {
      if( ps instanceof StoreNode st ) return st.rez();
      if( ps instanceof StructNode st ) return st;
      throw unimpl();
    }
    return null;
  }


  // Changing edges to bypass, but typically not removing nodes nor edges
  @Override public Node ideal_mono() {
    Node mem = mem();
    // Bypass unrelated Stores, but only if the Address predates the Store.  If
    // the Load address depends on the Store memory, then the Load cannot
    // bypass the Store.
    if( mem instanceof StoreNode ) {
      throw unimpl();
    //  StoreNode st2 = (StoreNode)mem;
    //  if( st2.adr()==adr() && !Util.eq(st2._fld,_fld) ) // Very weak "Address must predate" test
    //    return set_mem(st2.mem());
    }

    Node adr = adr();
    Type tadr = adr._val;
    BitsAlias aliases = tadr instanceof TypeMemPtr ? ((TypeMemPtr)tadr)._aliases : null;

    // Load can move past a Join if all aliases align.
    if( mem instanceof MemJoinNode && aliases != null ) {
    //  Node jmem = ((MemJoinNode)mem).can_bypass(aliases);
    //  if( jmem != null ) {
    //    jmem.xval();
    //    return set_mem(jmem);
    //  }
      throw unimpl();
    }

    // Load can move out of a Call, if the function has no Parm:mem - happens
    // for single target calls that do not (have not yet) inlined.
    if( mem instanceof MProjNode && mem.in(0) instanceof CallNode )
    //  return set_mem(((CallNode)mem.in(0)).mem());
      throw unimpl();

    // Load can bypass a New or Store if the address does not depend on the New/St.
    if( aliases != null && mem instanceof MProjNode ) {
    //  NewNode nnn = ((MrgProjNode)mem).nnn();
    //  // Bypass if aliases do not overlap
    //  if( !aliases.test_recur(nnn._alias) )
    //    return set_mem(mem.in(1));
    //  // Also bypass if address predates the allocation.  Here we just see that
    //  // the address comes from the function Parm, and the New is made in the
    //  // function.
    //  Node adr2 = adr instanceof CastNode ? adr.in(1) : adr;
    //  if( adr2 instanceof ParmNode )
    //    return set_mem(mem.in(1));
      throw unimpl();
    }

    return null;
  }

  @Override public Node ideal_grow() {
    Node mem = mem();
    Node adr = adr();
    // Load from a memory Phi; split through in an effort to sharpen the memory.
    // TODO: Only split thru function args if no unknown_callers, and must make a Parm not a Phi
    // TODO: Hoist out of loops.
    if( mem!=null && mem._op == OP_PHI && adr.in(0) instanceof NewNode ) {
    //  Node lphi = new PhiNode(Type.SCALAR,((PhiNode)mem)._badgc,mem.in(0));
    //  for( int i=1; i<mem._defs._len; i++ )
    //    lphi.add_def(Env.GVN.add_work_new(new LoadNode(mem.in(i),adr,_fld,_bad)));
    //  return lphi;
      throw unimpl();
    }

    return null;
  }

  // Find a matching prior Store - matching address.
  // Returns null if highest available memory does not match address.
  static Node find_previous_struct(Node mem, Node adr, BitsAlias aliases, boolean is_load ) {
    if( mem==null ) return null;
    Type tmem = mem._val;
    if( !(tmem instanceof TypeMem) || aliases==null ) return null;
    // Walk up the memory chain looking for an exact matching Store or New
    int cnt=0;
    while(true) {
      cnt++; assert cnt < 100; // Infinite loop?
      if( mem instanceof StoreNode st ) {
        if( st.adr()==adr ) return st.err(true)== null ? st : null; // Exact matching store
        //  // Wrong address.  Look for no-overlap in aliases
        //  Type tst = st.adr()._val;
        //  if( !(tst instanceof TypeMemPtr) ) return null; // Store has weird address
        //  BitsAlias st_alias = ((TypeMemPtr)tst)._aliases;
        //  if( aliases.join(st_alias) != BitsAlias.EMPTY )
        //    return null;        // Aliases not disjoint, might overlap but wrong address
        //if( mem == st.mem() ) return null;
        //mem = st.mem(); // Advance past
        throw unimpl();

      //} else if( mem instanceof MemPrimNode.LValueWrite ) {
      //  // Array stores and field loads never alias
      //  mem = ((MemPrimNode)mem).mem();

      } else if( mem instanceof MProjNode ) {
        Node mem0 = mem.in(0);
        if( mem0 instanceof NewNode nnn ) {
          if( adr.in(0)==nnn ) return nnn.rec();
          if( aliases.test_recur(nnn._alias) ) return null; // Overlapping, but wrong address - dunno, so must fail
          mem = nnn.mem(); // Advance past
        } else if( mem0 instanceof CallEpiNode ) { // Bypass an entire function call
          if( ((CallEpiNode)mem0)._is_copy ) return null;
          Type tmem0 = mem._val;
          Type tmem1 = ((CallEpiNode)mem0).call().mem()._val;
          if( !(tmem0 instanceof TypeMem) || !(tmem1 instanceof TypeMem) ) return null;
          mem = _find_previous_store_call(aliases,(TypeMem)tmem0,(TypeMem)tmem1,(CallEpiNode)mem0,is_load);
          if( mem==null ) return null;
        } else if( mem0 instanceof MemSplitNode ) { // Lifting out of a split/join region
          mem = ((MemSplitNode)mem0).mem();
        } else if( mem0 instanceof CallNode ) { // Lifting out of a Call
          mem = ((CallNode)mem0).mem();
        } else {
          throw unimpl(); // decide cannot be equal, and advance, or maybe-equal and return null
        }
      //} else if( mem instanceof MemJoinNode ) {
      //  Node jmem = ((MemJoinNode)mem).can_bypass(aliases);
      //  if( jmem == null ) return null;
      //  mem = jmem;
      //} else if( mem instanceof ParmNode ) {
      //  if( mem.in(0) instanceof FunNode && mem.in(0).is_copy(1)!=null ) mem = mem.in(1); // FunNode is dying, copy, so ParmNode is also
      //  else return null;
      //
      //} else if( mem instanceof PhiNode || // Would have to match on both sides, and Phi the results
      //           mem instanceof StartMemNode ||
      //           mem instanceof ConNode) {
      //  return null;
      } else {
        throw unimpl(); // decide cannot be equal, and advance, or maybe-equal and return null
      }
    }
  }

  // Can bypass call?  Return null if cannot or call.mem if can.
  static private Node _find_previous_store_call( BitsAlias aliases, TypeMem tmem0, TypeMem tmem1, CallEpiNode cepi, boolean is_load ) {
    // TODO: Strengthen this.  Global no-esc can bypass, IF during inline/clone
    // each clone body updates both aliases everywhere.
    if( !is_load ) return null; // For now, Store types NEVER bypass a call.
    //CallNode call = cepi.call();
    //if( tmem0.fld_not_mod(aliases, fld) && tmem1.fld_not_mod(aliases, fld) )
    //  return call.mem(); // Loads from final memory can bypass calls.  Stores cannot, store-over-final is in error.
    //TypeMemPtr escs = CallNode.tesc(call._val);
    //if( escs._aliases.join(aliases)==BitsAlias.EMPTY )
    //  return call.mem(); // Load from call; if memory is made *in* the call this will fail later on an address mismatch.
    return null;         // Stuck behind call
  }

  @Override public ErrMsg err( boolean fast ) {
    Type tadr = adr()._val;
    if( tadr.must_nil() ) return fast ? ErrMsg.FAST : ErrMsg.niladr(_bad,"Struct might be nil when reading",null);
    if( tadr==Type.ANY ) return null; // No error, since might fall to any valid thing
    if( !(tadr instanceof TypeMemPtr ptr) )
      return bad(fast,null); // Not a pointer nor memory, cannot load a field
    if( ptr.is_valtype() )   // These should always fold
      return bad(fast,ptr._obj);
    Type tmem = mem()._val;
    if( tmem==Type.ALL ) return bad(fast,null);
    return null;
  }
  private ErrMsg bad( boolean fast, TypeStruct to ) {
    //boolean is_closure = adr() instanceof NewNode nnn && nnn._is_closure;
    //return fast ? ErrMsg.FAST : ErrMsg.field(_bad,"Unknown",_fld,is_closure,to);
    throw unimpl();
  }
}
