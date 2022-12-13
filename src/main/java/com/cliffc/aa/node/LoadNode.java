package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV3;
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
    if( !(mem instanceof TypeMem tmem) ) return mem.oob(); // Not a memory?
    if( ptr instanceof TypeStruct ) return ptr.oob(TypeMem.ALLMEM); // Loading from a clazz
    if( !(ptr instanceof TypeMemPtr tptr) ) return ptr.oob(); // Not a pointer?
    if( tptr.above_center() ) return TypeMem.ANYMEM; // Loaded from nothing
    // Only the named aliases is live.
    return tmem.remove_no_escapes(tptr._aliases);
  }

  @Override public boolean has_tvar() { return true; }

  // Standard memory unification; the Load unifies with the loaded field.
  @Override public boolean unify( boolean test ) {
    TV3 self = tvar();
    TV3 ptr = adr().tvar();
    //assert !ptr.is_obj() && !self.is_nil() && self.arg("*")==null;
    //if( ptr.is_nil() )
    //  throw unimpl();
    //TV3 rec = ptr.arg("*");
    //if( rec==null )
    //  ptr.add_fld("*",rec = TV3.make_leaf("Load_unify"));
    //return self.unify(rec,test);
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
      Node rez = switch(ps) {
      case StoreNode st -> st.rez();
      case StructNode st -> st;
      default -> throw unimpl();
      };
      if( !_live.isa(rez._live) ) return null; // Stall until liveness matches
      return rez;
    }
    return null;
  }


  // Changing edges to bypass, but typically not removing nodes nor edges
  @Override public Node ideal_mono() {
    Node mem = mem();
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
    if( mem instanceof MProjNode mprj && mem.in(0) instanceof NewNode nnn && aliases != null ) {
      // Bypass if aliases do not overlap
      if( !aliases.test_recur(nnn._alias) )
        return set_mem(nnn.mem());
      // Also bypass if address predates the allocation.  Here we just see that
      // the address comes from the function Parm, and the New is made in the
      // function.
      Node adr2 = adr instanceof CastNode ? adr.in(1) : adr;
      if( adr2 instanceof ParmNode )
        //return set_mem(mem.in(1));
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
      Node lphi = new PhiNode(TypeNil.SCALAR,((PhiNode)mem)._badgc,mem.in(0));
      for( int i=1; i<mem._defs._len; i++ )
        lphi.add_def(Env.GVN.add_work_new(new LoadNode(mem.in(i),adr,_bad)));
      subsume(lphi);
      return lphi;
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
        // Wrong address.  Look for no-overlap in aliases
        Type tst = st.adr()._val;
        if( !(tst instanceof TypeMemPtr tmp) ) return null; // Store has weird address
        BitsAlias st_alias = tmp._aliases;
          if( aliases.join(st_alias) != BitsAlias.EMPTY )
            return null;        // Aliases not disjoint, might overlap but wrong address
        if( mem == st.mem() ) return null;
        mem = st.mem(); // Advance past

      //} else if( mem instanceof MemPrimNode.LValueWrite ) {
      //  // Array stores and field loads never alias
      //  mem = ((MemPrimNode)mem).mem();

      } else if( mem instanceof MProjNode ) {
        Node mem0 = mem.in(0);
        switch( mem0 ) {
        case NewNode nnn -> {
          if( adr.in(0) == nnn ) return nnn.rec();
          if( aliases.test_recur(nnn._alias) ) return null; // Overlapping, but wrong address - dunno, so must fail
          mem = nnn.mem(); // Advance past
        }
        case CallEpiNode  node -> { return null; } // TODO: Bypass entire function call
        case MemSplitNode node -> mem = node.mem(); // Lifting out of a split/join region
        case CallNode     node -> mem = node.mem(); // Lifting out of a Call

        case null, default -> throw unimpl(); // decide cannot be equal, and advance, or maybe-equal and return null
        }
      //} else if( mem instanceof MemJoinNode ) {
      //  Node jmem = ((MemJoinNode)mem).can_bypass(aliases);
      //  if( jmem == null ) return null;
      //  mem = jmem;
      //} else if( mem instanceof ParmNode ) {
      //  if( mem.in(0) instanceof FunNode && mem.in(0).is_copy(1)!=null ) mem = mem.in(1); // FunNode is dying, copy, so ParmNode is also
      //  else return null;
      //
      } else if( mem instanceof PhiNode || // Would have to match on both sides, and Phi the results'
                 mem instanceof ConNode) {
        return null;
      } else {
        throw unimpl(); // decide cannot be equal, and advance, or maybe-equal and return null
      }
    }
  }
}
