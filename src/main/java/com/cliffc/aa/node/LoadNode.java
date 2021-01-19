package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.util.Util;

import static com.cliffc.aa.AA.MEM_IDX;

// Load a named field from a struct.  Does it's own nil-check testing.  Loaded
// value depends on the struct typing.
public class LoadNode extends Node {
  private final String _fld;
  private final Parse _bad;

  public LoadNode( Node mem, Node adr, String fld, Parse bad ) { this(mem,adr,fld,bad,false,false); }
  public LoadNode( Node mem, Node adr, String fld, Parse bad, boolean closure_adr, boolean closure_val ) {
    super(OP_LOAD,null,mem,adr);
    _fld = fld;
    _bad = bad;
    // TRUE if either the address or value must be a TFP.
    // Address: means loading from a closure.
    // Value  : means loading      a closure.
    // Both: this is a linked-list display walk, finding the closure at the proper lexical depth.
    // Just address: this is loading a local variable at this closure.
    // Neither: this is a normal field load from a non-closure structure.
    // Just value: not allowed.
    assert (closure_adr || !closure_val); // Just value: not allowed
  }
  @Override public String xstr() { return "."+_fld; }   // Self short name
  String  str() { return xstr(); } // Inline short name
  Node mem() { return in(MEM_IDX); }
  Node adr() { return in(2); }
  private Node set_mem(Node a) { return set_def(1,a); }
  public int find(TypeStruct ts) { return ts.find(_fld); }

  @Override public Node ideal(GVNGCM gvn, int level) { throw com.cliffc.aa.AA.unimpl(); }

  // Strictly reducing optimizations
  @Override public Node ideal_reduce() {
    Node mem  = mem();
    Node adr = adr();
    Type tadr = adr.val();
    BitsAlias aliases = tadr instanceof TypeMemPtr ? ((TypeMemPtr)tadr)._aliases : null;

    // If we can find an exact previous store, fold immediately to the value.
    Node st = find_previous_store(mem(),adr(),aliases,_fld,true);
    if( st!=null ) {
      if( st instanceof StoreNode ) return (( StoreNode)st).rez();
      else                          return ((NewObjNode)st).get(_fld);
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
      StoreNode st2 = (StoreNode)mem;
      if( st2.adr()==adr() && !Util.eq(st2._fld,_fld) ) // Very weak "Address must predate" test
        return set_mem(st2.mem());
    }

    Node adr = adr();
    Type tadr = adr.val();
    BitsAlias aliases = tadr instanceof TypeMemPtr ? ((TypeMemPtr)tadr)._aliases : null;

    // Load can move past a Join if all aliases align.
    if( mem instanceof MemJoinNode && aliases != null ) {
      Node jmem = ((MemJoinNode)mem).can_bypass(aliases);
      if( jmem != null ) {
        jmem.xval();
        return set_mem(jmem);
      }
    }

    // Load can move out of a Call, if the function has no Parm:mem - happens
    // for single target calls that do not (have not yet) inlined.
    if( mem instanceof MProjNode && mem.in(0) instanceof CallNode )
      return set_mem(((CallNode)mem.in(0)).mem());

    // Load can bypass a New or Store if the address does not depend on the New/St.
    if( aliases != null && mem instanceof MrgProjNode ) {
      NewNode nnn = ((MrgProjNode)mem).nnn();
      // Bypass if aliases do not overlap
      if( !aliases.test_recur(nnn._alias) )
        return set_mem(mem.in(1));
      // Also bypass if address predates the allocation.  Here we just see that
      // the address comes from the function Parm, and the New is made in the
      // function.
      Node adr2 = adr instanceof CastNode ? adr.in(1) : adr;
      if( adr2 instanceof ParmNode )
        return set_mem(mem.in(1));
    }

    return null;
  }

  @Override public Node ideal_grow() {
    Node mem = mem();
    Node adr = adr();
    // Load from a memory Phi; split through in an effort to sharpen the memory.
    // TODO: Only split thru function args if no unknown_callers, and must make a Parm not a Phi
    // TODO: Hoist out of loops.
    if( mem._op == OP_PHI && mem.in(0)._op != OP_LOOP && adr.in(0) instanceof NewNode ) {
      Node lphi = new PhiNode(Type.SCALAR,((PhiNode)mem)._badgc,mem.in(0));
      for( int i=1; i<mem._defs._len; i++ )
        lphi.add_def(Env.GVN.xform(new LoadNode(mem.in(i),adr,_fld,_bad)));
      return lphi;
    }

    return null;
  }

  // Find a matching prior Store or NewObj - matching field name and address.
  // Returns null if highest available memory does not match name & address.
  static Node find_previous_store(Node mem, Node adr, BitsAlias aliases, String fld, boolean is_load ) {
    Type tmem = mem.val();
    if( !(tmem instanceof TypeMem) || aliases==null ) return null;
    // Walk up the memory chain looking for an exact matching Store or New
    int cnt=0;
    while(true) {
      cnt++; assert cnt < 100; // Infinite loop?
      if( mem instanceof StoreNode ) {
        StoreNode st = (StoreNode)mem;
        if( Util.eq(st._fld,fld) ) {
          if( st.adr()==adr ) return st.err(true)== null ? st : null; // Exact matching store
          // Matching field, wrong address.  Look for no-overlap in aliases
          Type tst = st.adr().val();
          if( !(tst instanceof TypeMemPtr) ) return null; // Store has weird address
          BitsAlias st_alias = ((TypeMemPtr)tst)._aliases;
          if( aliases.join(st_alias) != BitsAlias.EMPTY )
            return null;        // Aliases not disjoint, might overlap but wrong address
        }               // Wrong field name, cannot match
        mem = st.mem(); // Advance past

      } else if( mem instanceof MemPrimNode.LValueWrite ) {
        // Array stores and field loads never alias
        mem = ((MemPrimNode)mem).mem();

      } else if( mem instanceof MProjNode ) {
        Node mem0 = mem.in(0);
        if( mem0 instanceof CallEpiNode ) { // Bypass an entire function call
          if( ((CallEpiNode)mem0)._is_copy ) return null;
          Type tmem0 = mem.val();
          Type tmem1 = ((CallEpiNode)mem0).call().mem().val();
          if( !(tmem0 instanceof TypeMem) || !(tmem1 instanceof TypeMem) ) return null;
          mem = _find_previous_store_call(aliases,(TypeMem)tmem0,(TypeMem)tmem1,(CallEpiNode)mem0,fld,is_load);
          if( mem==null ) return null;
        } else if( mem0 instanceof MemSplitNode ) { // Lifting out of a split/join region
          mem = ((MemSplitNode)mem0).mem();
        } else if( mem0 instanceof CallNode ) { // Lifting out of a Call
          mem = ((CallNode)mem0).mem();
        } else {
          throw com.cliffc.aa.AA.unimpl(); // decide cannot be equal, and advance, or maybe-equal and return null
        }
      } else if( mem instanceof MrgProjNode ) {
        MrgProjNode mrg = (MrgProjNode)mem;
        NewNode nnn = mrg.nnn();
        if( nnn instanceof NewObjNode ) {
          int idx = ((NewObjNode)nnn)._ts.find(fld);
          if( idx >= 0 && adr instanceof ProjNode && adr.in(0) == nnn ) return nnn; // Direct hit
        }  // wrong field name or wrong alias, cannot match
        if( aliases.test_recur(nnn._alias) ) return null; // Overlapping, but wrong address - dunno, so must fail
        mem = mrg.mem(); // Advance past
      } else if( mem instanceof MemJoinNode ) {
        Node jmem = ((MemJoinNode)mem).can_bypass(aliases);
        if( jmem == null ) return null;
        mem = jmem;

      } else if( mem instanceof PhiNode ||
                 mem instanceof StartMemNode ||
                 mem instanceof ConNode) {
        return null;            // Would have to match on both sides, and Phi the results
      } else {
        throw com.cliffc.aa.AA.unimpl(); // decide cannot be equal, and advance, or maybe-equal and return null
      }
    }
  }

  // Can bypass call?  Return null if cannot or call.mem if can.
  static private Node _find_previous_store_call( BitsAlias aliases, TypeMem tmem0, TypeMem tmem1, CallEpiNode cepi, String fld, boolean is_load ) {
    // TODO: Strengthen this.  Global no-esc can bypass, IF during inline/clone
    // each clone body updates both aliases everywhere.
    if( !is_load ) return null; // For now, Store types NEVER bypass a call.
    CallNode call = cepi.call();
    if( !tmem0.fld_is_mod(aliases,fld) && !tmem1.fld_is_mod(aliases,fld) )
      return call.mem(); // Loads from final memory can bypass calls.  Stores cannot, store-over-final is in error.
    TypeMemPtr escs = call.tesc(call.val());
    if( escs._aliases.join(aliases)==BitsAlias.EMPTY )
      return call.mem(); // Load from call; if memory is made *in* the call this will fail later on an address mismatch.
    return null;         // Stuck behind call
  }


  @Override public Type value(GVNGCM.Mode opt_mode) {
    Node adr = adr();
    Type tadr = adr.val();
    if( !(tadr instanceof TypeMemPtr) ) return tadr.oob();
    TypeMemPtr tmp = (TypeMemPtr)tadr;

    // Loading from TypeMem - will get a TypeObj out.
    Node mem = mem();
    Type tmem = mem.val(); // Memory
    if( !(tmem instanceof TypeMem) ) return tmem.oob(); // Nothing sane
    TypeObj tobj = ((TypeMem)tmem).ld(tmp);

    // Loading from TypeObj - hoping to get a field out.
    if( tobj instanceof TypeStruct ) { // Struct; check for field
      TypeStruct ts = (TypeStruct)tobj;
      int idx = ts.find(_fld);  // Find the named field
      if( idx != -1 ) return ts.at(idx);  // Field type
      // No such field
    }
    return tobj.oob();          // No loading from e.g. Strings
  }

  // The only memory required here is what is needed to support the Load
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    if( def==adr() ) return TypeMem.ALIVE;
    Type tmem = mem().val();
    Type tptr = adr().val();
    if( !(tmem instanceof TypeMem   ) ) return tmem.oob(TypeMem.ALLMEM); // Not a memory?
    if( !(tptr instanceof TypeMemPtr) ) return tptr.oob(TypeMem.ALLMEM); // Not a pointer?
    if( tptr.above_center() ) return TypeMem.ANYMEM; // Loaded from nothing
    // Only named the named field from the named aliases is live.
    return ((TypeMem)tmem).remove_no_escapes(((TypeMemPtr)tptr)._aliases,_fld);
  }

  @Override public boolean unify( boolean test ) {
    // Input should be a TMem
    Node mem = mem();
    TVar tvmem = mem.tvar();
    if( tvmem instanceof TVDead ) return false; // Not gonna be a TMem
    // Address needs to name the aliases
    Type tadr = adr().val();
    if( !(tadr instanceof TypeMemPtr) )
      return false;             // Wait until types are sharper
    TypeMemPtr tmp = (TypeMemPtr)tadr;
    if( !(tvmem instanceof TMem) )     // One-time make a TMem
      return tvmem.unify(new TMem(mem),test);
    // Unify the given aliases and field against the loaded type
    return ((TMem)tvmem).unify_alias_load(tmp._aliases,_fld,tvar(),mem,test);
  }

  @Override public ErrMsg err( boolean fast ) {
    Type tadr = adr().val();
    if( tadr.must_nil() ) return fast ? ErrMsg.FAST : ErrMsg.niladr(_bad,"Struct might be nil when reading",_fld);
    if( !(tadr instanceof TypeMemPtr) )
      return bad(fast,null); // Not a pointer nor memory, cannot load a field
    TypeMemPtr ptr = (TypeMemPtr)tadr;
    Type tmem = mem().val();
    if( tmem==Type.ALL ) return bad(fast,null);
    if( tmem==Type.ANY ) return null; // No error
    TypeObj objs = tmem instanceof TypeMem
      ? ((TypeMem)tmem).ld(ptr) // General load from memory
      : ((TypeObj)tmem);
    if( !(objs instanceof TypeStruct) || find((TypeStruct)objs) == -1 )
      return bad(fast,objs);
    return null;
  }
  private ErrMsg bad( boolean fast, TypeObj to ) {
    boolean is_closure = adr() instanceof ProjNode && adr().in(0) instanceof NewObjNode && ((NewObjNode)adr().in(0))._is_closure;
    return fast ? ErrMsg.FAST : ErrMsg.field(_bad,"Unknown",_fld,is_closure,to);
  }
  @Override public int hashCode() { return super.hashCode()+_fld.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    return (o instanceof LoadNode) && Util.eq(_fld,((LoadNode)o)._fld);
  }

}
