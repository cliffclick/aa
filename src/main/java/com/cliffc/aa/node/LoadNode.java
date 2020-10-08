package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;

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
  String xstr() { return "."+_fld; }   // Self short name
  String  str() { return xstr(); } // Inline short name
  private Node mem() { return in(1); }
          Node adr() { return in(2); }
  private Node set_mem(Node a, GVNGCM gvn) { return set_def(1,a,gvn); }
  public int find(TypeStruct ts) { return ts.find(_fld); }

  @Override public Node ideal(GVNGCM gvn, int level) {
    Node mem  = mem();
    Node adr = adr();

    Type tadr = adr._val;
    BitsAlias aliases = tadr instanceof TypeMemPtr ? ((TypeMemPtr)tadr)._aliases : null;

    // If we can find an exact previous store, fold immediately to the value.
    // Do not move Loads "up" past unrelated stores, lest we make memory alive twice.
    Node st = find_previous_store(gvn,mem(),adr(),aliases,_fld,true);
    if( st!=null ) {
      if( st instanceof StoreNode ) return (( StoreNode)st).val();
      else                          return ((NewObjNode)st).get(_fld);
    }

    // Load can move past a Join if all aliases align.
    if( mem instanceof MemJoinNode && aliases != null ) {
      Node jmem = ((MemJoinNode)mem).can_bypass(aliases);
      if( jmem != null ) {
        jmem.xval(gvn._opt_mode);
        set_mem(jmem,gvn);
        return this;
      }
    }

    // Load can move out of a Call, if the function has no Parm:mem - happens
    // for single target calls that do not (have not yet) inlined.
    if( mem instanceof MProjNode && mem.in(0) instanceof CallNode )
      return set_mem(((CallNode)mem.in(0)).mem(),gvn);

    // Load can bypass a New or Store if the address does not depend on the New/St.
    if( aliases != null && mem instanceof MrgProjNode ) {
      NewNode nnn = ((MrgProjNode)mem).nnn();
      // Bypass if aliases do not overlap
      if( !aliases.test_recur(nnn._alias) )
        return set_mem(mem.in(1),gvn);
      // Also bypass if address predates the allocation.  Here we just see that
      // the address comes from the function Parm, and the New is made in the
      // function.
      Node adr2 = adr instanceof CastNode ? adr.in(1) : adr;
      if( adr2 instanceof ParmNode )
        return set_mem(mem.in(1),gvn);
    }

    // Load from a memory Phi; split through in an effort to sharpen the memory.
    // TODO: Only split thru function args if no unknown_callers, and must make a Parm not a Phi
    // TODO: Hoist out of loops.
    if( mem._op == OP_PHI && mem.in(0)._op != OP_LOOP && adr.in(0) instanceof NewNode ) {
      Node lphi = new PhiNode(Type.SCALAR,((PhiNode)mem)._badgc,mem.in(0));
      for( int i=1; i<mem._defs._len; i++ )
        lphi.add_def(gvn.xform(new LoadNode(mem.in(i),adr,_fld,_bad)));
      return lphi;
    }

    return null;
  }

  // Find a matching prior Store or NewObj - matching field name and address.
  // Returns null if highest available memory does not match name & address.
  static Node find_previous_store(GVNGCM gvn, Node mem, Node adr, BitsAlias aliases, String fld, boolean is_load ) {
    Type tmem0 = mem._val;
    if( !(tmem0 instanceof TypeMem) || aliases==null ) return null;
    TypeMem tmem = (TypeMem)tmem0;
    // Walk up the memory chain looking for an exact matching Store or New
    int cnt=0;
    while(true) {
      assert cnt++ < 100; // Infinite loop?
      if( mem instanceof StoreNode ) {
        StoreNode st = (StoreNode)mem;
        if( Util.eq(st._fld,fld) ) {
          if( st.adr()==adr ) return st.err(true)== null ? st : null; // Exact matching store
          // Matching field, wrong address.  Look for no-overlap in aliases
          Type tst = st.adr()._val;
          if( !(tst instanceof TypeMemPtr) ) return null; // Store has weird address
          BitsAlias st_alias = ((TypeMemPtr)tst)._aliases;
          if( aliases.join(st_alias) != BitsAlias.EMPTY )
            return null;        // Aliases not disjoint, might overlap but wrong address
        }               // Wrong field name, cannot match
        mem = st.mem(); // Advance past

      } else if( mem instanceof MProjNode ) {
        Node mem0 = mem.in(0);
        if( mem0 instanceof CallEpiNode ) { // Bypass an entire function call
          mem = _find_previous_store_call(gvn,aliases,tmem,(CallEpiNode)mem0,fld,is_load);
          if( mem==null ) return null;
        } else if( mem0 instanceof MemSplitNode ) { // Lifting out of a split/join region
          mem = ((MemSplitNode)mem0).mem();
        } else if( mem0 instanceof CallNode ) { // Lifting out of a Call
          mem = ((CallNode)mem0).mem();
        } else {
          throw com.cliffc.aa.AA.unimpl(); // decide cannot be equal, and advance, or maybe-equal andreturn null
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
        throw com.cliffc.aa.AA.unimpl(); // decide cannot be equal, and advance, or maybe-equal andreturn null
      }
    }
  }

  // Can bypass call?  Return null if cannot or call.mem if can.
  static private Node _find_previous_store_call(GVNGCM gvn, BitsAlias aliases, TypeMem tmem, CallEpiNode cepi, String fld, boolean is_load) {
    // TODO: Strengthen this.  Global no-esc can bypass, IF during inline/clone
    // each clone body updates both aliases everywhere.
    if( !is_load ) return null; // For now, Store types NEVER bypass a call.
    CallNode call = cepi.call();
    if( tmem.fld_is_final(aliases,fld) )
      return call.mem(); // Loads from final memory can bypass calls.  Stores cannot, store-over-final is in error.
    TypeMemPtr escs = call.tesc(call._val);
    if( escs._aliases.join(aliases)==BitsAlias.EMPTY )
      return call.mem(); // Load from call; if memory is made *in* the call this will fail later on an address mismatch.
    return null;         // Stuck behind call
  }


  @Override public Type value(GVNGCM.Mode opt_mode) {
    Node adr = adr();
    Type tadr = adr._val;
    if( !(tadr instanceof TypeMemPtr) ) return tadr.oob();
    TypeMemPtr tmp = (TypeMemPtr)tadr;

    // Loading from TypeMem - will get a TypeObj out.
    Node mem = mem();
    Type tmem = mem._val; // Memory
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
    Type tmem = mem()._val;
    Type tptr = adr()._val;
    if( !(tmem instanceof TypeMem   ) ) return tmem.oob(TypeMem.ALLMEM); // Not a memory?
    if( !(tptr instanceof TypeMemPtr) ) return tptr.oob(TypeMem.ALLMEM); // Not a pointer?
    if( tptr.above_center() ) return TypeMem.ANYMEM; // Loaded from nothing
    return ((TypeMem)tmem).remove_no_escapes(((TypeMemPtr)tptr)._aliases);
  }

  @Override public ErrMsg err( boolean fast ) {
    Type tadr = adr()._val;
    if( tadr.must_nil() ) return fast ? ErrMsg.FAST : ErrMsg.niladr(_bad,"Struct might be nil when reading",_fld);
    if( !(tadr instanceof TypeMemPtr) )
      return bad(fast); // Not a pointer nor memory, cannot load a field
    TypeMemPtr ptr = (TypeMemPtr)tadr;
    Type tmem = mem()._val;
    if( tmem==Type.ALL ) return bad(fast);
    if( tmem==Type.ANY ) return null; // No error
    TypeObj objs = tmem instanceof TypeMem
      ? ((TypeMem)tmem).ld(ptr) // General load from memory
      : ((TypeObj)tmem);
    if( !(objs instanceof TypeStruct) || find((TypeStruct)objs) == -1 )
      return bad(fast);
    return null;
  }
  private ErrMsg bad( boolean fast ) {
    boolean is_closure = adr() instanceof ProjNode && adr().in(0) instanceof NewObjNode && ((NewObjNode)adr().in(0))._is_closure;
    return fast ? ErrMsg.FAST : ErrMsg.field(_bad,"Unknown",_fld,is_closure,adr()._val);
  }
  @Override public int hashCode() { return super.hashCode()+_fld.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    return (o instanceof LoadNode) && Util.eq(_fld,((LoadNode)o)._fld);
  }
}
