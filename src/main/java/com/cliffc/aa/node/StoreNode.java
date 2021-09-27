package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.NonBlockingHashMap;
import com.cliffc.aa.util.Util;

import static com.cliffc.aa.AA.unimpl;
import static com.cliffc.aa.type.TypeFld.Access;

// Store a value into a named struct field.  Does it's own nil-check and value
// testing; also checks final field updates.
public class StoreNode extends Node {
  final String _fld;        // Field being updated
  private final Access _fin; // TypeFld.Access.Final or TypeFld.Access.RW
  private final Parse _bad;
  public StoreNode( Node mem, Node adr, Node val, Access fin, String fld, Parse bad ) {
    super(OP_STORE,null,mem,adr,val);
    _fld = fld;
    _fin = fin;
    _bad = bad;    // Tests can pass a null, but nobody else does
  }
  private StoreNode( StoreNode st, Node mem, Node adr ) { this(mem,adr,st.rez(),st._fin,st._fld,st._bad); }

  @Override public String xstr() { return "."+_fld+"="; } // Self short name
  String  str() { return xstr(); }   // Inline short name
  @Override public boolean is_mem() { return true; }

  Node mem() { return in(1); }
  Node adr() { return in(2); }
  Node rez() { return in(3); }
  public TypeFld find(TypeStruct ts) { return ts.fld_find(_fld); }

  @Override public Node ideal_reduce() {
    Node mem = mem();
    Node adr = adr();
    Type ta = adr._val;
    TypeMemPtr tmp = ta instanceof TypeMemPtr ? (TypeMemPtr)ta : null;

    // Is this Store dead from below?
    if( mem==this ) return null;
    if( ta.above_center() ) return mem;
    if( tmp!=null && _live.ld(tmp)==TypeObj.UNUSED )  return mem;

    // If Store is by a New and no other Stores, fold into the New.
    NewObjNode nnn;  TypeFld tfld;
    if( mem instanceof MrgProjNode && mem._keep==0 &&
        _keep <= 1 &&
        mem.in(0) instanceof NewObjNode && (nnn=(NewObjNode)mem.in(0)) == adr.in(0) &&
        !rez().is_forward_ref() &&
        mem._uses._len==2 && // Use is by DefMem and self
        (tfld=nnn._ts.fld_find(_fld))!= null ) {
      // Have to be allowed to directly update NewObjNode
      if( tfld._access==Access.RW || rez() instanceof FunPtrNode ) {
        // Field is modifiable; update New directly.
        if( tfld._access==Access.RW ) nnn.update(_fld,_fin,rez()); // Update the value, and perhaps the final field
        else                          nnn.add_fun(_bad,_fld,(FunPtrNode)rez()); // Stacked FunPtrs into an Unresolved
        mem.xval();             // Update memory state
        Env.DEFMEM.xval();      // Update default memory state
        Env.GVN.add_flow_uses(this);
        add_reduce_extra();     // Folding in allows store followers to fold in
        return mem;             // Store is replaced by using the New directly.
      }
    }

    // If Store is of a MemJoin and it can enter the split region, do so.
    // Requires no other memory *reader* (or writer), as the reader will
    // now see the Store effects as part of the Join.
    if( _keep<=1 && tmp != null && mem._keep==0 && mem instanceof MemJoinNode && mem._uses._len==1 ) {
      Node memw = _uses._len==0 ? this : get_mem_writer(); // Zero or 1 mem-writer
      // Check the address does not have a memory dependence on the Join.
      // TODO: This is super conservative
      if( adr instanceof FreshNode ) adr = ((FreshNode)adr).id();
      if( memw != null && adr instanceof ProjNode && adr.in(0) instanceof NewNode )
        return ((MemJoinNode)mem).add_alias_below_new(new StoreNode(this,mem,adr()),this);
    }

    return null;
  }
  @Override public Node ideal_mono() { return null; }
  @Override public Node ideal_grow() {
    Node mem = mem();
    Node adr = adr();
    Type ta = adr._val;
    TypeMemPtr tmp = ta instanceof TypeMemPtr ? (TypeMemPtr)ta : null;

    // If Store is of a memory-writer, and the aliases do not overlap, make parallel with a Join
    if( tmp != null && (tmp._aliases!=BitsAlias.NIL.dual()) &&
        mem.is_mem() && mem.check_solo_mem_writer(this) ) {
      Node head2;
      if( mem instanceof StoreNode ) head2=mem;
      else if( mem instanceof MrgProjNode && ((MrgProjNode)mem).mem()!=this ) head2=mem;
      else if( mem instanceof MProjNode && mem.in(0) instanceof CallEpiNode ) head2 = mem.in(0).in(0);
      else head2 = null;
      // Check no extra readers/writers at the split point
      if( head2 != null && MemSplitNode.check_split(this,escapees(),mem) ) {
        MemSplitNode.insert_split(this, escapees(), this, mem, head2);
        assert _uses._len==1 && _uses.at(0) instanceof MemJoinNode;
        return _uses.at(0); // Return the mem join
      }
    }
    return null;
  }
  // Liveness changes, check if reduce
  @Override public void add_work_extra(Work work,Type old) {
    Env.GVN.add_reduce(this); // Args can be more-alive
  }
  // If changing an input or value allows the store to no longer be in-error,
  // following Loads can collapse
  @Override public void add_reduce_extra() {
    for( Node use : _uses )
      if( use instanceof LoadNode )
        Env.GVN.add_mono(Env.GVN.add_reduce(use));
  }

  // StoreNode needs to return a TypeObj for the Parser.
  @Override public Type value(GVNGCM.Mode opt_mode) {
    Node mem = mem(), adr = adr(), rez = rez();
    Type tmem = mem._val;
    Type tadr = adr._val;
    Type tval = rez._val;  // Value
    if( tmem==Type.ALL || tadr==Type.ALL ) return Type.ALL;

    if( !(tmem instanceof TypeMem   ) ) return tmem.oob(TypeMem.ALLMEM);
    if( !(tadr instanceof TypeMemPtr) ) return tadr.above_center() ? tmem : TypeMem.ALLMEM;
    TypeMem    tm  = (TypeMem   )tmem;
    TypeMemPtr tmp = (TypeMemPtr)tadr;
    return tm.update(tmp._aliases,_fin,_fld,tval);
  }
  @Override BitsAlias escapees() {
    Type adr = adr()._val;
    if( !(adr instanceof TypeMemPtr) ) return adr.above_center() ? BitsAlias.EMPTY : BitsAlias.FULL;
    return ((TypeMemPtr)adr)._aliases;
  }

  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
  // Compute the liveness local contribution to def's liveness.  Ignores the
  // incoming memory types, as this is a backwards propagation of demanded
  // memory.
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    if( def==mem() ) return _live; // Pass full liveness along
    if( def==adr() ) return TypeMem.ALIVE; // Basic aliveness
    if( def==rez() ) return TypeMem.ESCAPE;// Value escapes
    throw unimpl();       // Should not reach here
  }

  @Override public ErrMsg err( boolean fast ) {
    Type tadr = adr()._val;
    if( tadr.must_nil() ) return fast ? ErrMsg.FAST : ErrMsg.niladr(_bad,"Struct might be nil when writing",_fld);
    if( !(tadr instanceof TypeMemPtr) )
      return bad("Unknown",fast,null); // Not a pointer nor memory, cannot store a field
    TypeMemPtr ptr = (TypeMemPtr)tadr;
    Type tmem = mem()._val;
    if( tmem==Type.ALL ) return bad("Unknown",fast,null);
    if( tmem==Type.ANY ) return null; // No error
    TypeObj objs = tmem instanceof TypeMem
      ? ((TypeMem)tmem).ld(ptr) // General load from memory
      : ((TypeObj)tmem);
    if( !(objs instanceof TypeStruct) ) return bad("No such",fast,objs);
    TypeStruct ts = (TypeStruct)objs;
    TypeFld fld = ts.fld_find(_fld);
    if( fld==null ) return bad("No such",fast,objs);
    Access access = fld._access;
    if( access!=Access.RW )
      return bad("Cannot re-assign "+access,fast,ts);
    return null;
  }
  private ErrMsg bad( String msg, boolean fast, TypeObj to ) {
    if( fast ) return ErrMsg.FAST;
    boolean is_closure = adr() instanceof ProjNode && adr().in(0) instanceof NewObjNode && ((NewObjNode)adr().in(0))._is_closure;
    return ErrMsg.field(_bad,msg,_fld,is_closure,to);
  }
  @Override public int hashCode() { return super.hashCode()+_fld.hashCode()+_fin.hashCode(); }
  // Stores are can be CSE/equal, and we might force a partial execution to
  // become a total execution (require a store on some path it didn't happen).
  // This can be undone later with splitting.
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !(o instanceof StoreNode) || !super.equals(o) ) return false;
    StoreNode st = (StoreNode)o;
    return _fin==st._fin && Util.eq(_fld,st._fld);
  }

  @Override public boolean unify( Work work ) {
    return unify("@{}",this,adr().tvar(),adr()._val,rez(),_fld,work);
  }

  // Common memory-update unification.  Store unifies with the stored value.
  // The ptr has to be not-nilable and have the fld, which unifies with the
  // value.  If the fld is missing, then if the ptr is open, add the field else
  // missing field error.
  public static boolean unify( String name, Node st, TV2 ptr, Type tptr, Node val, String id, Work work ) {
    if( st.tvar().is_err() ) return false; // Already an error, no progress
    // Propagate an error
    if( ptr.is_err() ) return st.tvar().unify(ptr,work);

    // Check for nil address
    if( ptr.is_nil() || (tptr instanceof TypeMemPtr && tptr.must_nil()) )
      return work==null || st.tvar().unify(TV2.make_err(st,"May be nil when accessing field "+id,"Store_update"),work);

    // Store value is always the stored value
    boolean progress = st.tvar().unify(val.tvar(),work);
    ptr.push_dep(st);

    // Matching fields unify
    TV2 fld = ptr.get(id);
    if( fld!=null )             // Unify against pre-existing field
      return fld.unify(st.tvar(), work) | progress;

    // The remaining cases all make progress and return true
    if( work==null ) return true;

    // Add field if open
    if( ptr.is_struct() && ptr.open() ) // Effectively unify with an extended struct.
      return ptr.add_fld(id,st.tvar(),work);

    // Unify against an open struct with the named field
    if( ptr.is_leaf() || ptr.is_fun() ) {
      TV2 tv2 = TV2.make_open_struct(name,st,TypeMemPtr.make(BitsAlias.EMPTY,TypeStruct.make()),"Store_update", new NonBlockingHashMap<>());
      tv2.args_put(id,st.tvar());
      return tv2.unify(ptr,work);
    }

    // Closed record, field is missing
    return st.tvar().unify(ptr.miss_field(st,id,"Store_update"),work);
  }

}
