package com.cliffc.aa.node;

import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.unimpl;
import static com.cliffc.aa.type.TypeFld.Access;

// Store a value into a named struct field.  Does it's own nil-check and value
// testing; also checks final field updates.
public class StoreNode extends StoreAbs {
  final String _fld;
  final Access _fin;
  public StoreNode( Node mem, Node adr, Node val, String fld, Access fin, Parse bad ) {
    super(mem,adr,val,bad);
    _fld = fld;
    _fin = fin;
  }

  
  @Override Type _value( TypeMem tm, TypeMemPtr tmp ) {
    return tm.update(tmp,TypeFld.make(_fld,rez()._val,_fin));
  }

  @Override TypeMem _live_use( TypeMem live0, TypeMemPtr tmp ) {
    assert !tmp.above_center();
    // Not a precise store, so no kills
    if( !tmp.is_con() ) return live0;

    
    throw unimpl();
  }

//  // Compute the liveness local contribution to def's liveness.  Turns around
//  // value into live: if values are ANY then nothing is demand-able.
//  @Override public Type live_use( int i ) {
//    Node def = in(i);
//    // Liveness as a TypeMem
//    TypeMem live = _live== Type.ALL ? RootNode.def_mem(def) : (TypeMem)_live;
//    // Input memory as a TypeMem
//    Type mem0 = mem()._val;
//    TypeMem mem = mem0== Type.ANY ? TypeMem.ANYMEM
//      : (mem0== Type.ALL ? TypeMem.ALLMEM
//         : (TypeMem)mem0);
//    TypeMemPtr tmp = adr()._val instanceof TypeMemPtr tmp0 ? tmp0 : adr()._val.oob(TypeMemPtr.ISUSED);
//
//    // Liveness for memory?
//    if( i==MEM_IDX ) {
//      adr().deps_add(def);
//      // Assume all above center aliases kill everything (will optimistically
//      // kill what we need) to make uses go away
//      if( tmp._aliases.above_center() ) {
//        for( int alias : tmp._aliases )
//          live = live.set(alias,TypeStruct.UNUSED);
//        return live;
//      }
//      mem().deps_add(def);
//      // Precise update if it's a single alias, and no value at alias is
//      // arriving here OR directly storing from the NewNode.
//      Node adr = adr();
//      if( adr instanceof FreshNode frsh ) adr = frsh.id();
//      int alias = tmp._aliases.abit();
//      if( adr instanceof NewNode nnn && (tmp._aliases.is_empty() || nnn._alias==alias) )
//        return live.set(nnn._alias,TypeStruct.UNUSED); // Precise set, no longer demanded
//
//      // Since empty can fall to any single precise alias, we need to assume
//      // all things are not demanded until one or more aliases show up.
//      if( tmp._aliases.is_empty() ) {
//        for( int ax=1; ax<mem.len(); ax++ )
//          if( mem.at(ax).above_center() )
//            live = live.set(ax,TypeStruct.UNUSED);
//      } else {
//        if( alias!=-1 && mem.at(alias).above_center() )
//          return live.set(alias,TypeStruct.UNUSED); // Precise set, no longer demanded
//      }
//      // Imprecise update, cannot dataflow kill alias going backwards
//      return live;
//    }
//    // Address changes liveness, the rez can be more live
//    if( rez()!=null ) adr().deps_add(rez());
//
//    // Demanded struct; if ptr just any/all else demand struct
//    TypeStruct ts = live.ld(tmp);
//    return i==CTL_IDX ? ts.oob() : ts;
//  }
//

  // Is this Store alive, based on given liveness?
  // Depends on the field
  @Override boolean _is_live( TypeStruct live ) {
    return live.at_def(_fld) == TypeMem.ALL;
  }

//  @Override public Node ideal_reduce() {
//    if( is_prim() ) return null;
//    if( _live == Type.ANY ) return null; // Dead from below; nothing fancy just await removal
//    Node mem = mem();
//    Node adr = adr();
//    Type ta = adr._val;
//    TypeMemPtr tmp = ta instanceof TypeMemPtr ? (TypeMemPtr)ta : null;
//
//    // Is this Store dead from below?
//    if( mem==this ) return null; // Dead self-cycle
//    if( tmp!=null && mem._val instanceof TypeMem ) {
//      // Address is high, do not bother storing.  Kill stored thing.
//      // Keep the store op until values are monotonic.
//      if( tmp.above_center() && rez() != null )
//        return Env.GVN.add_reduce(set_def(3,null)); // Try again
//      // Same/same up/down, or no value readers
//      if( _live.isa(mem._live) && (_uses._len==1 || mem._val == _val) ) {
//        // If dead from either above or below, we can remove
//        if( tmp.above_center() ) return mem;
//        TypeStruct ts0 = (_live instanceof TypeMem tm ? tm : _live.oob(TypeMem.ALLMEM)).ld(tmp);
//        if( ts0==TypeStruct.UNUSED ) {
//          if( mem._val == _val ) return mem; // Same/same or no readers, just delete
//          if( rez()!=null )
//            return Env.GVN.add_reduce(set_def(3,null)); // Don't store, keep until monotonic
//        }
//      }
//      mem.deps_add(this);   // Input address changes, check reduce
//      deps_add(this);       // Our   address changes, check reduce
//    }
//
//    // Store of a Store, same address
//    if( mem instanceof StoreNode st ) {
//      Node adr0 = st.adr();
//      if( adr  instanceof FreshNode f ) adr  = f.id();
//      if( adr0 instanceof FreshNode f ) adr0 = f.id();
//      if( adr == adr0 ) {
//        // Do not bypass a parallel writer
//        if( st.check_solo_mem_writer(this) &&
//            // And liveness aligns
//            st._live.isa(st.mem()._live) ) {
//          // Storing same-over-same, just use the first store
//          if( rez()==st.rez() ) return st;
//          // If not wiping out an error, wipe out the first store
//          if( st.rez()==null || st.rez().err(true)==null ) {
//            set_def(1,st.mem());
//            return this;
//          }
//        } else {
//          mem.deps_add(this);    // If become solo writer, check again
//        }
//      } else {
//        st.adr().deps_add(this);      // If address changes, check again
//      }
//    }
//
//    // Store of a Load
//    if( rez() instanceof LoadNode ld && ld.adr()==adr && ld.mem()==mem )
//      return mem;
//
//    //// Escape a dead MemSplit
//    //if( mem instanceof MProjNode && mem.in(0) instanceof MemSplitNode msp &&
//    //    msp.join()==null ) {
//    //  set_def(1,msp.mem());
//    //  xval();                   // Update memory state to include all the default memory
//    //  return this;
//    //}
//
//    //
//    //// If Store is of a MemJoin and it can enter the split region, do so.
//    //// Requires no other memory *reader* (or writer), as the reader will
//    //// now see the Store effects as part of the Join.
//    //if( tmp != null && mem instanceof MemJoinNode && mem._uses._len==1 ) {
//    //  Node memw = _uses._len==0 ? this : get_mem_writer(); // Zero or 1 mem-writer
//    //  // Check the address does not have a memory dependence on the Join.
//    //  // TODO: This is super conservative
//    //  if( adr instanceof FreshNode ) adr = ((FreshNode)adr).id();
//    //  if( memw != null && adr instanceof ProjNode && adr.in(0) instanceof NewNode )
//    //    return ((MemJoinNode)mem).add_alias_below_new(new StoreNode(this,mem,adr()),this);
//    //}
//    //
//    return null;
//  }
//
//  // Recursively collapse a set of SetFields into a single-use StructNode
//  static StructNode _fold(Node rez) {
//    if( rez instanceof StructNode st ) return st;
//    if( rez instanceof LoadNode ) return null;
//    SetFieldNode sfn = (SetFieldNode)rez;
//    StructNode st = _fold(sfn.in(0));
//    if( st==null || !st.set_fld(sfn._fld,sfn._fin,sfn.in(1),false) )
//      return null;
//    return st;
//  }
//
//
//  // Given a tptr, trez:
//  //    ptr.load().unify(rez)
//  @Override public boolean has_tvar() { return true; }
//  @Override public TV3 _set_tvar() {
//    assert rez()!=null; // Did not clear out during iter; return mem().tvar()
//
//    //TV3 tmem = mem().set_tvar();   TVMem mem;
//    //if( tmem instanceof TVMem mem0 ) mem = mem0;
//    //else tmem.unify(mem = new TVMem(),false);
//
//    TV3 rez = rez().set_tvar();    TVStruct stz;
//    if( rez instanceof TVStruct stz0 ) stz = stz0;
//    else rez.unify(stz = new TVStruct(true),false);
//    
//    TV3 adr = adr().set_tvar();    TVPtr ptr;
//    if( adr instanceof TVPtr ptr0 ) (ptr=ptr0).load().unify(stz,false);
//    else adr.unify(ptr=new TVPtr(BitsAlias.EMPTY,stz),false);
//    assert ptr.aliases()!=BitsAlias.NALL;
//    
//    //return mem;
//    return null;
//  }
//
//  @Override public boolean unify( boolean test ) {
//    TVPtr ptr = (TVPtr)adr().tvar();
//    return unify(ptr.aliases(),rez().tvar(),test);
//  }
//  static public boolean unify( BitsAlias aliases, TV3 tv, boolean test ) {
//    assert aliases!=BitsAlias.NALL;
//    boolean progress = false;
//    for( int alias : aliases ) {
//      // Called from set_tvar and tvar, so has to init-check
//      NewNode nn = NewNode.get(alias);
//      if( nn._tvar==null ) nn.set_tvar();
//      progress |= ((TVPtr)nn.tvar()).load().unify(tv,test);
//    }
//    return progress;
//  }
//
  @Override public ErrMsg err( boolean fast ) {
    ErrMsg err = super.err(fast);
    if( err!=null ) return err;
    // Check for storing over final
    throw unimpl();
  }
}
