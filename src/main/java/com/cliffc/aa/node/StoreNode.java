package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVPtr;
import com.cliffc.aa.tvar.TVStruct;
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
  @Override public String xstr() { return "."+_fld+"="; }   // Self short name

  
  @Override Type _value( TypeMem tm, TypeMemPtr tmp ) {
    return tm.update(tmp,TypeFld.make(_fld,rez()._val,_fin));
  }

  @Override Type _live_use( TypeMem live0, TypeMemPtr tmp, int i ) {
    assert !tmp.above_center();
    // Not a precise store, so no kills
    if( !tmp.is_con() ) {
      // Asking for live-in, give it
      if( i==1 ) return live0;
      TypeStruct luse = live0.ld(tmp);
      assert i==2 || i==3;        // Address & value live
      return luse.oob();          // Address is ANY/ALL
    }
    
    throw unimpl();
  }
  
  @Override TypeMem _live_kill(TypeMemPtr tmp) {
    return ((TypeMem)_live).kill(tmp._aliases,_fld);
  }


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

  @Override public TV3 _set_tvar() {
    assert rez()!= Env.ANY; // Did not clear out during iter; return mem().tvar()

    // Address is a ptr to a struct
    TV3 adr = adr().set_tvar();
    TVPtr ptr = adr instanceof TVPtr ptr0 ? ptr0 : new TVPtr(BitsAlias.EMPTY, new TVStruct(true));
    adr.unify(ptr,false);
    // The struct
    TVStruct ts = ptr.load();
    // Add/unify field into struct
    TV3 fld = rez().set_tvar();
    TV3 xfld = ts.arg(_fld);
    if( xfld==null ) ts.add_fld(_fld,fld,false);
    else             fld.unify(xfld,false);
    return null;
  }

  @Override public boolean unify( boolean test ) {
    TVPtr ptr = (TVPtr)adr().tvar();
    TV3 fld = rez().tvar();
    BitsAlias aliases = ptr.aliases();
    assert aliases!=BitsAlias.NALL;
    boolean progress = false;
    for( int alias : aliases ) {
      // Each alias unifies into the global field state
      TVPtr nptr = (TVPtr)NewNode.get(alias).tvar();
      TV3 xfld = nptr.load().arg(_fld);
      progress |= fld.unify(xfld,test);
      if( test && progress ) return true;
    }
    return progress;
  }

  @Override public ErrMsg err( boolean fast ) {
    ErrMsg err = super.err(fast);
    if( err!=null ) return err;
    // Check for storing over final
    throw unimpl();
  }
}
