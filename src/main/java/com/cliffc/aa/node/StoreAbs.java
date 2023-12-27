package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.TODO;
import static com.cliffc.aa.AA.MEM_IDX;

// Store a value into a named struct field.  Does it's own nil-check and value
// testing; also checks final field updates.
public abstract class StoreAbs extends Node {
  private final Parse _bad;
  public StoreAbs( Node mem, Node adr, Node val, Parse bad ) {
    super(null,mem,adr,val);
    _bad = bad;
  }
  
  @Override public boolean isMem() { return true; }

  public Node mem() { return in(1); }
  public Node adr() { return in(2); }
  public Node rez() { return in(3); }

  @Override public final Type value() {
    if( !(mem()._val instanceof TypeMem    tm ) ) return mem()._val.oob(TypeMem.ALLMEM);
    if( !(adr()._val instanceof TypeMemPtr tmp) ) return adr()._val.oob(TypeMem.ALLMEM);
    // Meet no aliases into memory
    if( tmp.above_center() || tmp._aliases.is_empty() )  return tm;
    if( tmp._aliases==BitsAlias.NALL ) return TypeMem.ALLMEM; // Updates all of memory
    // Subclass defined behavior
    return _value(tm, tmp);
  }
  // Subclasses define behavior past just a mem & ptr
  abstract Type _value( TypeMem tm, TypeMemPtr tmp );
  
  // Compute the liveness local contribution to def's liveness.  Turns around
  // value into live: if values are ANY then nothing is demand-able.
  @Override final public Type live_use( int i ) {
    // Currently Stores do not have control
    if( i==0 ) throw TODO();

    // _live is what is demanded from me;
    // - if my ptr is high, I do not know what to crush, so I might store all such aliases, so all are crushed (whole struct or just fields)
    // - if my ptr is low & con, I exactly crush it - whole struct or just  field
    // - if my ptr is low and not con, I do not crush anything, so liveness is untouched
    // - if asking for ptr or rez, if my live-in != live-out, I am using ptr and rez

    // Pointer, which memory we might kill
    TypeMemPtr tmp = adr()._val instanceof TypeMemPtr tmp0 ? tmp0 : adr()._val.oob(TypeMemPtr.ISUSED);
    if( tmp.above_center() ) {
      if( i!=MEM_IDX ) return Type.ANY;
      if( tmp._aliases==BitsAlias.NANY ) return TypeMem.ANYMEM; // High, killing all
      // Kill specific structs or fields
      return _live_kill(tmp);
    }
    adr().deps_add(in(i));
    
    // Liveness as a TypeMem.  If current liveness is the default ALL, go ahead
    // an upgrade to RootNodes global default - which globally excludes kills.
    TypeMem live0 = _live== Type.ALL ? RootNode.def_mem(this) : (TypeMem)_live;
    // Specific live-use varies from field-vs-struct
    return _live_use(live0,tmp,i);
  }
  abstract Type _live_use( TypeMem live0, TypeMemPtr tmp, int i );
  abstract TypeMem _live_kill(TypeMemPtr tmp);

  abstract boolean st_st_check( StoreAbs st );
  
  @Override public Node ideal_reduce() {
    if( isPrim() ) return null;
    if( _live == Type.ANY ) return null; // Dead from below; nothing fancy just await removal
    
    Node mem = mem();
    Node adr = adr();
    if( mem==this ) return null; // Dead self-cycle

    // Address is high, nothing is stored
    if( adr._val.above_center() )
      return kill_rez_stall_till_live();
    
    // Is this Store dead from below?
    if( adr._val instanceof TypeMemPtr tmp && _live instanceof TypeMem lmem &&
        !_is_live(lmem.ld(tmp)) )
      return kill_rez_stall_till_live();

    // Store of a Store, same address
    if( mem instanceof StoreNode st ) {
      Node adr0 = st.adr();
//      if( adr  instanceof FreshNode f ) adr  = f.id();
//      if( adr0 instanceof FreshNode f ) adr0 = f.id();
      if( adr == adr0 && st_st_check(st) ) {
        // Do not bypass a parallel writer
        if( st.check_solo_mem_writer(this) &&
            // And liveness aligns
            st._live.isa(st.mem()._live) ) {
          // Storing same-over-same, just use the first store
          if( rez()==st.rez() ) return st;
          // If not wiping out an error, wipe out the first store
          if( st.rez()==null || st.rez().err(true)==null ) {
//            set_def(1,st.mem());
//            return this;
            throw TODO();
          }
        } else {
          mem.deps_add(this);    // If become solo writer, check again
        }
      } else {
        st.adr().deps_add(this);      // If address changes, check again
      }
    }

    // Store of a Load
    if( rez() instanceof LoadNode ld && ld.adr()==adr() && ld.mem()==mem )
      throw TODO(); //return mem;

    return null;
  }

  // Is this Store alive, based on given liveness?
  // StoreX checks the whole struct while Store only checks the field
  abstract boolean _is_live( TypeStruct live );
  
  // Still until live-ness alives, then kill self
  private Node kill_rez_stall_till_live() {
    // No need for rez
    if( rez()!=Env.ANY ) Env.GVN.add_reduce(setDef(3,Env.ANY));
    // Remove when liveness aligns
    if( _live.isa(mem()._live) ) return mem();
    mem().deps_add(this);
    return null;
  }

  
  // Given a tptr, trez:
  //    ptr.load().unify(rez)
  @Override public boolean has_tvar() { return true; }
 
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
    throw TODO();
  }

}
