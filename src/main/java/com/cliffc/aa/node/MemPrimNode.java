package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.*;

// Memory-based primitives
public abstract class MemPrimNode extends PrimNode {
  MemPrimNode( String name, TypeTuple formals, TypeNil ret ) { super(name,formals,ret); }
  Node mem() { return in(MEM_IDX); }
  Node adr() { return in(ARG_IDX); }
  Node idx() { return in(ARG_IDX+1); }
  Node rez() { return in(ARG_IDX+2); }
  abstract String bal_close();
  @Override public String xstr() { return _name+(bal_close()==null?"":bal_close()); }

  @Override public ErrMsg err(boolean fast) {
    Type tmem = mem()._val;
    Type tadr = adr()._val;
    Type tidx = _defs._len <= ARG_IDX+1 ? TypeNil.NIL : idx()._val;
    if( tmem==Type.ANY ) return null; // No error
    if( tadr==Type.ANY ) return null; // No error
    if( tidx==Type.ANY ) return null; // No error
    //if( tadr.must_nil() ) return fast ? ErrMsg.FAST : ErrMsg.niladr(_badargs[1],"Array might be nil when reading",null);
    //if( !(tadr instanceof TypeMemPtr) )
    //  return fast ? ErrMsg.FAST : ErrMsg.typerr(_badargs[1],tadr, TypeMemPtr.ISUSED);
    //TypeMemPtr ptr = (TypeMemPtr)tadr;
    //TypeStruct objs = ((TypeMem)tmem).ld(ptr); // General load from memory
    //if( objs==TypeStruct.UNUSED ) return null; // Can fall to valid array
    //if( !(objs instanceof TypeAry) )
    //  return fast ? ErrMsg.FAST : ErrMsg.typerr(_badargs[1],ptr,tmem,TypeMemPtr.ARYPTR);
    //TypeAry ary = (TypeAry)objs;
    //if( tidx instanceof TypeInt ) {
    //  TypeInt idx = (TypeInt)tidx;
    //  if( idx.is_con() ) {
    //    long i = idx.getl();
    //    long len = ary._size.is_con() ? ary._size.getl() : (ary._size._z>=63 ? Integer.MAX_VALUE : (1L<<ary._size._z));
    //    if( i<0 || i>=len ) return fast ? ErrMsg.FAST : ErrMsg.niladr(_badargs[2],"Index must be out of bounds",null);
    //  }
    //}
    //
    //return null;
    throw unimpl();
  }

  // ------------------------------------------------------------
  public abstract static class ReadPrimNode extends MemPrimNode {
    public ReadPrimNode( String name, TypeTuple formals, TypeNil ret ) { super(name,formals,ret); }

    // The only memory required here is what is needed to support the Load
    @Override public Type live_use( int i ) {
      //if( def==adr() ) return TypeMem.ALIVE;
      //if( _defs._len>3 && def==idx() ) return TypeMem.ALIVE;
      //Type tmem = mem()._val;
      //Type tptr = adr()._val;
      //if( !(tmem instanceof TypeMem   ) ) return tmem.oob(TypeMem.ALLMEM); // Not a memory?
      //if( !(tptr instanceof TypeMemPtr) ) return tptr.oob(TypeMem.ALLMEM); // Not a pointer?
      //return ((TypeMem)tmem).remove_no_escapes(((TypeMemPtr)tptr)._aliases,"", Type.SCALAR);
      throw unimpl();
    }

  }

  //// Array length
  //public static class LValueLength extends ReadPrimNode {
  //  public LValueLength() { super("$#",TypeMemPtr.LVAL_LEN,TypeInt.INT64); }
  //  @Override public String bal_close() { return null; } // Not a balanced op
  //  @Override public Type value() {
  //    Type mem = val(MEM_IDX);
  //    Type adr = val(ARG_IDX);
  //    if( !(mem  instanceof TypeMem  ) ) return mem .oob();
  //    if( !(adr instanceof TypeMemPtr) ) return adr.oob();
  //    TypeMemPtr ptr = (TypeMemPtr)mem.sharptr(adr);
  //    if( !(ptr._obj instanceof TypeAry) ) return ptr._obj.oob(TypeInt.INT64);
  //    TypeAry ary = (TypeAry)ptr._obj;
  //    return ary._size;
  //  }
  //  @Override public void add_flow_use_extra(Node chg) {
  //    if( chg==mem() ) Env.GVN.add_flow(adr());  // Memory value lifts to an alias, address is more alive
  //  }
  //  // Similar to LoadNode, of a field named '#'
  //  @Override public TypeMem live_use(Node def ) {
  //    if( def==adr() ) return TypeMem.ALIVE;
  //    Type tmem = mem()._val;
  //    Type tptr = adr()._val;
  //    if( !(tmem instanceof TypeMem   ) ) return tmem.oob(TypeMem.ALLMEM); // Not a memory?
  //    if( !(tptr instanceof TypeMemPtr) ) return tptr.oob(TypeMem.ALLMEM); // Not a pointer?
  //    if( tptr.above_center() ) return TypeMem.ANYMEM; // Loaded from nothing
  //    // Only named the named field from the named aliases is live.
  //    return ((TypeMem)tmem).remove_no_escapes(((TypeMemPtr)tptr)._aliases,"#", Type.SCALAR);
  //  }
  //
  //  @Override public boolean has_tvar() { return true; }
  //  @Override public TV2 new_tvar( String alloc_site) { return TV2.make_base(this,TypeInt.INT64,alloc_site); }
  //
  //  @Override public boolean unify( boolean test ) {
  //    // The input is an array, but that's about all we can say
  //    TV2 tptr = tvar(ARG_IDX);
  //    //if( tptr.isa("Ary") ) return false;
  //    //if( test ) return true;
  //    //Type ptr = val(ARG_IDX);
  //    //tptr.unify(TV2.make("Ary",this,ptr,"array_len",new NonBlockingHashMap<>()),test);
  //    //return true;
  //    throw unimpl();
  //  }
  //
  //  @Override public TypeInt apply( Type[] args ) { throw unimpl(); }
  //}

  //// Produces a binop LValue, where the leading TMP is a non-zero array
  //static class LValueRead extends ReadPrimNode {
  //  LValueRead() { super("[",TypeMemPtr.LVAL_RD,Type.SCALAR); }
  //  @Override public String bal_close() { return "]"; } // Balanced op
  //  @Override public Type value() {
  //    Type mem = val(MEM_IDX);
  //    Type adr = val(ARG_IDX);
  //    Type idx = val(ARG_IDX+1);
  //    if( !(mem  instanceof TypeMem  ) ) return mem .oob();
  //    if( !(adr instanceof TypeMemPtr) ) return adr.oob();
  //    if( !(idx instanceof TypeInt) && idx != Type.XNIL ) return idx.oob();
  //    if( err(true) != null ) return Type.SCALAR;
  //    TypeMemPtr ptr = (TypeMemPtr)mem.sharptr(adr);
  //    TypeInt idx2 = idx==Type.XNIL ? TypeInt.ZERO : (TypeInt)idx;
  //    if( !(ptr._obj instanceof TypeAry) ) return ptr._obj.oob();
  //    TypeAry ary = (TypeAry)ptr._obj;
  //    return ary.ld(idx2);
  //  }
  //
  //  // Standard memory unification; the Load unifies with the loaded field.
  //  @Override public boolean unify( boolean test ) {
  //    return StoreNode.unify("Ary",this,adr().tvar(),adr()._val,tvar(),"elem",test);
  //  }
  //
  //  @Override public TypeInt apply( Type[] args ) { throw unimpl(); }
  //}
  //
  //// ------------------------------------------------------------
  //public abstract static class WritePrimNode extends MemPrimNode {
  //  WritePrimNode( String name, TypeStruct formals, Type ret ) { super(name,formals,ret); }
  //  @Override public boolean is_mem() { return true; }
  //
  //
  //  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
  //  // The only memory required here is what is needed to support the Load
  //  @Override public TypeMem live_use(Node def ) {
  //    if( def==mem() ) return _live; // Pass full liveness along
  //    if( def==rez() ) return TypeMem.ALIVE; // Value escapes
  //    if( def==adr() ) return TypeMem.ALIVE; // Basic aliveness
  //    if( def==idx() ) return TypeMem.ALIVE; // Basic aliveness
  //    throw unimpl();                        // Should not reach here
  //  }
  //  @Override BitsAlias escapees() {
  //    Type adr = adr()._val;
  //    if( !(adr instanceof TypeMemPtr) ) return adr.above_center() ? BitsAlias.EMPTY : BitsAlias.FULL;
  //    return ((TypeMemPtr)adr)._aliases;
  //  }
  //}
  //
  //// Produces a triop LValue, where the leading TMP is a non-zero array
  //static class LValueWrite extends WritePrimNode {
  //  LValueWrite() { super("[",TypeMemPtr.LVAL_WR,Type.SCALAR); }
  //  @Override public String bal_close() { return "]:="; } // Balanced op
  //  @Override public Type value() {
  //    Type mem = val(MEM_IDX);
  //    Type ary = val(ARG_IDX  );
  //    Type idx = val(ARG_IDX+1);
  //    Type val = val(ARG_IDX+2);
  //    if( !(mem instanceof TypeMem   ) ) return mem.oob();
  //    if( !(ary instanceof TypeMemPtr) ) return ary.oob();
  //    if( !(idx instanceof TypeInt) && idx!=Type.XNIL ) return idx.oob();
  //    if( !val.isa(Type.SCALAR) ) return val.oob();
  //    TypeMem    tmem = (TypeMem   )mem;
  //    TypeMemPtr tary = (TypeMemPtr)ary;
  //    TypeInt    tidx = idx==Type.XNIL ? TypeInt.ZERO : (TypeInt)idx;
  //    TypeMem tmem2 = tmem.update(tary._aliases,tidx,val);
  //    return tmem2;
  //  }
  //  @Override public boolean has_tvar() { return true; }
  //  @Override public TV2 new_tvar( String alloc_site) { return null; }
  //  @Override public boolean unify( boolean test ) {
  //    boolean progress = false;
  //    TV2 idx = tvar(ARG_IDX+1);
  //    if( !(idx.is_base() && idx._flow.isa(TypeInt.INT64)) ) {
  //      if( test ) return true;
  //      progress = idx.unify(TV2.make_base(idx(), TypeInt.INT64, "[]:="),test);
  //    }
  //    return StoreNode.unify("Ary",this,adr().tvar(),adr()._val,rez().tvar(),"elem",test) | progress;
  //  }
  //  @Override public TypeInt apply( Type[] args ) { throw unimpl(); }
  //}
  //
  //// Produces a triop LValue, where the leading TMP is a non-zero array
  //static class LValueWriteFinal extends WritePrimNode {
  //  LValueWriteFinal() { super("[",TypeMemPtr.LVAL_WR,Type.SCALAR); }
  //  @Override public String bal_close() { return "]="; } // Balanced op
  //  @Override public Type value() {
  //    Type mem = val(MEM_IDX);
  //    Type ary = val(ARG_IDX  );
  //    Type idx = val(ARG_IDX+1);
  //    Type val = val(ARG_IDX+2);
  //    if( !(mem instanceof TypeMem   ) ) return mem.oob();
  //    if( !(ary instanceof TypeMemPtr) ) return ary.oob();
  //    if( !(idx instanceof TypeInt) && idx!=Type.XNIL ) return idx.oob();
  //    if( !val.isa(Type.SCALAR) ) return val.oob();
  //    TypeMem    tmem = (TypeMem   )mem;
  //    TypeMemPtr tary = (TypeMemPtr)ary;
  //    TypeInt    tidx = idx==Type.XNIL ? TypeInt.ZERO : (TypeInt)idx;
  //    TypeMem tmem2 = tmem.update(tary._aliases,tidx,val);
  //    return tmem2;
  //  }
  //
  //  // Unify address as Ary, idx as int64, Ary.elem and val to self.
  //  @Override public boolean has_tvar() { return true; }
  //  @Override public TV2 new_tvar( String alloc_site) { return null; }
  //  @Override public boolean unify( boolean test ) {
  //    boolean progress = false;
  //    TV2 idx = tvar(ARG_IDX+1);
  //    if( !(idx.is_base() && idx._flow.isa(TypeInt.INT64)) ) {
  //      if( test ) return true;
  //      progress = idx.unify(TV2.make_base(idx(), TypeInt.INT64, "[]:="),test);
  //    }
  //    return StoreNode.unify("Ary",this,adr().tvar(),adr()._val,rez().tvar(),"elem",test) | progress;
  //  }
  //  @Override public TypeInt apply( Type[] args ) { throw unimpl(); }
  //  @Override public ErrMsg err(boolean fast) {
  //    ErrMsg msg = super.err(fast);
  //    if( msg != null ) return msg;
  //    return ErrMsg.syntax(_badargs[0],"Final array assignment not supported.");
  //  }
  //}

}
