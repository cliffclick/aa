package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.*;

// Memory-based primitives
public abstract class MemPrimNode extends PrimNode {
  MemPrimNode( String name, TypeStruct formals, Type ret ) { super(name,formals,ret); _op_prec = 0; }
  Node mem() { return in(MEM_IDX); }
  Node adr() { return in(ARG_IDX); }
  Node idx() { return in(ARG_IDX+1); }
  Node rez() { return in(ARG_IDX+2); }
  abstract String bal_close();
  @Override public String xstr() { return _name+(bal_close()==null?"":bal_close()); }

  @Override public ErrMsg err(boolean fast) {
    Type tmem = mem()._val;
    Type tadr = adr()._val;
    Type tidx = _defs._len <= ARG_IDX+1 ? Type.XNIL : idx()._val;
    if( tmem==Type.ANY ) return null; // No error
    if( tadr==Type.ANY ) return null; // No error
    if( tidx==Type.ANY ) return null; // No error
    if( tadr.must_nil() ) return fast ? ErrMsg.FAST : ErrMsg.niladr(_badargs[1],"Array might be nil when reading",null);
    if( !(tadr instanceof TypeMemPtr) )
      return fast ? ErrMsg.FAST : ErrMsg.typerr(_badargs[1],tadr,tmem,TypeMemPtr.ISUSED);
    TypeMemPtr ptr = (TypeMemPtr)tadr;
    TypeObj objs = ((TypeMem)tmem).ld(ptr); // General load from memory
    if( objs==TypeObj.UNUSED || objs==TypeObj.XOBJ ) return null; // Can fall to valid array
    if( !(objs instanceof TypeAry) )
      return fast ? ErrMsg.FAST : ErrMsg.typerr(_badargs[1],ptr,tmem,TypeMemPtr.ARYPTR);
    TypeAry ary = (TypeAry)objs;
    if( tidx instanceof TypeInt ) {
      TypeInt idx = (TypeInt)tidx;
      if( idx.is_con() ) {
        long i = idx.getl();
        long len = ary._size.is_con() ? ary._size.getl() : (ary._size._z>=63 ? Integer.MAX_VALUE : (1L<<ary._size._z));
        if( i<0 || i>=len ) return fast ? ErrMsg.FAST : ErrMsg.niladr(_badargs[2],"Index must be out of bounds",null);
      }
    }

    return null;
  }

  // ------------------------------------------------------------
  public abstract static class ReadPrimNode extends MemPrimNode {
    public ReadPrimNode( String name, TypeStruct formals, Type ret ) { super(name,formals,ret); }
    
    @Override public FunPtrNode clazz_node( ) {
      try(GVNGCM.Build<FunPtrNode> X = Env.GVN.new Build<>()) {
        assert _defs._len==0 && _uses._len==0;
        FunNode  fun = ( FunNode) X.xform(new  FunNode(_name,this));
        ParmNode rpc = (ParmNode) X.xform(new ParmNode(TypeRPC.ALL_CALL,null,fun,0      ,"rpc"));
        Node mem     =            X.xform(new ParmNode(TypeMem.MEM     ,null,fun,MEM_IDX," mem"));
        fun._bal_close = bal_close();
        add_def(null);              // Control for the primitive in slot 0
        add_def(mem );              // Memory  for the primitive in slot 1
        while( len() < _sig._formals.nargs() ) add_def(null);
        for( TypeFld arg : _sig._formals.flds() )
          if( arg._order!=MEM_IDX ) // Already handled MEM_IDX
            set_def(arg._order,X.xform(new ParmNode(arg._t.simple_ptr(), null, fun, arg._order, arg._fld)));
        Node nnn = X.xform(this);
        // Functions return the set of *modified* memory.  ReadPrimNodes do not modify
        // memory.
        RetNode ret = (RetNode)X.xform(new RetNode(fun,mem,nnn,rpc,fun));
        Env.SCP_0.add_def(ret);
        // No closures are added to primitives
        return (X._ret = (FunPtrNode)X.xform(new FunPtrNode(_name,ret)));
      }
    }

    // The only memory required here is what is needed to support the Load
    @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
      if( def==adr() ) return TypeMem.ALIVE;
      if( _defs._len>3 && def==idx() ) return TypeMem.ALIVE;
      Type tmem = mem()._val;
      Type tptr = adr()._val;
      if( !(tmem instanceof TypeMem   ) ) return tmem.oob(TypeMem.ALLMEM); // Not a memory?
      if( !(tptr instanceof TypeMemPtr) ) return tptr.oob(TypeMem.ALLMEM); // Not a pointer?
      return ((TypeMem)tmem).remove_no_escapes(((TypeMemPtr)tptr)._aliases,"", Type.SCALAR);
    }

  }

  // Array length
  public static class LValueLength extends ReadPrimNode {
    public LValueLength() { super("$#",TypeMemPtr.LVAL_LEN,TypeInt.INT64); _op_prec=1;}
    @Override public String bal_close() { return null; } // Not a balanced op
    @Override public Type value(GVNGCM.Mode opt_mode) {
      Type mem = val(MEM_IDX);
      Type adr = val(ARG_IDX);
      if( !(mem  instanceof TypeMem  ) ) return mem .oob();
      if( !(adr instanceof TypeMemPtr) ) return adr.oob();
      TypeMemPtr ptr = (TypeMemPtr)mem.sharptr(adr);
      if( !(ptr._obj instanceof TypeAry) ) return ptr._obj.oob(TypeInt.INT64);
      TypeAry ary = (TypeAry)ptr._obj;
      return ary._size;
    }
    @Override public void add_work_use_extra(Work work, Node chg) {
      if( chg==mem() ) work.add(adr());  // Memory value lifts to an alias, address is more alive
    }
    // Similar to LoadNode, of a field named '#'
    @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
      if( def==adr() ) return TypeMem.ALIVE;
      Type tmem = mem()._val;
      Type tptr = adr()._val;
      if( !(tmem instanceof TypeMem   ) ) return tmem.oob(TypeMem.ALLMEM); // Not a memory?
      if( !(tptr instanceof TypeMemPtr) ) return tptr.oob(TypeMem.ALLMEM); // Not a pointer?
      if( tptr.above_center() ) return TypeMem.ANYMEM; // Loaded from nothing
      // Only named the named field from the named aliases is live.
      return ((TypeMem)tmem).remove_no_escapes(((TypeMemPtr)tptr)._aliases,"#", Type.SCALAR);
    }
    
    @Override public TV2 new_tvar( String alloc_site) { return TV2.make_base(this,TypeInt.INT64,alloc_site); }

    @Override public boolean unify( Work work ) {
      // The input is an array, but that's about all we can say
      TV2 tptr = tvar(ARG_IDX);
      if( tptr.isa("Ary") ) return false;
      if( work == null ) return true;
      tptr.unify(TV2.make("Ary",this,"array_len"),work);
      return true;
    }

    @Override public TypeInt apply( Type[] args ) { throw unimpl(); }
  }

  // Produces a binop LValue, where the leading TMP is a non-zero array
  static class LValueRead extends ReadPrimNode {
    LValueRead() { super("[",TypeMemPtr.LVAL_RD,Type.SCALAR); }
    @Override public String bal_close() { return "]"; } // Balanced op
    @Override public byte op_prec() { return 0; } // Balanced op
    @Override public Type value(GVNGCM.Mode opt_mode) {
      Type mem = val(MEM_IDX);
      Type adr = val(ARG_IDX);
      Type idx = val(ARG_IDX+1);
      if( !(mem  instanceof TypeMem  ) ) return mem .oob();
      if( !(adr instanceof TypeMemPtr) ) return adr.oob();
      if( !(idx instanceof TypeInt) && idx != Type.XNIL ) return idx.oob();
      if( err(true) != null ) return Type.SCALAR;
      TypeMemPtr ptr = (TypeMemPtr)mem.sharptr(adr);
      TypeInt idx2 = idx==Type.XNIL ? TypeInt.ZERO : (TypeInt)idx;
      if( !(ptr._obj instanceof TypeAry) ) return ptr._obj.oob();
      TypeAry ary = (TypeAry)ptr._obj;
      return ary.ld(idx2);
    }

    // Standard memory unification; the Load unifies with the loaded field.
    @Override public boolean unify( Work work ) {
      return StoreNode.unify("Ary",this,adr().tvar(),adr()._val,this,"elem",work);
    }

    @Override public TypeInt apply( Type[] args ) { throw unimpl(); }
  }

  // ------------------------------------------------------------
  public abstract static class WritePrimNode extends MemPrimNode {
    WritePrimNode( String name, TypeStruct formals, Type ret ) { super(name,formals,ret); }
    @Override public boolean is_mem() { return true; }

    @Override public FunPtrNode clazz_node( ) {
      try(GVNGCM.Build<FunPtrNode> X = Env.GVN.new Build<>()) {
        assert _defs._len==0 && _uses._len==0;
        FunNode  fun = ( FunNode) X.xform(new  FunNode(_name,this).add_def(Env.SCP_0)); // Points to ScopeNode only
        ParmNode rpc = (ParmNode) X.xform(new ParmNode( 0     ,"rpc" ,fun,Env.ALL_CALL,null));
        ParmNode mem = (ParmNode) X.xform(new ParmNode(MEM_IDX," mem",fun,TypeMem.MEM,Env.DEFMEM,null));
        fun._bal_close = bal_close();
        add_def(null);              // Control for the primitive in slot 0
        add_def(mem );              // Memory  for the primitive in slot 1
        while( len() < _sig._formals.nargs() ) add_def(null);
        for( TypeFld arg : _sig._formals.flds() )
          set_def(arg._order,X.xform(new ParmNode(arg._order,arg._fld,fun, (ConNode)Node.con(arg._t.simple_ptr()),null)));
        // Write prims return both a value and memory.
        MemPrimNode prim = (MemPrimNode)X.xform(this);
        RetNode ret = (RetNode)X.xform(new RetNode(fun,prim,prim.rez(),rpc,fun));
        return (X._ret = new FunPtrNode(_name,ret));
      }
    }

    @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
    // The only memory required here is what is needed to support the Load
    @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
      if( def==mem() ) return _live; // Pass full liveness along
      if( def==rez() ) return TypeMem.ESCAPE;// Value escapes
      if( def==adr() ) return TypeMem.ALIVE; // Basic aliveness
      if( def==idx() ) return TypeMem.ALIVE ;// Basic aliveness
      throw unimpl();                        // Should not reach here
    }
    @Override BitsAlias escapees() {
      Type adr = adr()._val;
      if( !(adr instanceof TypeMemPtr) ) return adr.above_center() ? BitsAlias.EMPTY : BitsAlias.FULL;
      return ((TypeMemPtr)adr)._aliases;
    }
  }

  // Produces a triop LValue, where the leading TMP is a non-zero array
  static class LValueWrite extends WritePrimNode {
    LValueWrite() { super("[",TypeMemPtr.LVAL_WR,Type.SCALAR); }
    @Override public String bal_close() { return "]:="; } // Balanced op
    @Override public byte op_prec() { return 0; }
    @Override public Type value(GVNGCM.Mode opt_mode) {
      Type mem = val(MEM_IDX);
      Type ary = val(ARG_IDX  );
      Type idx = val(ARG_IDX+1);
      Type val = val(ARG_IDX+2);
      if( !(mem instanceof TypeMem   ) ) return mem.oob();
      if( !(ary instanceof TypeMemPtr) ) return ary.oob();
      if( !(idx instanceof TypeInt) && idx!=Type.XNIL ) return idx.oob();
      if( !val.isa(Type.SCALAR) ) return val.oob();
      TypeMem    tmem = (TypeMem   )mem;
      TypeMemPtr tary = (TypeMemPtr)ary;
      TypeInt    tidx = idx==Type.XNIL ? TypeInt.ZERO : (TypeInt)idx;
      TypeMem tmem2 = tmem.update(tary._aliases,tidx,val);
      return tmem2;
    }
    @Override public boolean unify( Work work ) {
      boolean progress = false;
      TV2 idx = tvar(ARG_IDX+1);
      if( !(idx.is_base() && idx._type.isa(TypeInt.INT64)) ) {
        if( work==null ) return true;
        progress = idx.unify(TV2.make_base(idx(), TypeInt.INT64, "[]:="), work);
      }
      return StoreNode.unify("Ary",this,adr().tvar(),adr()._val,rez(),"elem",work) | progress;
    }
    @Override public TypeInt apply( Type[] args ) { throw unimpl(); }
  }

  // Produces a triop LValue, where the leading TMP is a non-zero array
  static class LValueWriteFinal extends WritePrimNode {
    LValueWriteFinal() { super("[",TypeMemPtr.LVAL_WR,Type.SCALAR); }
    @Override public String bal_close() { return "]="; } // Balanced op
    @Override public byte op_prec() { return 0; }
    @Override public Type value(GVNGCM.Mode opt_mode) {
      Type mem = val(MEM_IDX);
      Type ary = val(ARG_IDX  );
      Type idx = val(ARG_IDX+1);
      Type val = val(ARG_IDX+2);
      if( !(mem instanceof TypeMem   ) ) return mem.oob();
      if( !(ary instanceof TypeMemPtr) ) return ary.oob();
      if( !(idx instanceof TypeInt) && idx!=Type.XNIL ) return idx.oob();
      if( !val.isa(Type.SCALAR) ) return val.oob();
      TypeMem    tmem = (TypeMem   )mem;
      TypeMemPtr tary = (TypeMemPtr)ary;
      TypeInt    tidx = idx==Type.XNIL ? TypeInt.ZERO : (TypeInt)idx;
      TypeMem tmem2 = tmem.update(tary._aliases,tidx,val);
      return tmem2;
    }

    // Unify address as Ary, idx as int64, Ary.elem and val to self.
    @Override public boolean unify( Work work ) {
      boolean progress = false;
      TV2 idx = tvar(ARG_IDX+1);
      if( !(idx.is_base() && idx._type.isa(TypeInt.INT64)) ) {
        if( work==null ) return true;
        progress = idx.unify(TV2.make_base(idx(), TypeInt.INT64, "[]:="), work);
      }
      return StoreNode.unify("Ary",this,adr().tvar(),adr()._val,rez(),"elem",work) | progress;
    }
    @Override public TypeInt apply( Type[] args ) { throw unimpl(); }
    @Override public ErrMsg err(boolean fast) {
      ErrMsg msg = super.err(fast);
      if( msg != null ) return msg;
      return ErrMsg.syntax(_badargs[0],"Final array assignment not supported.");
    }
  }

}
