package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.*;

// Memory-based primitives
public abstract class MemPrimNode extends PrimNode {
  MemPrimNode( String name, String[] args, TypeTuple formals, Type ret ) { super(name,args,formals,ret); _op_prec = 0; }
  Node mem() { return in(1); }
  Node adr() { return in(2); }
  Node idx() { return in(3); }
  Node rez() { return in(4); }
  abstract String bal_close();
  @Override public String xstr() { return _name+(bal_close()==null?"":bal_close()); }

  @Override public ErrMsg err(boolean fast) {
    Type tmem = mem().val();
    Type tadr = adr().val();
    Type tidx = _defs._len <= 3 ? Type.XNIL : idx().val();
    if( tmem==Type.ANY ) return null; // No error
    if( tadr==Type.ANY ) return null; // No error
    if( tidx==Type.ANY ) return null; // No error
    if( tadr.must_nil() ) return fast ? ErrMsg.FAST : ErrMsg.niladr(_badargs[1],"Array might be nil when reading",null);
    if( !(tadr instanceof TypeMemPtr) )
      throw unimpl();
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
    ReadPrimNode( String name, String[] args, TypeTuple formals, Type ret ) { super(name,args,formals,ret); }

    @Override public FunPtrNode as_fun( GVNGCM gvn ) {
      try(GVNGCM.Build<FunPtrNode> X = gvn.new Build<>()) {
        assert _defs._len==0 && _uses._len==0;
        FunNode  fun = ( FunNode) X.xform(new  FunNode(this).add_def(Env.ALL_CTRL)); // Points to ScopeNode only
        ParmNode rpc = (ParmNode) X.xform(new ParmNode(-1,"rpc",fun,Node.con(TypeRPC.ALL_CALL),null));
        ParmNode mem = (ParmNode) X.xform(new ParmNode(MEM_IDX," mem",fun,TypeMem.MEM,Env.DEFMEM,null));
        fun._bal_close = bal_close();
        add_def(null);              // Control for the primitive in slot 0
        add_def(mem );              // Memory  for the primitive in slot 1
        for( int i=ARG_IDX; i<_sig.nargs(); i++ ) // First is display, never used
          add_def(X.xform(new ParmNode(i,_sig._args[i],fun, Node.con(_sig.arg(i).simple_ptr()),null)));
        X.xform(this);
        // Functions return the set of *modified* memory.  ReadPrimNodes do not modify
        // memory.
        RetNode ret = (RetNode)X.xform(new RetNode(fun,mem(),this,rpc,fun));
        // No closures are added to primitives
        return (X._ret = new FunPtrNode(ret,null));
      }
    }

    // The only memory required here is what is needed to support the Load
    @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
      if( def==adr() ) return TypeMem.ALIVE;
      if( _defs._len>3 && def==idx() ) return TypeMem.ALIVE;
      Type tmem = mem().val();
      Type tptr = adr().val();
      if( !(tmem instanceof TypeMem   ) ) return tmem.oob(TypeMem.ALLMEM); // Not a memory?
      if( !(tptr instanceof TypeMemPtr) ) return tptr.oob(TypeMem.ALLMEM); // Not a pointer?
      return ((TypeMem)tmem).remove_no_escapes(((TypeMemPtr)tptr)._aliases,"");
    }

  }

  // Array length
  static class LValueLength extends ReadPrimNode {
    LValueLength() { super("#",new String[]{" ctl"," mem","^","ary"},TypeTuple.LVAL_LEN,TypeInt.INT64); }
    @Override public String bal_close() { return null; } // Balanced op
    @Override public Node ideal(GVNGCM gvn, int level) { return null; }
    @Override public Type value(GVNGCM.Mode opt_mode) {
      Type mem = val(1);
      Type adr = val(2);
      if( !(mem  instanceof TypeMem  ) ) return mem .oob();
      if( !(adr instanceof TypeMemPtr) ) return adr.oob();
      TypeMemPtr ptr = (TypeMemPtr)mem.sharptr(adr);
      if( !(ptr._obj instanceof TypeAry) ) return ptr._obj.oob(TypeInt.INT64);
      TypeAry ary = (TypeAry)ptr._obj;
      return ary._size;
    }
    @Override public TypeInt apply( Type[] args ) { throw unimpl(); }
  }

  // Produces a binop LValue, where the leading TMP is a non-zero array
  static class LValueRead extends ReadPrimNode {
    LValueRead() { super("[",new String[]{" ctl"," mem","^","ary","idx"},TypeTuple.LVAL_RD,Type.SCALAR); }
    @Override public String bal_close() { return "]"; } // Balanced op
    @Override public byte op_prec() { return 0; } // Balanced op
    @Override public Node ideal(GVNGCM gvn, int level) { return null; }
    @Override public Type value(GVNGCM.Mode opt_mode) {
      Type mem = val(1);
      Type adr = val(2);
      Type idx = val(3);
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
    @Override public TypeInt apply( Type[] args ) { throw unimpl(); }
  }

  // ------------------------------------------------------------
  public abstract static class WritePrimNode extends MemPrimNode {
    WritePrimNode( String name, String[] args, TypeTuple formals, Type ret ) { super(name,args,formals,ret); }

    @Override public FunPtrNode as_fun( GVNGCM gvn ) {
      try(GVNGCM.Build<FunPtrNode> X = gvn.new Build<>()) {
        assert _defs._len==0 && _uses._len==0;
        FunNode  fun = ( FunNode) X.xform(new  FunNode(this).add_def(Env.ALL_CTRL)); // Points to ScopeNode only
        ParmNode rpc = (ParmNode) X.xform(new ParmNode(-1,"rpc",fun,Node.con(TypeRPC.ALL_CALL),null));
        ParmNode mem = (ParmNode) X.xform(new ParmNode(MEM_IDX," mem",fun,TypeMem.MEM,Env.DEFMEM,null));
        fun._bal_close = bal_close();
        add_def(null);              // Control for the primitive in slot 0
        add_def(mem );              // Memory  for the primitive in slot 1
        for( int i=ARG_IDX; i<_sig.nargs(); i++ ) // First is display, never used
          add_def(X.xform(new ParmNode(i,_sig._args[i],fun, Node.con(_sig.arg(i).simple_ptr()),null)));
        // Write prims return both a value and memory.
        MemPrimNode prim = (MemPrimNode)X.xform(this);
        RetNode ret = (RetNode)X.xform(new RetNode(fun,prim,prim.rez(),rpc,fun));
        return (X._ret = new FunPtrNode(ret,null));
      }
    }

    @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
    // The only memory required here is what is needed to support the Load
    @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
      if( def==mem() ) return _live; // Pass full liveness along
      if( def==adr() ) return TypeMem.ALIVE; // Basic aliveness
      if( def==idx() ) return TypeMem.ALIVE ;// Basic aliveness
      if( def==rez() ) return TypeMem.ESCAPE;// Value escapes
      throw unimpl();                        // Should not reach here
    }
    @Override BitsAlias escapees() {
      Type adr = adr().val();
      if( !(adr instanceof TypeMemPtr) ) return adr.above_center() ? BitsAlias.EMPTY : BitsAlias.FULL;
      return ((TypeMemPtr)adr)._aliases;
    }
  }

  // Produces a triop LValue, where the leading TMP is a non-zero array
  static class LValueWrite extends WritePrimNode {
    LValueWrite() { super("[",new String[]{" ctl"," mem","^","ary","idx","val"},TypeTuple.LVAL_WR,Type.SCALAR); }
    @Override public String bal_close() { return "]:="; } // Balanced op
    @Override public byte op_prec() { return 0; }
    @Override public Node ideal(GVNGCM gvn, int level) { return null; }
    @Override public Type value(GVNGCM.Mode opt_mode) {
      Type mem = val(1);
      Type ary = val(2);
      Type idx = val(3);
      Type val = val(4);
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
    @Override public TypeInt apply( Type[] args ) { throw unimpl(); }
  }

  // Produces a triop LValue, where the leading TMP is a non-zero array
  static class LValueWriteFinal extends WritePrimNode {
    LValueWriteFinal() { super("[",new String[]{" ctl"," mem","^","ary","idx","val"},TypeTuple.LVAL_WR,Type.SCALAR); }
    @Override public String bal_close() { return "]="; } // Balanced op
    @Override public byte op_prec() { return 0; }
    @Override public Node ideal(GVNGCM gvn, int level) { return null; }
    @Override public Type value(GVNGCM.Mode opt_mode) {
      Type mem = val(1);
      Type ary = val(2);
      Type idx = val(3);
      Type val = val(4);
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
    @Override public TypeInt apply( Type[] args ) { throw unimpl(); }
    @Override public ErrMsg err(boolean fast) {
      ErrMsg msg = super.err(fast);
      if( msg != null ) return msg;
      return Node.ErrMsg.syntax(_badargs[0],"Final array assignment not supported.");
    }
  }

}
