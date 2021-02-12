package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;

// Allocates a TypeStr in memory.  Weirdly takes a string OBJECT (not pointer),
// and produces the pointer.  Hence liveness is odd.
public abstract class NewStrNode extends NewNode.NewPrimNode<TypeStr> {
  public NewStrNode( TypeStr to, String name, boolean reads, int op_prec, Type... args) {
    super(OP_NEWSTR,BitsAlias.STR,to,name,reads,op_prec,args);
  }
  @Override TypeStr dead_type() { return TypeStr.XSTR; }
  protected static void add_libs( Ary<NewPrimNode> INTRINSICS ) {
    INTRINSICS.push(new ConvertI64Str());
    INTRINSICS.push(new ConvertF64Str());
    INTRINSICS.push(new AddStrStr());
  }

  // --------------------------------------------------------------------------
  public static class ConStr extends NewStrNode {
    public ConStr( String str ) { super(TypeStr.con(str),"con",false,-1,Type.CTRL,TypeMem.ALLMEM,null); }
    @Override TypeStr valueobj() { return _ts; }
    @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) { throw com.cliffc.aa.AA.unimpl(); } // No inputs
    // Constant Strings intern
    @Override public int hashCode() { return _ts._hash; }
    @Override public boolean equals(Object o) { return o instanceof ConStr && _ts==((ConStr)o)._ts; }
  }

  public static class ConvertI64Str extends NewStrNode {
    public ConvertI64Str( ) { super(TypeStr.STR,"str",false,-1,Type.CTRL,TypeMem.ALLMEM,null,TypeInt.INT64); }
    @Override TypeObj valueobj() {
      Type t = val(3);
      if( t.above_center() || !(t instanceof TypeInt) ) return t.oob(TypeStr.STR);
      if( !t.is_con() ) return TypeStr.STR;
      return TypeStr.make(false,Long.toString(t.getl()).intern());
    }
    @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) { return TypeMem.ALIVE; }
  }

  public static class ConvertF64Str extends NewStrNode {
    public ConvertF64Str( ) { super(TypeStr.STR,"str",false,-1,Type.CTRL,TypeMem.ALLMEM,null,TypeFlt.FLT64); }
    @Override TypeObj valueobj() {
      Type t = val(3);
      if( t.above_center() || !(t instanceof TypeFlt) ) return t.oob(TypeStr.STR);
      if( !t.is_con() ) return TypeStr.STR;
      return TypeStr.make(false,Double.toString(t.getd()).intern());
    }
    @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) { return TypeMem.ALIVE; }
  }

  // String concat.  NIL values are treated "as-if" the empty string.
  // If both arguments are NIL, NIL is returned.
  // If one  argument  is  NIL, the other non-nil argument is returned.
  // If neither argument is NIL, the two strings are concatenated into a new third string.
  public static class AddStrStr extends NewStrNode {
    private static int OP_PREC=7;
    public AddStrStr( ) { super(TypeStr.STR,"+",true,OP_PREC,Type.CTRL,TypeMem.MEM_STR,null,TypeMemPtr.STR0,TypeMemPtr.STR0); }
    @Override public Type value(GVNGCM.Mode opt_mode) {
      if( is_unused() ) return Type.ANY;
      Type m   = val(1);
      Type sp0 = val(3);
      Type sp1 = val(4);
      if( m.above_center() || sp0.above_center() || sp1.above_center() ) return Type.ANY;
      if( !(m instanceof TypeMem)   ) return Type.ALL;
      if( sp0==Type.XNIL && sp1==Type.XNIL ) return TypeTuple.make(TypeObj.UNUSED,Type.XNIL);
      if( !sp0.isa(TypeMemPtr.STR0) ) return _value(TypeStr.STR);
      if( !sp1.isa(TypeMemPtr.STR0) ) return _value(TypeStr.STR);
      TypeMem mem = (TypeMem)m;
      TypeObj s0 = sp0==Type.XNIL ? TypeObj.UNUSED : mem.ld((TypeMemPtr)sp0);
      TypeObj s1 = sp1==Type.XNIL ? TypeObj.UNUSED : mem.ld((TypeMemPtr)sp1);
      if( sp0==Type.XNIL ) return _value(s1);
      if( sp1==Type.XNIL ) return _value(s0);
      if( !(s0 instanceof TypeStr) || !(s1 instanceof TypeStr) ) return _value(TypeStr.STR);
      TypeStr str0 = (TypeStr)s0;
      TypeStr str1 = (TypeStr)s1;
      if( !str0.is_con() || !str1.is_con() ) return _value(TypeStr.STR);
      return _value(TypeStr.make(false,(str0.getstr()+str1.getstr()).intern()));
    }
    TypeTuple _value(TypeObj tobj) { return TypeTuple.make(Type.CTRL,tobj,_tptr); }
    @Override TypeObj valueobj() { throw com.cliffc.aa.AA.unimpl(); }
    @Override public byte op_prec() { return (byte)OP_PREC; }
    @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
      if( def==in(3) || def==in(4) ) return TypeMem.ALIVE;
      assert def==in(1);
      // Memory for aliases is alive, as-if a READ/LOAD
      Type tmem = val(1);
      Type tptr0= val(3);
      Type tptr1= val(4);
      if( !(tmem  instanceof TypeMem   ) ) return tmem .oob(TypeMem.ALLMEM); // Not a memory?
      if( !(tptr0 instanceof TypeMemPtr) ) return tptr0.oob(TypeMem.ALLMEM); // Not a pointer?
      if( !(tptr1 instanceof TypeMemPtr) ) return tptr1.oob(TypeMem.ALLMEM); // Not a pointer?
      TypeMem esc0 = ((TypeMem)tmem).remove_no_escapes(((TypeMemPtr)tptr0)._aliases,"");
      TypeMem esc1 = ((TypeMem)tmem).remove_no_escapes(((TypeMemPtr)tptr1)._aliases,"");
      return (TypeMem)esc0.meet(esc1);
    }
    @Override public void add_flow_use_extra(Node chg) {
      if( chg==in(3) || chg==in(4) ) Env.GVN.add_flow(in(1));  // Address into a Load changes, the Memory can be more alive.
    }
  }
}
