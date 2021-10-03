package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.*;

// Allocates a TypeStr in memory.  Weirdly takes a string OBJECT (not pointer),
// and produces the pointer.  Hence, liveness is odd.
public abstract class NewStrNode extends NewNode.NewPrimNode<TypeStr> {
  public NewStrNode( TypeStr to, String name, boolean reads, int op_prec, TypeFld... args) {
    super(OP_NEWSTR,BitsAlias.STR,to,name,reads,TypeStr.STR,op_prec,args);
  }

  @Override public TV2 new_tvar(String alloc_site) { return TV2.make("Str",this,alloc_site); }

  @Override public boolean unify(Work work) {
    TV2 tv = tvar();
    if( tv._type==null ) { tv._type = _tptr; return true; }
    return false;
  }

  @Override TypeStr dead_type() { return TypeStr.XSTR; }

  // --------------------------------------------------------------------------
  public static class ConStr extends NewStrNode {
    public ConStr( String str ) { super(TypeStr.con(str),"con",false,-1,TypeFld.MEM); }
    @Override TypeStr valueobj() { return _ts; }
    @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) { throw unimpl(); } // No inputs
    // Constant Strings intern
    @Override public int hashCode() { return is_unused() ? super.hashCode() : _ts._hash; }
    @Override public boolean equals(Object o) { return o instanceof ConStr && _ts==((ConStr)o)._ts; }
    @Override public TV2 new_tvar(String alloc_site) { return TV2.make_base(this,_tptr==null ? null : _tptr.make_from(_ts),alloc_site); }
  }

  public static class ConvertI64Str extends NewStrNode {
    public ConvertI64Str( ) { super(TypeStr.STR,"str",false,-1,TypeFld.make_arg(TypeInt.INT64,ARG_IDX)); }
    @Override TypeObj valueobj() {
      Type t = val(ARG_IDX);
      if( t.above_center() || !(t instanceof TypeInt) ) return t.oob(TypeStr.STR);
      if( !t.is_con() ) return TypeStr.STR;
      return TypeStr.make(false,Long.toString(t.getl()).intern());
    }
    @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) { return TypeMem.ALIVE; }
  }

  public static class ConvertF64Str extends NewStrNode {
    public ConvertF64Str( ) { super(TypeStr.STR,"str",false,-1,TypeFld.make_arg(TypeFlt.FLT64,ARG_IDX)); }
    @Override TypeObj valueobj() {
      Type t = val(ARG_IDX);
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
    private static final int OP_PREC=7;
    public AddStrStr( ) { super(TypeStr.STR,"$+",true,OP_PREC,
                                TypeFld.make_arg(TypeMemPtr.STR0,ARG_IDX  ),
                                TypeFld.make_arg(TypeMemPtr.STR0,ARG_IDX+1)); }
    @Override public Type value(GVNGCM.Mode opt_mode) {
      if( is_unused() ) return Type.ANY;
      Type m   = val(MEM_IDX);
      Type sp0 = val(ARG_IDX);
      Type sp1 = val(ARG_IDX+1);
      if( !(m instanceof TypeMem)   ) return _value(sp0,sp1,m.oob(TypeObj.ISUSED));
      if( sp0==Type.XNIL && sp1==Type.XNIL ) return TypeTuple.make(Type.CTRL,TypeObj.UNUSED,Type.XNIL);
      if( sp0.above_center() || sp1.above_center() ) return _value(sp0,sp1,TypeObj.UNUSED);
      if( !sp0.isa(TypeMemPtr.STR0.simple_ptr()) ) return _value(sp0,sp1,TypeStr.STR);
      if( !sp1.isa(TypeMemPtr.STR0.simple_ptr()) ) return _value(sp0,sp1,TypeStr.STR);
      TypeMem mem = (TypeMem)m;
      TypeObj s0 = sp0==Type.XNIL ? TypeObj.UNUSED : mem.ld((TypeMemPtr)sp0);
      TypeObj s1 = sp1==Type.XNIL ? TypeObj.UNUSED : mem.ld((TypeMemPtr)sp1);
      if( sp0==Type.XNIL ) return _value(sp0,sp1,s1);
      if( sp1==Type.XNIL ) return _value(sp0,sp1,s0);
      if( !(s0 instanceof TypeStr) || !(s1 instanceof TypeStr) )
        return _value(sp0,sp1,s0.above_center() && s1.above_center() ? TypeStr.XSTR : TypeStr.STR);
      TypeStr str0 = (TypeStr)s0;
      TypeStr str1 = (TypeStr)s1;
      if( !str0.is_con() || !str1.is_con() )
        return _value(sp0,sp1,TypeStr.STR);
      return _value(sp0,sp1,TypeStr.make(false,(str0.getstr()+str1.getstr()).intern()));
    }
    TypeTuple _value(Type sp0, Type sp1, TypeObj tobj) {
      Type tp = sp0.must_nil() && sp1.must_nil() ? _tptr.meet_nil(Type.XNIL) : _tptr;
      return TypeTuple.make(Type.CTRL,tobj,tp);
    }
    @Override TypeObj valueobj() { throw unimpl(); }
    @Override public byte op_prec() { return (byte)OP_PREC; }
    @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
      if( def==in(ARG_IDX) || def==in(ARG_IDX+1) ) return TypeMem.ALIVE;
      assert def==in(MEM_IDX);
      // Memory for aliases is alive, as-if a READ/LOAD
      Type tmem = val(MEM_IDX);
      Type tptr0= val(ARG_IDX);
      Type tptr1= val(ARG_IDX+1);
      if( !(tmem  instanceof TypeMem   ) ) return tmem .oob(TypeMem.ALLMEM); // Not a memory?
      if( !(tptr0 instanceof TypeMemPtr) ) return tptr0.oob(TypeMem.ALLMEM); // Not a pointer?
      if( !(tptr1 instanceof TypeMemPtr) ) return tptr1.oob(TypeMem.ALLMEM); // Not a pointer?
      TypeMem esc0 = ((TypeMem)tmem).remove_no_escapes(((TypeMemPtr)tptr0)._aliases,"",Type.SCALAR);
      TypeMem esc1 = ((TypeMem)tmem).remove_no_escapes(((TypeMemPtr)tptr1)._aliases,"",Type.SCALAR);
      return (TypeMem)esc0.meet(esc1);
    }
    @Override public void add_work_use_extra(Work work,Node chg) {
      if( chg==in(ARG_IDX) || chg==in(ARG_IDX+1) ) work.add(in(MEM_IDX));  // Address into a Load changes, the Memory can be more alive.
    }
  }
}
