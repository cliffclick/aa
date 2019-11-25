package com.cliffc.aa.type;

import com.cliffc.aa.util.VBitSet;

// Types which extend memory-based objects - currently Structs (which include
// tuples but not TypeTuple) and Str (Strings); will include Arrays at some
// point.  Structs have memory words addressed by a base-pointer and a field
// name (for tuples, the field number), and Arrays have memory words addressed
// by a base-pointer and an index.
public class TypeObj<O extends TypeObj<O>> extends Type<O> {
  boolean _any;                 // True=choice/join; False=all/meet
  public BitsAlias _news;       // NewNode aliases that make this type
  TypeObj(byte type, boolean any, BitsAlias news) { super(type); init(type,any,news); }
  protected void init (byte type, boolean any, BitsAlias news) { super.init(type); _any=any; _news=news;}
  // Hash does not depend on other types, so never changes
  @Override int compute_hash() { return _type+(_any?1:0); }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    return o instanceof TypeObj &&
      _any==((TypeObj)o)._any &&
      _type==((TypeObj)o)._type &&
      (_news == null || ((TypeObj)o)._news==null ||  _news==((TypeObj)o)._news);
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( VBitSet dups ) { return (_any?"~":"") + _news.toString()+"obj"; }

  private static TypeObj FREE=null;
  @Override protected O free( O ret ) { FREE=this; return ret; }
  @SuppressWarnings("unchecked")
  private static TypeObj make_impl( boolean any, BitsAlias news ) {
    TypeObj t1 = FREE;
    if( t1 == null ) t1 = new TypeObj(TOBJ,any,news);
    else { FREE = null; t1.init(TOBJ,any,news); }
    TypeObj t2 = (TypeObj)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }
  public Type make( boolean any, BitsAlias news ) { return make_impl(any,news); }
  public static final TypeObj OBJ = make_impl(false,BitsAlias.NZERO);
  public static final TypeObj XOBJ = (TypeObj)OBJ.dual();
  static final TypeObj[] TYPES = new TypeObj[]{OBJ,XOBJ};

  @SuppressWarnings("unchecked")
  @Override protected O xdual() { return (O)new TypeObj(TOBJ,!_any,_news.dual()); }
  @Override protected Type xmeet( Type t ) {
    if( !(t instanceof TypeObj) ) return ALL;
    if( t instanceof TypeName ) return t.xmeet(this); // Let TypeName sort it out (since Name::int8 should drop to ALL)
    TypeObj to = (TypeObj)t;
    BitsAlias news = to._news == null ? _news : _news.meet(to._news); // _news can be null for global constant strings
    return _any ? to.make(to._any,news) : make(_any,news);
  }
  // Update (approximately) the current TypeObj.  Merges fields.
  public TypeObj update(byte fin, String fld, Type val) { return this; }
  // Exact object update.  Replaces fields.
  public TypeObj st    (byte fin, String fld, Type val) { return this; }
  // Allowed to update this field?  No fields in an OBJ, but an XOBJ might fall
  // to a struct with fields.
  public boolean can_update(String fld) { return above_center(); }
  public TypeObj lift_final() { return this; }
  BitsAlias aliases() { return _news; }
  @Override public boolean above_center() { return _any; }
  @Override public boolean may_be_con() { return _any; }
  @Override public boolean is_con() { return false; }
  @Override public boolean must_nil() { return false; }
  @Override public boolean  may_nil() { return false; }
  @Override Type make_recur(TypeName tn, int d, VBitSet bs ) { return this; }
  // Dual, except keep TypeMem.XOBJ as high for starting GVNGCM.opto() state.
  @Override public TypeObj startype() { assert _type==TOBJ; return XOBJ; }
  TypeObj make_base(TypeStruct obj) { throw com.cliffc.aa.AA.unimpl(); } // Only valid for TypeName,TypeStruct
}
