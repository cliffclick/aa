package com.cliffc.aa.type;

import com.cliffc.aa.util.VBitSet;
// Types which extend memory-based objects - currently Structs (which include
// tuples but not TypeTuple) and Str (Strings); will include Arrays at some
// point.  Structs have memory words addressed by a base-pointer and a field
// name (for tuples, the field number), and Arrays have memory words addressed
// by a base-pointer and an index.
public class TypeObj<O extends TypeObj<O>> extends Type<O> {
  boolean _any;                 // True=choice/join; False=all/meet
  TypeObj             (byte type, String name, boolean any) { super(type); init(type,name,any); }
  protected void init (byte type, String name, boolean any) { super.init(type, name); _any=any;}
  // Hash does not depend on other types, so never changes
  @Override int compute_hash() { return super.compute_hash()+(_any?1:0); }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeObj) || !super.equals(o) ) return false;
    return _any ==((TypeObj)o)._any;
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( VBitSet dups ) { return _name+(_any?"~obj":"obj"); }

  private static TypeObj FREE=null;
  @Override protected O free( O ret ) { FREE=this; return ret; }
  @SuppressWarnings("unchecked")
  private static TypeObj make( String name, boolean any ) {
    TypeObj t1 = FREE;
    if( t1 == null ) t1 = new TypeObj(TOBJ,name,any);
    else {  FREE = null;      t1.init(TOBJ,name,any); }
    TypeObj t2 = (TypeObj)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }
  public static Type make0( boolean any ) { return make("",any); }
  public static final TypeObj OBJ = make("",false);
  public static final TypeObj XOBJ = (TypeObj)OBJ.dual();
  static final TypeObj[] TYPES = new TypeObj[]{OBJ,XOBJ};

  @SuppressWarnings("unchecked")
  @Override protected O xdual() { return (O)new TypeObj(TOBJ,_name,!_any); }
  @Override protected Type xmeet( Type t ) {
    if( !(t instanceof TypeObj) ) return ALL;
    return _any ? t : OBJ;
  }
  // Update (approximately) the current TypeObj.  Merges fields.
  public TypeObj update(byte fin, String fld, Type val) { return this; }
  // Exact object update.  Replaces fields.
  public TypeObj st    (byte fin, String fld, Type val) { return this; }
  // True if this field is not modified.  Allows a Load to bypass.
  boolean is_clean(String fld) { return _any; }

  @Override public boolean above_center() { return _any; }
  @Override public boolean may_be_con() { return _any; }
  @Override public boolean is_con() { return false; }
  @Override public boolean must_nil() { return false; }
  @Override public boolean  may_nil() { return false; }
  // Dual, except keep TypeMem.XOBJ as high for starting GVNGCM.opto() state.
  @Override public TypeObj startype() { assert _type==TOBJ; return XOBJ; }
}
