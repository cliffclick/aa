package com.cliffc.aa.type;

import com.cliffc.aa.util.VBitSet;

/*
Theory: TypeObj have an alias#, never themselves have an aliasing issue.
TypeMem merges unrelated TypeObjs as always.
TypeMemPtr CAN have multi-aliases and CAN alias to different TO's.

Problem is lack of canonicalization: TypeMem[#4:str,#7:str] - 4 is parent of 7
and both are Str.  Should fold up, but [4]:str != [7]:str.

So alias# in TypeObj can be removed / ignored?  Only for debug?

TMP has a set of alias#s.  Maybe even remove/ignores TO.  A TMP means nothing
without a TM?  Can I make a ptr-to-struct?  Or only a ptr-to-[17] and TM[17] is
a struct?

TM just indexes TOs by alias#.


*/



// Types which extend memory-based objects - currently Structs (which include
// tuples but not TypeTuple) and Str (Strings); will include Arrays at some
// point.  Structs have memory words addressed by a base-pointer and a field
// name (for tuples, the field number), and Arrays have memory words addressed
// by a base-pointer and an index.
public class TypeObj<O extends TypeObj<O>> extends Type<O> {
  boolean _any;                 // True=choice/join; False=all/meet
  TypeObj(byte type, boolean any) { super(type); init(type,any); }
  protected void init (byte type, boolean any) { super.init(type); _any=any;}
  // Hash does not depend on other types, so never changes
  @Override int compute_hash() { return _type+(_any?1:0); }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    return o instanceof TypeObj &&
      _any ==((TypeObj)o)._any &&
      _type==((TypeObj)o)._type;
  }
  //@Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( VBitSet dups ) { return _any?"~obj":"obj"; }

  private static TypeObj FREE=null;
  @Override protected O free( O ret ) { FREE=this; return ret; }
  @SuppressWarnings("unchecked")
  private static TypeObj make_impl( boolean any ) {
    TypeObj t1 = FREE;
    if( t1 == null ) t1 = new TypeObj(TOBJ,any);
    else { FREE = null; t1.init(TOBJ,any); }
    TypeObj t2 = (TypeObj)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }
  public static Type make0( boolean any ) { return make_impl(any); }
  public static final TypeObj OBJ = make_impl(false);
  public static final TypeObj XOBJ = (TypeObj)OBJ.dual();
  static final TypeObj[] TYPES = new TypeObj[]{OBJ,XOBJ};

  @SuppressWarnings("unchecked")
  @Override protected O xdual() { return (O)new TypeObj(TOBJ,!_any); }
  @Override protected Type xmeet( Type t ) {
    if( !(t instanceof TypeObj) ) return ALL;
    if( t instanceof TypeName ) return t.xmeet(this); // Let TypeName sort it out (since Name::int8 should drop to ALL)
    return _any ? t : OBJ;
  }
  // Update (approximately) the current TypeObj.  Merges fields.
  public TypeObj update(byte fin, String fld, Type val) { return this; }
  // Exact object update.  Replaces fields.
  public TypeObj st    (byte fin, String fld, Type val) { return this; }
  // Allowed to update this field?  No fields in an OBJ, but an XOBJ might fall
  // to a struct with fields.
  public boolean can_update(String fld) { return above_center(); }
  public TypeObj lift_final() { return this; }
  @Override public boolean above_center() { return _any; }
  @Override public boolean may_be_con() { return _any; }
  @Override public boolean is_con() { return false; }
  @Override public boolean must_nil() { return false; }
  @Override public boolean  may_nil() { return false; }
  //@Override Type make_recur(TypeName tn, int d, VBitSet bs ) { return this; }
  // Dual, except keep TypeMem.XOBJ as high for starting GVNGCM.opto() state.
  @Override public TypeObj startype() { assert _type==TOBJ; return XOBJ; }
}
