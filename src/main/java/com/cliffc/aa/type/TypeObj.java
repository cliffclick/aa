package com.cliffc.aa.type;

import com.cliffc.aa.util.VBitSet;
import java.util.function.Predicate;

// Types which extend memory-based objects - currently Structs (which include
// tuples but not TypeTuple) and Str (Strings); will include Arrays at some
// point.  Structs have memory words addressed by a base-pointer and a field
// name (for tuples, the field number), and Arrays have memory words addressed
// by a base-pointer and an index.
public class TypeObj<O extends TypeObj<O>> extends Type<O> {
  boolean _any;                 // True=choice/join; False=all/meet
  boolean _use;                 // Equal to _any for OBJ/XOBJ; unequal to _any for UNUSED/ISUSED
  public boolean _esc;          // Some pointer-to-obj has escaped
  protected TypeObj  (byte type, String name, boolean any, boolean esc) { this(type,name,any,any,esc); }
  protected void init(byte type, String name, boolean any, boolean esc) { init(type,name,any,any,esc); }
  private TypeObj    (byte type, String name, boolean any, boolean use, boolean esc) { super(type); init(type,name,any,use,esc); }
  private void init  (byte type, String name, boolean any, boolean use, boolean esc) { super.init(type, name); _any=any; _use=use; _esc=esc; }
  // Hash does not depend on other types, so never changes
  @Override int compute_hash() { return super.compute_hash()+(_any?1:0)+(_use?2:0)+(_esc?4:0); }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeObj) || !super.equals(o) ) return false;
    TypeObj to = (TypeObj)o;
    return _any ==to._any && _use ==to._use && _esc==to._esc;
  }
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( VBitSet dups ) {
    String x = _any==_use ? "obj" : "use";
    return _name+((_any?"~":"")+(_esc?"!":"")+x);
  }

  private static TypeObj FREE=null;
  @Override protected O free( O ret ) { FREE=this; return ret; }
  @SuppressWarnings("unchecked")
  private static TypeObj make( String name, boolean any, boolean use, boolean esc ) {
    TypeObj t1 = FREE;
    if( t1 == null ) t1 = new TypeObj(TOBJ,name,any,use,esc);
    else {  FREE = null;      t1.init(TOBJ,name,any,use,esc); }
    TypeObj t2 = (TypeObj)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }
  public static final TypeObj OBJ   = make("",false,false,true); // Any obj; allocated as *something*
  public static final TypeObj ISUSED= make("",false,true ,true); // Possibly allocated, the worst possible result
  public static final TypeObj UNUSED= (TypeObj)ISUSED.dual();    // Never allocated
  public static final TypeObj XOBJ  = (TypeObj)OBJ   .dual();    // alloc, but object type is unknown (either struct or array)
  static final TypeObj[] TYPES = new TypeObj[]{OBJ,ISUSED,UNUSED,XOBJ};

  @Override boolean is_display() { return false; }
  @SuppressWarnings("unchecked")
  @Override protected O xdual() { return (O)new TypeObj(TOBJ,_name,!_any,!_use,!_esc); }
  @Override protected Type xmeet( Type t ) {
    if( !(t instanceof TypeObj) ) return ALL;
    assert this!=t; // already handled
    TypeObj to = (TypeObj)t;
    boolean esc = _esc|to._esc;
    if( _any ) {                // 'this' is high
      if( _use && t == UNUSED ) return XOBJ.make_from_esc(esc);
      return to.make_from_esc(esc); // Above all 't', so return 't' with esc
    }
    // 'this' is low
    if( !_use && t == ISUSED ) return ISUSED.make_from_esc(esc);
    return this.make_from_esc(esc);
  }
  @SuppressWarnings("unchecked")
  public O make_from_esc(boolean esc) { return _esc==esc ? (O)this : make_from_esc_impl(esc); }
  @SuppressWarnings("unchecked")
  protected O make_from_esc_impl(boolean esc) { return (O)make(_name,_any,_use,esc);  }
      
  // Update (approximately) the current TypeObj.  Merges fields.
  public TypeObj update(byte fin, String fld, Type val) { return this; }
  // Exact object update.  Replaces fields.
  public TypeObj st    (byte fin, String fld, Type val) { return this; }

  @Override public boolean above_center() { return _any; }
  @Override public boolean may_be_con() { return _any; }
  @Override public boolean is_con() { return false; }
  @Override public boolean must_nil() { return false; }
  @Override public boolean  may_nil() { return false; }
  @Override void walk( Predicate<Type> p ) { p.test(this); }
  // Widen (loss info), to make it suitable as the default function memory.
  // Must be monotonic, as CallEpiNode.value() uses this.
  public TypeObj crush() { return this; }
}
