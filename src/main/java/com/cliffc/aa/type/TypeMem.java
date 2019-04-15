package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;

// Memory type; the state of all of memory; memory edges order memory ops.
// Produced at the program start, consumed by all function calls, consumed be
// Loads, consumed and produced by Stores.  Can be broken out in the "equiv-
// alence class" (Alias#) model of memory over a bulk memory to allow more fine
// grained knowledge.  Memory is accessed via Alias#s, where all TypeObjs in an
// Alias class are Meet together as an approximation.
public class TypeMem extends Type<TypeMem> {
  // Mapping from alias#s to the current known alias state
  private TypeObj[] _aliases;
  // The "default" infinite mapping.  Everything past _aliases.length or null
  // maps to the default instead.  If the default is null, then the aliasing is
  // exact, and trying to read null is an error.
  private TypeObj _def;
  
  private TypeMem  (TypeObj def, TypeObj[] aliases ) { super(TMEM); init(def,aliases); }
  private void init(TypeObj def, TypeObj[] aliases ) {
    super.init(TMEM);
    _def = def;
    _aliases = aliases;
    assert check(def,aliases);
  }
  // "tight": no extra instances of default
  private static boolean check(TypeObj def, TypeObj[] aliases ) {
    if( def != null )
      for( TypeObj obj : aliases )
        if( obj==def )
          return false; // Extra instances of default; messes up canonical rep for hash-cons
    return aliases.length==0 || aliases[aliases.length-1] != def;
  }
  @Override public int hashCode( ) {
    return super.hashCode() + Arrays.hashCode(_aliases) + _def.hashCode();
  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeMem) ) return false;
    TypeMem tf = (TypeMem)o;
    if( _def != tf._def || _aliases.length != tf._aliases.length ) return false;
    for( int i=0; i<_aliases.length; i++ )
      if( _aliases[i] != tf._aliases[i] ) // note '==' and NOT '.equals()'
        return false;
    return true;
  }
  // Never part of a cycle, so the normal check works
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( BitSet dups ) {
    SB sb = new SB();
    sb.p("[");
    if( _def != TypeObj.OBJ )
      sb.p("mem#:").p(_def.toString()).p(",");
    for( int i=0; i<_aliases.length; i++ )
      if( _aliases[i] != null )
        sb.p(i).p("#:").p(_aliases[i].toString()).p(",");
    return sb.p("]").toString();
  }
  // Alias must exist
  public TypeObj at0(int alias) {
    if( alias >= _aliases.length ) return _def;
    TypeObj obj = _aliases[alias];
    return obj==null ? _def : obj;
  }
  
  private static TypeMem FREE=null;
  @Override protected TypeMem free( TypeMem ret ) { _aliases=null; FREE=this; return ret; }
  private static TypeMem make( TypeObj def, TypeObj[] aliases ) {
    TypeMem t1 = FREE;
    if( t1 == null ) t1 = new TypeMem(def,aliases);
    else { FREE = null;       t1.init(def,aliases); }
    TypeMem t2 = (TypeMem)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  // Precise single alias
  public static TypeMem make(int alias, TypeObj oop ) {
    assert oop!=null;
    TypeObj[] oops = new TypeObj[alias+1];
    oops[alias] = oop;
    return make(TypeObj.OBJ,oops);
  }
  // Canonicalize memory before making
  static TypeMem make0( TypeObj def, TypeObj[] objs ) {
    // Remove elements redundant with the default value
    int len = objs.length;
    for( int i=0; i<len; i++ )  if( objs[i]==def )  objs[i]=null;
    while( len > 0 && objs[len-1]==null ) len--;
    if( len < objs.length ) objs = Arrays.copyOf(objs,len);
    return make(def,objs);
  }

  public  static final TypeMem MEM = make(TypeObj.OBJ,new TypeObj[0]);
  public  static final TypeMem XMEM = MEM.dual();
  public  static final TypeMem MEM_STR = make(TypeStr.STR_alias,TypeStr.STR);
  public  static final TypeMem MEM_ABC = make(TypeStr.ABC_alias,TypeStr.ABC);
  static final TypeMem[] TYPES = new TypeMem[]{MEM,MEM_STR};

  // All mapped memories remain, but each memory flips internally.
  @Override protected TypeMem xdual() {
    TypeObj[] oops = new TypeObj[_aliases.length];
    for(int i=0; i<_aliases.length; i++ )
      if( _aliases[i] != null )
        oops[i] = (TypeObj)_aliases[i].dual();
    return new TypeMem((TypeObj)_def.dual(), oops);
  }
  @Override protected Type xmeet( Type t ) {
    if( t._type != TMEM ) return ALL; //
    TypeMem tf = (TypeMem)t;
    // Meet of default values, meet of element-by-element.
    TypeObj def = (TypeObj)_def.meet(tf._def);
    int len = Math.max(_aliases.length,tf._aliases.length);
    TypeObj[] objs = new TypeObj[len];
    for( int i=0; i<len; i++ )
      objs[i] = (TypeObj)at0(i).meet(tf.at0(i));
    return make0(def,objs);
  }

  // Meet of all possible loadable values
  public TypeObj ld( TypeMemPtr ptr ) {
    boolean any = ptr.above_center();
    TypeObj obj = TypeObj.OBJ;
    if( !any ) obj = (TypeObj)TypeObj.OBJ.dual();
    for( int alias : ptr._aliases ) {
      TypeObj x = at0(alias);
      obj = (TypeObj)(any ? obj.join(x) : obj.meet(x));
    }
    return obj;
  }

  // Meet of all possible storable values, after updates
  public TypeMem st( TypeMemPtr ptr, String fld, int fld_num, Type val ) {
    assert val.isa_scalar();
    TypeObj[] objs = new TypeObj[_aliases.length];
    for( int alias : ptr._aliases )
      objs[alias] = at0(alias).update(fld,fld_num,val);
    return make0(_def,objs);
  }

  // Merge two memories with no overlaps.  This is similar to a st(), except
  // updating an entire Obj not just a field, and not a replacement.  The
  // given memory is precise - the default field is ignorable.
  public TypeMem merge( TypeMem mem ) {
    // Check no overlap
    int  len =     _aliases.length;
    int mlen = mem._aliases.length;
    for( int i=0; i<mlen; i++ ) {
      if( mem._aliases[i]==null ) continue;
      assert i >= len || _aliases[i]==null;
    }
    TypeObj[] objs = Arrays.copyOf(_aliases,Math.max(len,mlen));
    for( int i=0; i<mlen; i++ )
      if( mem._aliases[i]!=null)
        objs[i] = mem._aliases[i];
    return make(_def,objs);
  }
  
  @Override public boolean above_center() { return _def.above_center(); }
  @Override public boolean may_be_con()   { return false;}
  @Override public boolean is_con()       { return false;}
  @Override public boolean must_nil() { return false; } // never a nil
  @Override Type not_nil() { return this; }

  /** See giant discussion in {@link Bits#split_alias(int, HashMap)}.  Change
   *  all instances of TypeMem.at0(a1) to include a2 - updating in-place and
   *  changing the hash as appropriate. */
  static void split_alias( int a1, int a2 ) {
    ArrayList<TypeMem> tms = new ArrayList<>();
    INTERN.entrySet().removeIf(entry -> {
        Type t = entry.getKey();
        if( !(t instanceof TypeMem) ) return false;
        TypeMem tm = (TypeMem)t;
        TypeObj[] tos = tm._aliases;
        if( a1 >= tos.length ) return false; // No a1 instance
        TypeObj to = tos[a1];
        if( to==null ) return false; // a1 is the default, so is a2
        assert to != tm._def;
        tms.add(tm);                 // Must update this TypeMem and rehash
        if( a2 >= tos.length )
          tm._aliases = tos = Arrays.copyOf(tos,a2+1);
        tos[a2] = to;
        return true;
      });
    // For all updated TypeMems re-insert with new hash code
    for( TypeMem tm : tms )
      tm.retern();
  }
}
