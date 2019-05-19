package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;

import java.util.Arrays;
import java.util.BitSet;

/**
   Memory type; the state of all of memory; memory edges order memory ops.
   Produced at the program start, consumed by all function calls, consumed be
   Loads, consumed and produced by Stores.  Can be broken out in the "equiv-
   alence class" (Alias#) model of memory over a bulk memory to allow more fine
   grained knowledge.  Memory is accessed via Alias#s, where all TypeObjs in an
   Alias class are Meet together as an approximation.

   Conceptually, each alias# represents an infinite set of pointers - broken
   into equivalence classes.  We can split such a class in half - some pointers
   will go left and some go right, and where we can't tell we'll use both sets.
   Any alias set is a tree-like nested set of sets bottoming out in individual
   pointers.  The types are conceptually unchanged if we start using e.g. 2
   alias#s instead of 1 everywhere - we've just explicitly named the next layer
   in the tree-of-sets.

   Split an existing alias# in half, such that some ptrs point to one half or
   the other, and most point to either (or both).  Basically find all
   references to alias#X and add a new alias#Y paired with X - making all
   alias types use both equally.  Leave the base constructor of an X alias
   (some NewNode) alone - it still produces just an X.  The Node calling
   split_alias gets Y alone, and the system as a whole makes a conservative
   approximation that {XY} are always confused.  Afterwards we can lift the
   types to refine as needed.

   During iter()/pessimistic-GVN we'll have ptrs to a single New which splits -
   and this splits the aliases; repeated splitting induces a tree.  Some ptrs
   to the tree-root will remain, and represent conservative approximation as
   updates to outputs from all News.  We'll also have sharper direct ptrs
   flowing out, pointing to only results from a single New.  At the opto()
   point we'll not have any more confused types.

   Memory is supposed to be everywhere precise - but an "all-memory" notion is
   used to handle the worse-case from e.g. all unknown calls.  Really the worse
   a Call can be is to "leak" all aliases that come in to the the call - but we
   need a convenient Bottom type.  Missing aliases default to TypeObj.

   CNC - Observe that the alias Trees on Fields applies to Indices on arrays as
   well - if we can group indices in a tree-like access pattern (obvious one
   being All vs some Constants).
*/
public class TypeMem extends Type<TypeMem> {

  private boolean _any;

  // Mapping from alias#s to the current known alias state
  private TypeObj[] _aliases;
  
  private TypeMem  (boolean any, TypeObj[] aliases) { super(TMEM); init(any,aliases); }
  private void init(boolean any, TypeObj[] aliases) {
    super.init(TMEM);
    _any = any;
    _aliases = aliases;
    assert check();
  }
  // False if not 'tight' (no trailing null pairs) or any matching pairs (should
  // collapse to their parent) or any mixed parent/child.
  private boolean check() {
    TypeObj to = _any ? TypeObj.XOBJ : TypeObj.OBJ;
    TypeObj[] as = _aliases;
    if( as.length == 0 ) return true;
    if( ((as.length)&1) == 1 ) return false; // Must be even
    if( as[0]!=null ) return false; // null is null is null is null...
    // No instances of default
    for( TypeObj tt : _aliases ) if( tt==to ) return false;
    
    // Look at the 'parent' and both 'children'
    for( int i=1; i<(as.length>>1); i++ ) {
      int j=i<<1;               // Children
      if( as[i] == null ) {     // Parent is null
        // Illegal for both children to be equal and not-null (can roll up otherwise).
        if( as[j]==as[j+1] && as[j]!=null ) return false;
      } else {                  // Parent not-null; children must be null
        if( j < as.length && (as[j]!=null || as[j+1] != null) ) return false;
      }
    }
    return _aliases[_aliases.length-2] != null || _aliases[_aliases.length-1] != null;
  }
  @Override int compute_hash() {
    int hash = TMEM + (_any?1:0);
    for( TypeObj obj : _aliases )  if( obj != null )  hash += obj._hash;
    return hash;
  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeMem) ) return false;
    TypeMem tf = (TypeMem)o;
    if( _any != tf._any || _aliases.length != tf._aliases.length ) return false;
    for( int i=0; i<_aliases.length; i++ )
      if( _aliases[i] != tf._aliases[i] ) // note '==' and NOT '.equals()'
        return false;
    return true;
  }
  // Never part of a cycle, so the normal check works
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( BitSet dups ) {
    SB sb = new SB();
    sb.p("[").p(_any?"any,":"");
    for( int i=0; i<_aliases.length; i++ )
      if( _aliases[i] != null )
        sb.p(i).p("#:").p(_aliases[i].toString()).p(",");
    return sb.p("]").toString();
  }
                
  // Alias-at.  Walks up the tree to parent aliases as needed.
  public TypeObj at0(long alias) {
    while( alias>0 ) {
      if( alias < _aliases.length && _aliases[(int)alias]!=null )
        return _aliases[(int)alias];
      alias>>=1;
    }
    // Rolled off the top, it is the default
    return _any ? TypeObj.XOBJ : TypeObj.OBJ;
  }
  
  private static TypeMem FREE=null;
  @Override protected TypeMem free( TypeMem ret ) { _aliases=null; FREE=this; return ret; }
  private static TypeMem make(boolean any, TypeObj[] aliases) {
    TypeMem t1 = FREE;
    if( t1 == null ) t1 = new TypeMem(any,aliases);
    else { FREE = null;       t1.init(any,aliases); }
    TypeMem t2 = (TypeMem)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  // Precise single alias
  public static TypeMem make(long alias, TypeObj oop ) {
    long len = (alias|1)+1;      // Round up to even pairs
    assert 0 <= len && len < (1<<20); // Time to change data structures!!!
    TypeObj[] as = new TypeObj[(int)len];
    as[(int)alias] = oop;
    return make(false,as);
  }

  // Canonicalize memory before making
  static TypeMem make0( boolean any, TypeObj[] objs ) {
    // Remove elements redundant with the default value
    TypeObj def = any ? TypeObj.XOBJ : TypeObj.OBJ;
    int len = objs.length;
    for( int i=0; i<len; i++ )  if( objs[i]==def )  objs[i]=null;
    // Clean out pairs
    for( int i=2; i<(len&-2); i+=2 ) // Limit 'i' to even/odd pairs
      if( objs[i]!=null && objs[i]==objs[i+1] ) { // matching pair?
        objs[i>>1] = objs[i];                     // roll up the pair to parent
        objs[i]=objs[i+1]=null;
      }
    // Remove trailing nulls
    while( len > 0 && objs[len-1]==null ) len--;
    len = (len+1)&-2;           // Round to pairs
    if( len < objs.length ) objs = Arrays.copyOf(objs,len); // trim length
    return make(any,objs);
  }

  public  static final TypeMem MEM = make(false,new TypeObj[0]);
  public  static final TypeMem XMEM = MEM.dual();
          static final TypeMem MEM_STR = make(BitsAlias.STR_alias,TypeStr.STR);
          static final TypeMem MEM_ABC = make(TypeStr.ABC_alias,TypeStr.ABC);
  static final TypeMem[] TYPES = new TypeMem[]{MEM,MEM_STR};

  // All mapped memories remain, but each memory flips internally.
  @Override protected TypeMem xdual() {
    TypeObj[] oops = new TypeObj[_aliases.length];
    for(int i=0; i<_aliases.length; i++ )
      if( _aliases[i] != null )
        oops[i] = (TypeObj)_aliases[i].dual();
    return new TypeMem(!_any,oops);
  }
  @Override protected Type xmeet( Type t ) {
    if( t._type != TMEM ) return ALL; //
    TypeMem tf = (TypeMem)t;

    // Meet of default values, meet of element-by-element.
    int len = Math.max(_aliases.length,tf._aliases.length);
    TypeObj[] objs = new TypeObj[len];
    for( int i=0; i<len; i++ )
      if( (i<   _aliases.length &&    _aliases[i] != null) ||
          (i<tf._aliases.length && tf._aliases[i] != null) ) // short-cut for both null
        objs[i] = (TypeObj)at0(i).meet(tf.at0(i));           // meet element-by-element
    return make0(_any&tf._any,objs);
  }

  // Meet of all possible loadable values
  public TypeObj ld( TypeMemPtr ptr ) {
    throw com.cliffc.aa.AA.unimpl();
    //boolean any = ptr.above_center();
    //TypeObj obj = TypeObj.OBJ;
    //if( !any ) obj = (TypeObj)TypeObj.OBJ.dual();
    //for( int alias : ptr._aliases ) {
    //  TypeObj x = at0(alias);
    //  obj = (TypeObj)(any ? obj.join(x) : obj.meet(x));
    //}
    //return obj;
  }

  // Meet of all possible storable values, after updates
  public TypeMem st( TypeMemPtr ptr, String fld, int fld_num, Type val ) {
    assert val.isa_scalar();
    //TypeObj[] objs = new TypeObj[_aliases.length];
    //for( int alias : ptr._aliases )
    //  objs[alias] = at0(alias).update(fld,fld_num,val);
    //return make0(_any,objs);
    throw com.cliffc.aa.AA.unimpl();
  }

  // Merge two memories with no overlaps.  This is similar to a st(), except
  // updating an entire Obj not just a field, and not a replacement.  The
  // given memory is precise - the _any field is ignorable.
  public TypeMem merge( TypeMem mem ) {
    // Check no overlap
    int  len =     _aliases.length;
    int mlen = mem._aliases.length;
    for( int i=0; i<mlen; i++ ) {
      if( mem._aliases[i]==null ) continue;
      assert i >= len || _aliases[i]==null || _aliases[i]==mem._aliases[i];
    }
    TypeObj[] objs = Arrays.copyOf(_aliases,Math.max(len,mlen));
    for( int i=0; i<mlen; i++ )
      if( mem._aliases[i]!=null)
        objs[i] = mem._aliases[i];
    return make0(_any,objs);
  }
  
  @Override public boolean above_center() { return _any; }
  @Override public boolean may_be_con()   { return false;}
  @Override public boolean is_con()       { return false;}
  @Override public boolean must_nil() { return false; } // never a nil
  @Override Type not_nil() { return this; }
}
