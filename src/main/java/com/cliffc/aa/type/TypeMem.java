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
  // CNC: Check rd_bar & if pass era-check use brooks-barrier version (if fail,
  // get an updated brooks-barrier version).

  // Mapping from alias#s to the current known alias state
  private TypeObj[] _aliases;
  
  private TypeMem  (boolean any, TypeObj[] aliases) { super(TMEM); init(any,aliases); }
  private void init(boolean any, TypeObj[] aliases) {
    super.init(TMEM);
    _any = any;
    _aliases = aliases;
    assert check();
  }
  // False if any bit needs to split or not "tight": no extra instances of default
  private boolean check() {
    TypeObj to = _any ? TypeObj.XOBJ : TypeObj.OBJ;
    for( int i=0; i<_aliases.length; i++ )
      if( (_aliases[i]!=null && BitsAlias.get_child(i)!=0) || _aliases[i]==to )
        return false;
    return _aliases.length==0 || _aliases[_aliases.length-1] != null;
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
    for( int i=0; i<_aliases.length; i++ ) if( _aliases[i] != null ) sb(sb,_aliases[i].toString(),i);
    return sb.p("]").toString();
  }
  // Recursively walk the split tree, and print bits.  Type is same for all
  // bits - it can only differ for new post-split types.
  private SB sb(SB sb, String sobj, int i) {
    int a0 = BitsAlias.get_child(i);
    if( a0 == 0 )  return sb.p(i).p("#:").p(sobj).p(",");
    return sb(sb(sb,sobj,a0),sobj,a0+1);  // Recursively do 2 bits
  }
                
  // Alias
  public TypeObj at0(int alias) {
    TypeObj obj = alias < _aliases.length ? _aliases[alias] : null;
    int p = BitsAlias.get_parent(alias);
    if( p != 0 && _aliases[p] != null ) {
      assert obj==null;         // not both parent and child
      return _aliases[p];       // Return parent
    }
    return obj==null ? (_any ? TypeObj.XOBJ : TypeObj.OBJ) : obj;
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
  public static TypeMem make(int alias, TypeObj oop ) {
    TypeObj[] as = new TypeObj[alias+1];
    as[alias] = oop;
    return make(false,as);
  }

  // Canonicalize memory before making
  static TypeMem make0( boolean any, TypeObj[] objs ) {
    // Remove elements redundant with the default value
    TypeObj def = any ? TypeObj.XOBJ : TypeObj.OBJ;
    int len = objs.length;
    for( int i=0; i<len; i++ )  if( objs[i]==def )  objs[i]=null;
    while( len > 0 && objs[len-1]==null ) len--;
    if( len < objs.length ) objs = Arrays.copyOf(objs,len);
    // Split any split bits
    int a0;  TypeObj obj;
    for( int i=0; i<len; i++ )
      if( (obj=objs[i])!=null && (a0=BitsAlias.get_child(i))!=0 ) {
        if( a0+2 >= objs.length ) objs = Arrays.copyOf(objs,a0+2);
        objs[i   ] = null;
        objs[a0  ] = obj;
        objs[a0+1] = obj;
      }
    return make(any,objs);
  }

  public  static final TypeMem MEM = make(false,new TypeObj[0]);
  public  static final TypeMem XMEM = MEM.dual();
          static final TypeMem MEM_STR = make(TypeStr.STR_alias,TypeStr.STR);
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
    boolean any = _any&tf._any;
    TypeObj to = any ? TypeObj.XOBJ : TypeObj.OBJ;
    for( int i=0; i<len; i++ ) {
      TypeObj obj = (TypeObj)at0(i).meet(tf.at0(i));
      objs[i] = obj==to ? null : obj; // Use null for the default, canonicalize
      // Check the read-barrier to see if either side of the meet contains
      // split-bits.
      int a0;
      if( obj!=to && (a0=BitsAlias.get_child(i))!=0 ) {
        // Do the splits now - if the split-bit has non-default values it will
        // get set again sharper.
        if( a0+2 >= objs.length ) objs = Arrays.copyOf(objs,a0+2);
        objs[i   ] = null;      // Never return the split-bit again
        objs[a0  ] = obj;
        objs[a0+1] = obj;
      }
    }
    return make0(any,objs);
  }

  // Meet of all possible loadable values
  public TypeObj ld( TypeMemPtr ptr ) {
    if(    _aliases.length < BitsAlias.MAX_SPLITS ) throw com.cliffc.aa.AA.unimpl(); // Might need to split this guy
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
    if(    _aliases.length < BitsAlias.MAX_SPLITS ) throw com.cliffc.aa.AA.unimpl(); // Might need to split this guy
    assert val.isa_scalar();
    TypeObj[] objs = new TypeObj[_aliases.length];
    for( int alias : ptr._aliases )
      objs[alias] = at0(alias).update(fld,fld_num,val);
    return make0(_any,objs);
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
