package com.cliffc.aa.type;

import com.cliffc.aa.AA;
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
  
  // Mapping from alias#s to the current known alias state.  Slot 0 is
  // reserved, and TypeMem is never a nil.  Slot#1 is the Parent-Of-All
  // aliases, and is the default value.  Default values are replaced with null
  // - a tad easier to debug, but no other real reason.
  private TypeObj[] _aliases;
  
  private TypeMem  (TypeObj[] aliases) { super(TMEM); init(aliases); }
  private void init(TypeObj[] aliases) {
    super.init(TMEM);
    _aliases = aliases;
    assert check();
  }
  // False if not 'tight' (no trailing null pairs) or any matching pairs (should
  // collapse to their parent) or any mixed parent/child.
  private boolean check() {
    TypeObj[] as = _aliases;
    if( as.length == 0 ) return true;
    if( as[0]!=null ) return false;          // Slot 0 reserved
    if( as[1]!=TypeObj.OBJ && as[1]!=TypeObj.XOBJ && as[1] != null )
      return false;             // Only 2 choices
    if( as.length==2 ) return true; // Trivial all of memory
    // "tight" - something in the last slot
    if( _aliases[_aliases.length-1] == null ) return false;

    // If the parent is set, it is the default and no child should have the
    // same type as the default.  If the parent is closed and all children are
    // set, then the parent is not needed; if all children are the same they
    // can be replaced by the closed parent.
    for( int i=as.length-1; i>=1; i-- ) {
      TypeTree par = BitsAlias.TREES.at(i), x=par._par;
      assert par._idx==i;
      if( par._kids==null ) continue; // Not a parent
      TypeObj part = as[i];           // Parent type
      while( part == null ) {
        assert x._kids != null;
        part = as[x._idx];
        x = x._par;
      }
      int uidx = -1;                  // unique type index
      for( int j=0; j<par._kids._len; j++ ) {
        int kidx = par._kids.at(j)._idx;
        TypeObj kidt = kidx < as.length ? as[kidx] : null;
        if( kidt == null ) continue;   // Kid not reporting
        if( kidt==part ) return false; // Kid should be shadowed by parent
        if( uidx == -1 ) uidx = kidt._uid;      // Gather unique kid type
        else if( uidx != kidt._uid ) uidx = -2; // Different kid types
      }
      if( par.closed() && uidx== -2 ) return false; // All equal kid types shadow parent
    }
    return true;
  }
  @Override int compute_hash() {
    int hash = TMEM;
    for( TypeObj obj : _aliases )  if( obj != null )  hash += obj._hash;
    return hash;
  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeMem) ) return false;
    TypeMem tf = (TypeMem)o;
    if( _aliases.length != tf._aliases.length ) return false;
    for( int i=0; i<_aliases.length; i++ )
      if( _aliases[i] != tf._aliases[i] ) // note '==' and NOT '.equals()'
        return false;
    return true;
  }
  // Never part of a cycle, so the normal check works
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( BitSet dups ) {
    if( this== MEM ) return "[mem]";
    if( this==XMEM ) return "[~mem]";
    SB sb = new SB();
    sb.p("[");
    for( int i=1; i<_aliases.length; i++ )
      if( _aliases[i] != null )
        sb.p(i).p("#:").p(_aliases[i].toString()).p(",");
    return sb.p("]").toString();
  }
                
  // Alias-at.  Walks up the tree to parent aliases as needed.  Always hits on
  // _aliases[1], and now never returns a null.  Prior versions go back-n-forth
  // on whether or not this call returns a null.
  public TypeObj at0(int alias) {
    while( alias >= _aliases.length || _aliases[alias]==null )
      alias = BitsAlias.TREES.at(alias)._par._idx; // Walk up the alias tree
    return _aliases[alias];
  }
  // Alias-at, but defaults to "XOBJ" for easy meet() calls.
  // Never returns a null.
  public TypeObj at(int alias) {
    TypeObj obj = at0(alias);
    return obj==null ? TypeObj.XOBJ : obj;
  }
  
  private static TypeMem FREE=null;
  @Override protected TypeMem free( TypeMem ret ) { _aliases=null; FREE=this; return ret; }
  private static TypeMem make(TypeObj[] aliases) {
    TypeMem t1 = FREE;
    if( t1 == null ) t1 = new TypeMem(aliases);
    else { FREE = null;       t1.init(aliases); }
    TypeMem t2 = (TypeMem)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  // Canonicalize memory before making.  Unless specified, the default memory is "dont care"
  static TypeMem make0( TypeObj[] as ) {
    int len = as.length;
    if( as[1]==null ) as[1] = TypeObj.XOBJ; // Default memory is "dont care"
    if( len == 2 ) return make(as);
    // If the parent is set, it is the default and no child should have the
    // same type as the default.  If the parent is closed and all children are
    // set, then the parent is not needed; if all children are the same they
    // can be replaced by the closed parent.
    for( int i=as.length-1; i>=1; i-- ) {
      TypeTree par = BitsAlias.TREES.at(i);
      if( par._kids==null ) continue; // Not a parent
      TypeObj part = as[i];           // Parent type
      for( TypeTree x = par._par; part==null; x = x._par )
        part = as[x._idx];
      
      TypeObj utype = null;     // Unique kid type
      for( int j=0; j<par._kids._len; j++ ) {
        int kidx = par._kids.at(j)._idx;
        TypeObj kidt = kidx < as.length ? as[kidx] : null;
        if( kidt==part ) as[kidx]=null;  // Kid is shadowed by parent
        if( kidt==null ) kidt=part;      // Kid not reporting, use parent type
        
        if( utype == null ) utype = kidt;       // Gather unique kid type
        else if( utype != kidt ) utype = as[1]; // Different kid types
      }
      if( par.closed() && utype != as[1] && utype != null )
        throw AA.unimpl();      // Parent is closed and null and all kids are equal
    }
    
    // Remove trailing nulls; make the array "tight"
    while( as[len-1] == null ) len--;
    if( as.length!=len ) as = Arrays.copyOf(as,len);

    return make(as);
  }

  // Precise single alias.  Other aliases are "dont care".  Nil not allowed.
  public static TypeMem make(int alias, TypeObj oop ) {
    TypeObj[] as = new TypeObj[alias+1];
    as[BitsAlias.ALL._idx] = TypeObj.XOBJ; // Everything else is "dont care"
    as[alias] = oop;
    return make(as);
  }

  public  static final TypeMem MEM = make(new TypeObj[]{null,TypeObj.OBJ}); // Every alias filled with something
  public  static final TypeMem XMEM = MEM.dual(); // Every alias filled with anything
  public  static final TypeMem EMPTY_MEM = XMEM; //make(new TypeObj[0]); // Tried no-memory-vs-XOBJ-memory
          static final TypeMem MEM_STR = make(BitsAlias.STR._idx,TypeStr.STR);
          static final TypeMem MEM_ABC = make(BitsAlias.STR._idx,TypeStr.ABC);
  static final TypeMem[] TYPES = new TypeMem[]{MEM,MEM_STR};

  // All mapped memories remain, but each memory flips internally.
  @Override protected TypeMem xdual() {
    TypeObj[] oops = new TypeObj[_aliases.length];
    for(int i=0; i<_aliases.length; i++ )
      if( _aliases[i] != null )
        oops[i] = (TypeObj)_aliases[i].dual();
    return new TypeMem(oops);
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
        objs[i] = (TypeObj)at(i).meet(tf.at(i));             // meet element-by-element
    return make0(objs);
  }

  // Meet of all possible loadable values
  public TypeObj ld( TypeMemPtr ptr ) {
    boolean any = ptr.above_center();
    TypeObj obj = any ? TypeObj.OBJ : TypeObj.XOBJ;
    for( int alias : ptr._aliases ) {
      TypeObj x = at0(alias);
      obj = (TypeObj)(any ? obj.join(x) : obj.meet(x));
    }
    return obj;
  }

  // Meet of all possible storable values, after updates
  public TypeMem st( TypeMemPtr ptr, String fld, int fld_num, Type val ) {
    assert val.isa_scalar();
    //TypeObj[] objs = new TypeObj[_aliases.length];
    //for( int alias : ptr._aliases )
    //  objs[alias] = at0(alias).update(fld,fld_num,val);
    //return make0(_any,objs);
    throw AA.unimpl();
  }

  // Merge two memories with no overlaps.  This is similar to a st(), except
  // updating an entire Obj not just a field, and not a replacement.  The
  // given memory is precise.
  public TypeMem merge( TypeMem mem ) {
    // Given memory must be "skinny", only a single alias.
    TypeObj[] ms = mem._aliases;
    int mlen = ms.length;
    int alias = mlen-1;
    TypeObj obj = ms[alias];
    assert alias >= 2 && obj != null;
    for( int i=2; i<alias; i++ )  assert ms[i]==null;

    // Check no overlap or conflicts
    assert at0(alias) == _aliases[1]; // Alias about-to-be-stomped is the default
    TypeObj[] objs = Arrays.copyOf(_aliases,Math.max(_aliases.length,alias+1));
    objs[alias]=obj;
    return make0(objs);
  }
  
  @Override public boolean above_center() { return _aliases[1].above_center(); }
  @Override public boolean may_be_con()   { return false;}
  @Override public boolean is_con()       { return false;}
  @Override public boolean must_nil() { return false; } // never a nil
  @Override Type not_nil() { return this; }
  // Dual, except keep TypeMem.XOBJ as high for starting GVNGCM.opto() state.
  @Override public TypeMem startype() {
    TypeObj[] oops = new TypeObj[_aliases.length];
    for(int i=0; i<_aliases.length; i++ )
      if( _aliases[i] != null )
        oops[i] = _aliases[i].startype();
    return make0(oops);
  }
}
