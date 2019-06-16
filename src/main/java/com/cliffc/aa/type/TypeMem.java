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
  // Mapping from alias#s to the current known alias state.  Slot 0 is
  // reserved; TypeMem is never a nil.  Slot#1 is the Parent-Of-All aliases and
  // is the default value.  Default values are replaced with null during
  // canonicalization.
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
    // No dups of the default in slot 1
    for( int i=2; i<as.length; i++ )
      if( as[i]==as[1] )
        return false;
    return true;
  }
  @Override int compute_hash() {
    // Horrible class-loader ordering bug:
    // - TypeMem.clinit makes
    // - TypeMem.ALL which calls hashcons which calls
    // - TypeMem.compute_hash which calls
    // - BitsAlias.HASHMAKER which calls
    // - BitsAlias.clinit which splits many alias bits which calls
    // - Bits.HASHMAKER.split which looks in
    // - Type.INTERN to split all TypeMems.
    // - But TypeMem.ALL is not yet in Type.INTERN
    if( _aliases.length==2 ) return TMEM + _aliases[1]._hash;
       
    // Hash is preserved across splitting bits
    return TMEM + BitsAlias.HASHMAKER.compute_hash(_aliases);
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
    sb.p('[');
    for( int i=1; i<_aliases.length; i++ )
      if( _aliases[i] != null )
        sb.p(i).p("#:").p(_aliases[i].toString()).p(",");
    return sb.p(']').toString();
  }
                
  // Alias-at.  Out of bounds or null uses the default.
  public TypeObj at(int alias) {
    TypeObj obj = alias < _aliases.length ? _aliases[alias] : null;
    return obj==null ? _aliases[1] : obj;
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
    if( as[1]==null ) as[1] = TypeObj.XOBJ; // Default memory is "dont care"
    int len = as.length;
    if( len == 2 ) return make(as);
    // No dups of default in slot 1
    for( int i=2; i<len; i++ )
      if( as[i]==as[1] )
        as[i]=null;
    // Remove trailing nulls; make the array "tight"
    while( as[len-1] == null ) len--;
    if( as.length!=len ) as = Arrays.copyOf(as,len);

    return make(as);
  }

  // Precise single alias.  Other aliases are "dont care".  Nil not allowed.
  public static TypeMem make(int alias, TypeObj oop ) {
    TypeObj[] as = new TypeObj[alias+1];
    as[1] = TypeObj.XOBJ; // Everything else is "dont care"
    as[alias] = oop;
    return make0(as);
  }
  public static TypeMem make(BitsAlias bits, TypeObj oop ) {
    TypeObj[] as = new TypeObj[bits.max()+1];
    as[BitsAlias.ALL] = TypeObj.XOBJ; // Everything else is "dont care"
    for( int b : bits )
      as[b] = oop;
    return make0(as);
  }

  public static final TypeMem  MEM; // Every alias filled with something
  public static final TypeMem XMEM; // Every alias filled with anything
  public static final TypeMem EMPTY_MEM;
         static final TypeMem MEM_STR;
         static final TypeMem MEM_ABC;
  static {
    MEM  = make(new TypeObj[]{null,TypeObj. OBJ}); // Every alias filled with something
    XMEM = make(new TypeObj[]{null,TypeObj.XOBJ}); // Every alias filled with anything
    EMPTY_MEM = XMEM; //make(new TypeObj[0]); // Tried no-memory-vs-XOBJ-memory
    // This next init will trigger BitsAlias to build all inital aliases
    // splitting all the strings.
    MEM_STR = make(BitsAlias.STRBITS,TypeStr.STR);
    MEM_ABC = make(TypeStr.ABC.get_alias(),TypeStr.ABC);
    assert MEM_ABC._aliases.length==BitsAlias.HASHMAKER.last_split()+1;
  }
  static final TypeMem[] TYPES = new TypeMem[]{MEM,MEM_STR,MEM_ABC};

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
    for( int i=1; i<len; i++ )
      objs[i] = (TypeObj)at(i).meet(tf.at(i)); // meet element-by-element
    return make0(objs);
  }

  // Part of a Smalltalk-ish "becomes" operation on splitting alias Bits.
  // See big comment in Bits.java.
  void split_bit( int paridx, int newidx ) {
    if( paridx == 1 ) return; // New index splits from the default, do nothing.
    if( paridx >= _aliases.length || _aliases[paridx]==null ) return;
    if( newidx >= _aliases.length )
      _aliases = Arrays.copyOf(_aliases,newidx+1);
    _aliases[newidx] = _aliases[paridx];
  }
  
  // Meet of all possible loadable values
  public TypeObj ld( TypeMemPtr ptr ) {
    boolean any = ptr.above_center();
    TypeObj obj = any ? TypeObj.OBJ : TypeObj.XOBJ;
    for( int alias : ptr._aliases ) {
      if( alias != 0 ) {        // nil on a JOIN is ignored, on a MEET is failure
        TypeObj x = at(alias);
        obj = (TypeObj)(any ? obj.join(x) : obj.meet(x));
      }
    }
    return obj;
  }

  // Meet of all possible storable values, after updates
  public TypeMem st( TypeMemPtr ptr, String fld, int fld_num, Type val ) {
    assert val.isa_scalar();
    TypeObj[] objs = Arrays.copyOf(_aliases,Math.max(_aliases.length,ptr._aliases.max()+1));
    for( int alias : ptr._aliases )
      objs[alias] = at(alias).update(fld,fld_num,val);
    return make0(objs);
  }

  // Merge two memories with no overlaps.  This is similar to a st(), except
  // updating an entire Obj not just a field, and not a replacement.  The given
  // memory is generally precise, except after a alias split and before any
  // inputs are re-value()'d.
  public TypeMem merge( TypeMem mem ) {
    TypeObj[] objs = Arrays.copyOf(_aliases,Math.max(_aliases.length,mem._aliases.length));
    for( int i=2; i<mem._aliases.length; i++ )
      if( mem._aliases[i] != null )
        objs[i] = mem._aliases[i];
    return make0(objs);
  }

  // Return is a Tuple of TypeMem's, all with unrelated aliases.  The slot0
  // is the default and is same as this (except that the named _aliases
  // are going to be overwritten).  All others are in alias order, but not
  // matching alias#, and contain a TypeMem with just that alias.
  public TypeTuple split(int[] aliases) {
    TypeMem[] ts = new TypeMem[aliases.length+1];
    ts[0] = this;
    for( int i=0; i<aliases.length; i++ )
      ts[i+1] = TypeMem.make(aliases[i],at(aliases[i]));
    return TypeTuple.make0(false,ts);
  }
  
  @Override public boolean above_center() { return _aliases[1].above_center(); }
  @Override public boolean may_be_con()   { return false;}
  @Override public boolean is_con()       { return false;}
  @Override public boolean must_nil() { return false; } // never a nil
  @Override Type not_nil() { return this; }
  // Dual, except keep TypeMem.XOBJ as high for starting GVNGCM.opto() state.
  @Override public TypeMem startype() {
    if( this==XMEM ) return XMEM;
    TypeObj[] oops = new TypeObj[_aliases.length];
    for(int i=0; i<_aliases.length; i++ )
      if( _aliases[i] != null )
        oops[i] = _aliases[i].startype();
    return make0(oops);
  }
  @Override boolean hasBits(BitSet bs) {
    if( bs.get(_uid) ) return false;
    bs.set(_uid);
    for( Type t: _aliases )
      if( t!=null && t.hasBits(bs) )
        return true;
    return false;
  }
}
