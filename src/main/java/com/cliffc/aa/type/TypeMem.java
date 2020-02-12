package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.Arrays;
import java.util.BitSet;

/**
   See also node/MemMerge.java

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

   Splitting happens during code-cloning (inlining) where we make a copy of an
   alias generator (NewNode).  Both copies are alias renumbered to child alias
   numbers from the parent.  The IR will be holding on to some copies of the
   original alias#, which is now confused with both children.  After a full
   round of gcp() this confusion will be removed.  While the confusion is not
   (yet) removed, we will have to deal with this mixture of the left child,
   right child, and parent.

   We use an "all-memory" notion to handle the worse-case from e.g. all unknown
   calls.  Really the worse a Call can be is to "leak" all aliases that come in
   to the the call (and are reachable from those) - but we need a convenient
   Bottom type.  Missing aliases default to TypeObj.

   The representation is a collection of TypeObjs indexed by alias#.  Missing
   aliases are always equal to their nearest present parent.  The root at
   alias#1 is only either OBJ or XOBJ.  Alias#0 is nil and is always missing.
   The structure is canonicalized; if a child is a dup of a parent it is
   removed (since an ask will yield the correct value from the parent).

   Child classes also contain a 'lost' bit, set if more than one instance of a
   child class can be alive at once.  It is usually set for a parent (both
   children alive at once) unless a child later dies.  It is typically set for
   NewNodes that are called repeatedly and have a long lifetime.  It is
   typically clear for closures (which are just NewNodes) which have a stack
   lifetime.  Long-lived closures will again have the bit set.  This bit
   inverts for inverted TypeObjs.

   There is no meet/join relationship between parent and child; a child can be
   precisely updated independently from the parent and other sibilings.

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

  // An alias is "lost" (or "escaped") then there may be more than 1 instance
  // alive at any one time.  There can be many instances over time (e.g.
  // standard closure stack lifetime) that are not lost and many more
  // optimizations apply.  If an alias is not lost ("captured") then it has no
  // children or is dead/~obj.  This bit inverts with inverted TypeObj.
  private TypeBits _losts;

  private TypeMem  (TypeObj[] aliases, TypeBits losts) { super(TMEM); init(aliases,losts); }
  private void init(TypeObj[] aliases, TypeBits losts) {
    super.init(TMEM);
    _aliases = aliases;
    _losts  = losts;
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
    // No dups of any parent
    for( int i=2; i<as.length; i++ ) {
      Type asi = as[i];
      if( asi != null ) {
        for( int par = BitsAlias.TREE.parent(i); par!=0; par = BitsAlias.TREE.parent(par) )
          if( as[par] == asi )
            return false;       // Dup of a parent
        // Parents are always lost (since the parent & all children co-exist).
        // Bit is inverted for inverted types.
        if( BitsAlias.is_parent(i) && (_losts.test(i) ^ !asi.above_center()) )
          return false;         // Precise, below center and has children
      }
    }

    return true;
  }
  @Override int compute_hash() {
    int sum=TMEM+_losts.hashCode();
    for( TypeObj obj : _aliases ) sum += obj==null ? 0 : obj._hash;
    return sum;
  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeMem) ) return false;
    TypeMem tf = (TypeMem)o;
    if( _aliases.length != tf._aliases.length ) return false;
    if( _losts != tf._losts ) return false;
    for( int i=0; i<_aliases.length; i++ )
      if( _aliases[i] != tf._aliases[i] ) // note '==' and NOT '.equals()'
        return false;
    return true;
  }
  // Never part of a cycle, so the normal check works
  @Override public boolean cycle_equals( Type o ) { return equals(o); }
  @Override String str( VBitSet dups ) {
    if( this==FULL ) return "[allmem]";
    if( this==EMPTY) return "[]";
    if( this== MEM ) return "[mem]";
    if( this==XMEM ) return "[~mem]";
    SB sb = new SB();
    sb.p('[');
    for( int i=1; i<_aliases.length; i++ )
      if( _aliases[i] != null )
        sb.p(i).p(_losts.test(i)?'+':'#').p(':').p(_aliases[i].toString()).p(",");
    return sb.p(']').toString();
  }

  // Alias-at.  Out of bounds or null uses the parent value.
  public TypeObj at(int alias) { return _aliases[at_idx(alias)]; }
  // Alias-at index
  public int at_idx(int alias) {
    assert alias != 0;
    while( true ) {
      if( alias < _aliases.length && _aliases[alias] != null )
        return alias;
      alias = BitsAlias.TREE.parent(alias);
    }
  }
  //
  public TypeObj[] alias2objs() { return _aliases; }
  public TypeBits losts() { return _losts; }

  // Return set of aliases.  Not even sure if this is well-defined.
  public BitsAlias aliases() {
    if( this== FULL ) return BitsAlias.NZERO;
    if( this==EMPTY ) return BitsAlias.EMPTY;
    BitsAlias bas = BitsAlias.EMPTY;
    for( int i=0; i<_aliases.length; i++ )
      if( _aliases[i]!=null && !_aliases[i].above_center() )
        bas = bas.set(i);
    return bas;
  }
  // Toss out memory state not visible from these aliases
  public TypeMem trim_to_alias(BitsAlias bas) {
    if( bas == BitsAlias.EMPTY || this==EMPTY )
      return EMPTY;                // Shortcut
    if( bas.test(1) ) return this; // Shortcut, all aliases used so no trimming
    TypeObj[] objs = new TypeObj[Math.max(bas.max()+1,_aliases.length)];
    objs[1] = TypeObj.XOBJ;
    // For every alias in the included set, include in the result (perhaps
    // reading from a parent alias).
    for( int alias : bas )
      objs[alias] = at(alias);
    // Also include any children, whose parent is included.
    for( int i=2; i<_aliases.length; i++ )
      if( _aliases[i]!=null && bas.test_recur(i) )
        { assert objs[i]==null || objs[i]==_aliases[i]; objs[i] = _aliases[i]; }
    return make0(objs,_losts);
  }

  // Recursively explore reachable aliases.
  public BitsAlias recursive_aliases( BitsAlias abs, int alias ) {
    if( abs.test_recur(alias) ) return abs; // Already walked
    abs = abs.or(alias);        // 'alias' is a reachable alias
    return at(alias).recursive_aliases(abs,this); // Plus what can be reached from the alias
  }

  private static TypeMem FREE=null;
  @Override protected TypeMem free( TypeMem ret ) { _aliases=null; FREE=this; return ret; }
  private static TypeMem make(TypeObj[] aliases, TypeBits losts) {
    TypeMem t1 = FREE;
    if( t1 == null ) t1 = new TypeMem(aliases,losts);
    else { FREE = null;       t1.init(aliases,losts); }
    TypeMem t2 = (TypeMem)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  // Canonicalize memory before making.  Unless specified, the default memory is "dont care"
  public static TypeMem make0( TypeObj[] as, TypeBits losts ) {
    if( as[1]==null ) as[1] = TypeObj.XOBJ; // Default memory is "dont care"
    int len = as.length;
    if( len == 2 ) return make(as,losts);
    // No dups of a parent
    for( int i=1; i<as.length; i++ )
      if( as[i] != null )
        for( int par = BitsAlias.TREE.parent(i); par!=0; par = BitsAlias.TREE.parent(par) )
          if( as[par] == as[i] )
            { as[i] = null; break; }
    // Remove trailing nulls; make the array "tight"
    while( as[len-1] == null ) len--;
    if( as.length!=len ) as = Arrays.copyOf(as,len);
    
    // Parents are always lost (since the parent & all children co-exist).
    // Bit is inverted for inverted types.
    for( int i=1; i<as.length; i++ )
      if( as[i] != null )
        if( BitsAlias.is_parent(i) )
          losts = as[i].above_center() ? losts.clr(i) : losts.set(i);

    return make(as,losts);
  }

  // Precise single alias.  Other aliases are "dont care".  Nil not allowed.
  // Both "dont care" and this alias are exact.
  public static TypeMem make(int alias, TypeObj oop ) {
    TypeObj[] as = new TypeObj[alias+1];
    as[1] = TypeObj.XOBJ;
    as[alias] = oop;
    return make0(as,TypeBits.EMPTY);
  }
  //public static TypeMem make(BitsAlias bits, TypeObj oop ) {
  //  TypeObj[] as = Arrays.copyOf(MEM._aliases,Math.max(MEM._aliases.length,bits.max()+1));
  //  for( int b : bits )  as[b] = oop;
  //  return make0(as);
  //}

  public static final TypeMem FULL; // Every alias filled with something
  public static final TypeMem EMPTY;// Every alias filled with anything
  public static final TypeMem  MEM; // FULL, except lifts REC, arrays, STR
  public static final TypeMem XMEM; //
  public static final TypeMem  MEM_CLN; // Clean (not modified) versions
  public static final TypeMem MEM_ABC, MEM_STR;
  static {
    // All memory, all aliases, holding anything.
    FULL = make(new TypeObj[]{null,TypeObj.OBJ},TypeBits.FULL);
    EMPTY= FULL.dual();

    // All memory.  Includes breakouts for all structs and all strings.
    // Triggers BitsAlias.<clinit> which makes all the initial alias splits.
    // Not currently including closures
    TypeObj[] tos = new TypeObj[Math.max(BitsAlias.TUPLE,BitsAlias.STR)+1];
    tos[BitsAlias.ALL] = TypeObj.OBJ;
    tos[BitsAlias.TUPLE]=TypeStruct.ALLSTRUCT;
    tos[BitsAlias.STR] = TypeStr.STR; // TODO: Proxy for all-arrays
    MEM  = make(tos,TypeBits.FULL);
    XMEM = MEM.dual();

    TypeObj[] tcs = new TypeObj[Math.max(BitsAlias.TUPLE,BitsAlias.STR)+1];
    tcs[BitsAlias.ALL] = TypeObj.OBJ;
    tcs[BitsAlias.TUPLE]=TypeStruct.ALLSTRUCT_CLN;
    tcs[BitsAlias.STR] = TypeStr.STR; // TODO: Proxy for all-arrays
    MEM_CLN = make(tcs,TypeBits.FULL);

    TypeObj[] tss = new TypeObj[BitsAlias.STR+1];
    tss[1] = TypeObj.XOBJ;
    tss[BitsAlias.STR] = TypeStr.STR;
    MEM_STR  = make(tss,TypeBits.make(BitsAlias.STR));
    MEM_ABC  = make(TypeMemPtr.ABCPTR.getbit(),TypeStr.ABC);
  }
  static final TypeMem[] TYPES = new TypeMem[]{FULL,MEM,MEM_ABC};

  // All mapped memories remain, but each memory flips internally.
  @Override protected TypeMem xdual() {
    TypeObj[] oops = new TypeObj[_aliases.length];
    for(int i=0; i<_aliases.length; i++ )
      if( _aliases[i] != null )
        oops[i] = (TypeObj)_aliases[i].dual();
    return new TypeMem(oops,_losts.dual());
  }
  @Override protected Type xmeet( Type t ) {
    if( t._type != TMEM ) return ALL; //
    TypeMem tf = (TypeMem)t;
    // Shortcut common case
    if( this==FULL || tf==FULL ) return FULL;
    if( this==EMPTY ) return t;
    if( tf  ==EMPTY ) return this;
    // Meet of default values, meet of element-by-element.
    int  len = Math.max(_aliases.length,tf._aliases.length);
    int mlen = Math.min(_aliases.length,tf._aliases.length);
    TypeObj[] objs = new TypeObj[len];
    for( int i=1; i<len; i++ )
      objs[i] = i<mlen && _aliases[i]==null && tf._aliases[i]==null // Shortcut null-vs-null
        ? null : (TypeObj)at(i).meet(tf.at(i)); // meet element-by-element
    TypeBits losts = (TypeBits)_losts.meet(tf._losts); // Being lost propagates
    return make0(objs,losts);
  }

  // Meet of all possible loadable values
  public TypeObj ld( TypeMemPtr ptr ) {
    if( this== FULL ) return TypeObj. OBJ;
    if( this==EMPTY ) return TypeObj.XOBJ;
    boolean any = ptr.above_center();
    TypeObj obj = any ? TypeObj.OBJ : TypeObj.XOBJ;
    // Any alias, plus all of its children, are meet/joined.  This does a
    // tree-based scan on the inner loop.
    BitSet bs = ptr._aliases.tree().plus_kids(ptr._aliases);
    for( int alias = bs.nextSetBit(0); alias >= 0; alias = bs.nextSetBit(alias+1) ) {
      TypeObj x = at(alias);
      obj = (TypeObj)(any ? obj.join(x) : obj.meet(x));
    }
    return obj;
  }

  // Whole object Store at an alias.  Just merge with the parent.
  public TypeMem st( int alias, TypeObj obj ) {
    TypeObj to = at(alias);     // Current value for alias
    int max = Math.max(_aliases.length,alias+1);
    TypeObj[] tos = Arrays.copyOf(_aliases,max);
    tos[alias] = (TypeObj)to.meet(obj);
    TypeBits los = to.above_center() ? _losts : _losts.set(alias);
    return TypeMem.make0(tos,los);
  }

  // Mark all memory as being clean (not modified in this function).
  // Recursive.
  public TypeMem clean() {
    if( this==MEM || this==MEM_CLN )
      return MEM_CLN;           // Shortcut
    if( this==XMEM ) return XMEM;
    TypeObj[] ts = _aliases.clone();
    for( int i=1; i<ts.length; i++ )
      if( ts[i] != null )
        ts[i] = (TypeObj)ts[i].clean();
    return make0(ts,_losts);
  }

  // True if all looked-at memory is clean.  Allows a Load to bypass calls.
  public boolean is_clean( BitsAlias aliases, String fld ) {
    for( int alias : aliases )
      if( alias != 0 && !at(alias).is_clean(fld) )
        return false;
    return true;
  }

  @Override public boolean above_center() {
    for( TypeObj alias : _aliases )
      if( alias != null && !alias.above_center() )
        return false;
    return true;
  }
  @Override public boolean may_be_con()   { return false;}
  @Override public boolean is_con()       { return false;}
  @Override public boolean must_nil() { return false; } // never a nil
  @Override Type not_nil() { return this; }
  // Dual, except keep TypeMem.XOBJ as high for starting GVNGCM.gcp() state.
  @Override public TypeMem startype() {
    if( this==EMPTY ) return EMPTY;
    if( this== XMEM ) return  XMEM;
    TypeObj[] oops = new TypeObj[_aliases.length];
    for(int i=0; i<_aliases.length; i++ )
      if( _aliases[i] != null )
        oops[i] = _aliases[i].startype();
    return make0(oops,TypeBits.EMPTY);
  }
}
