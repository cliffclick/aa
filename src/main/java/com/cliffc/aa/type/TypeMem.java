package com.cliffc.aa.type;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.AryInt;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;

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

  // A cache of sharpened pointers.  Pointers get sharpened by looking up their
  // aliases in this memory (perhaps merging several aliases).  The process is
  // recursive and "deeply" sharpens pointers, and is somewhat expensive.
  // Maintain a cache of prior results.  Not related to the objects Type, so
  // not part of the hash/equals checks.  Optional.  Lazily filled in.
  private HashMap<TypeMemPtr,TypeMemPtr> _sharp_cache;

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
    if( as.length == 1 ) return true;
    if( as[1]!=TypeObj.OBJ    && as[1]!=TypeObj.XOBJ   &&
        as[1]!=TypeObj.ISUSED && as[1]!=TypeObj.UNUSED &&
        !(as[1] instanceof TypeLive) &&
        as[1] != null )
      return false;             // Only 2 choices
    if( as.length==2 ) return true; // Trivial all of memory
    // "tight" - something in the last slot
    if( _aliases[_aliases.length-1] == null ) return false;
    // No dups of any parent
    for( int i=2; i<as.length; i++ )
      if( as[i] != null )
        for( int par = BitsAlias.TREE.parent(i); par!=0; par = BitsAlias.TREE.parent(par) )
          if( as[par] != null ) {
            if( as[par] == as[i] ) return false; // Dup of a parent
            break;
          }
    return true;
  }
  @Override int compute_hash() {
    int sum=TMEM;
    for( TypeObj obj : _aliases ) sum += obj==null ? 0 : obj._hash;
    return sum;
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
  @Override String str( VBitSet dups ) {
    if( this==FULL ) return "[ all ]";
    if( this==EMPTY) return "[_____]";
    if( this== MEM ) return "[ mem ]";
    if( this==XMEM ) return "[~mem ]";
    if( this==DEAD ) return "[dead ]";
    SB sb = new SB();
    sb.p('[');
    for( int i=1; i<_aliases.length; i++ )
      if( _aliases[i] != null )
        sb.p(i).p(':').p(_aliases[i].toString()).p(",");
    return sb.unchar().p(']').toString();
  }

  // Alias-at.  Out of bounds or null uses the parent value.
  public TypeObj at(int alias) { return at(_aliases,alias); }
  static TypeObj at(TypeObj[] tos, int alias) { return tos[at_idx(tos,alias)]; }
  // Alias-at index
  static int at_idx(TypeObj[]aliases, int alias) {
    while( true ) {
      if( alias==0 ) return 0;
      if( alias < aliases.length && aliases[alias] != null )
        return alias;
      alias = BitsAlias.TREE.parent(alias);
    }
  }
  //
  public TypeObj[] alias2objs() { return _aliases; }
  public int len() { return _aliases.length; }

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

  private static TypeMem FREE=null;
  @Override protected TypeMem free( TypeMem ret ) { _aliases=null; _sharp_cache=null; FREE=this; return ret; }
  private static TypeMem make(TypeObj[] aliases) {
    TypeMem t1 = FREE;
    if( t1 == null ) t1 = new TypeMem(aliases);
    else { FREE = null;       t1.init(aliases); }
    TypeMem t2 = (TypeMem)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  // Canonicalize memory before making.  Unless specified, the default memory is "do not care"
  public static TypeMem make0( TypeObj[] as ) {
    int len = as.length;
    if( as[1]==null ) {
      int i; for( i=2; i<len; i++ )
        if( as[i]!=null && as[i] != TypeObj.XOBJ )
          break;
      if( i==len ) return DEAD; // All things are dead, so dead
      as[1] = TypeObj.XOBJ;     // Default memory is "do not care"
    }
    if( len == 2 ) return make(as);
    // No dups of a parent
    for( int i=1; i<as.length; i++ )
      if( as[i] != null )
        for( int par = BitsAlias.TREE.parent(i); par!=0; par = BitsAlias.TREE.parent(par) )
          if( as[par] != null ) {
            if( as[par] == as[i] ) as[i] = null;
            break;
          }
    // Remove trailing nulls; make the array "tight"
    while( as[len-1] == null ) len--;
    if( as.length!=len ) as = Arrays.copyOf(as,len);
    return make(as);
  }

  // Precise single alias.  Other aliases are "do not care".  Nil not allowed.
  // Both "do not care" and this alias are exact.
  public static TypeMem make(int alias, TypeObj oop ) {
    TypeObj[] as = new TypeObj[alias+1];
    as[1] = TypeObj.UNUSED;
    as[alias] = oop;
    return make0(as);
  }
  public static TypeMem make(BitsAlias aliases, TypeObj oop ) {
    TypeObj[] as = new TypeObj[aliases.max()+1];
    as[1] = TypeObj.UNUSED;
    for( int alias : aliases )
      if( alias != 0 )
        as[alias] = oop;
    return make0(as);
  }

  public static final TypeMem FULL; // Every alias filled with something
  public static final TypeMem EMPTY;// Every alias filled with anything
  public static final TypeMem  MEM; // FULL, except lifts REC, arrays, STR
  public static final TypeMem XMEM; //
  public static final TypeMem DEAD, ALIVE; // Sentinel for liveness flow; not part of lattice
  public static final TypeMem ESCAPE; // Sentinel for liveness, where the value "escapes" the local scope
  public static final TypeMem ANYMEM,ALLMEM; // Every alias is unused (so above XOBJ or below OBJ)
  public static final TypeMem MEM_ABC, MEM_STR;
  static {
    // Every alias is unused
    ANYMEM = make(new TypeObj[]{null,TypeObj.UNUSED});
    ALLMEM = ANYMEM.dual();
    // All memory, all aliases, holding anything.
    FULL = make(new TypeObj[]{null,TypeObj.OBJ});
    EMPTY= FULL.dual();

    // Sentinel for liveness flow; not part of lattice
    DEAD = make(new TypeObj[1]);
    ALIVE = make(new TypeObj[]{null,TypeLive.BASIC});
    ESCAPE = make(new TypeObj[]{null,TypeLive.ESCAPE});

    // All memory.  Includes breakouts for all structs and all strings.
    // Triggers BitsAlias.<clinit> which makes all the initial alias splits.
    // Not currently including closures
    TypeObj[] tos = new TypeObj[Math.max(BitsAlias.RECORD,BitsAlias.ABC)+1];
    tos[BitsAlias.ALL] = TypeObj.ISUSED;
    tos[BitsAlias.RECORD]=TypeStruct.ALLSTRUCT;
    tos[BitsAlias.ARY] = TypeStr.STR; // TODO: Proxy for all-arrays
    tos[BitsAlias.ABC] = TypeStr.ABC; //
    MEM  = make(tos);
    XMEM = MEM.dual();

    MEM_STR = make(BitsAlias.STR,TypeStr.STR);
    MEM_ABC = make(BitsAlias.ABC,TypeStr.ABC);
  }
  static final TypeMem[] TYPES = new TypeMem[]{FULL,MEM,MEM_ABC,ANYMEM};

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
    // Sentinel only, not part of lattice.  Not symmetric, but we allow this shortcut here
    if( this==DEAD ) return t;
    if( tf  ==DEAD ) return this;
    // Meet of default values, meet of element-by-element.
    int  len = Math.max(_aliases.length,tf._aliases.length);
    int mlen = Math.min(_aliases.length,tf._aliases.length);
    TypeObj[] objs = new TypeObj[len];
    for( int i=1; i<len; i++ )
      objs[i] = i<mlen && _aliases[i]==null && tf._aliases[i]==null // Shortcut null-vs-null
        ? null : (TypeObj)at(i).meet(tf.at(i)); // meet element-by-element
    return make0(objs);
  }

  // Shallow meet of all possible loadable values.  Used in Node.value calls, so must be monotonic.
  public TypeObj ld( TypeMemPtr ptr ) {
    if( ptr._aliases == BitsAlias.NIL.dual() || ptr._aliases == BitsAlias.NIL )
      return ptr.oob(TypeObj.OBJ);
    if( ptr._aliases == BitsAlias.EMPTY )
      return oob(TypeObj.OBJ);
    if( this== FULL ) return TypeObj. OBJ;
    if( this==EMPTY ) return TypeObj.XOBJ;
    return ld(_aliases,ptr._aliases);
  }
  static TypeObj ld( TypeObj[] tos, BitsAlias aliases ) {
    boolean any = aliases.above_center();
    // Any alias, plus all of its children, are meet/joined.  This does a
    // tree-based scan on the inner loop.
    TypeObj obj1 = any ? TypeObj.ISUSED : TypeObj.UNUSED;
    for( int alias : aliases )
      for( int kid=alias; kid!=0; kid=BitsAlias.next_kid(alias,kid) ) {
        TypeObj x = at(tos,kid);
        obj1 = (TypeObj)(any ? obj1.join(x) : obj1.meet(x));
      }
    return obj1;
  }

  // Transitively walk all reachable aliases from this set of aliases, and
  // return the complete set.
  public BitsAlias all_reaching_aliases(BitsAlias aliases) {
    if( aliases==BitsAlias.NIL || aliases==BitsAlias.EMPTY ) return aliases;
    if( aliases==BitsAlias.FULL ) return aliases;
    AryInt work = new AryInt();
    VBitSet visit = new VBitSet();
    for( int alias : aliases )
      for( int kid=alias; kid!=0; kid = BitsAlias.next_kid(alias,kid) )
        work.push(kid);

    while( !work.isEmpty() ) {
      int alias=work.pop();
      TypeObj to = at(alias);
      if( to==TypeObj.OBJ || to==TypeObj.ISUSED )
        return BitsAlias.FULL;  // All structs with all possible pointers
      if( !(to instanceof TypeStruct) ) continue;
      TypeStruct ts = (TypeStruct)to;
      // Incomplete struct?  This is an early escapee from Parse times; more
      // fields may be added which we assume is a pointer to all.
      if( ts._open )
        return BitsAlias.FULL;
      for( int i=0; i<ts._ts.length; i++ ) {
        Type fld = ts._ts[i];
        if( TypeMemPtr.OOP.isa(fld) )
          fld = TypeMemPtr.OOP;                      // All possible pointers
        if( !(fld instanceof TypeMemPtr) ) continue; // Not a pointer, no more aliases
        if( ((TypeMemPtr)fld)._aliases.test(1) )
          return BitsAlias.FULL; // All possible pointers
        // Walk the possible pointers, and include them in the slice
        for( int ptralias : ((TypeMemPtr)fld)._aliases )
          for( int kid=ptralias; kid!=0; kid = BitsAlias.next_kid(ptralias,kid) )
            if( !visit.tset(kid) ) {
              work.push(kid);
              aliases = aliases.set(kid);
            }
      }
    }

    return aliases;
  }

  // Slice memory by aliases; unnamed aliases are replaced with ~use.
  public TypeMem slice_reaching_aliases(BitsAlias aliases) { return slice_reaching_aliases(aliases,at(1),TypeObj.UNUSED); }
  public TypeMem slice_reaching_aliases(BitsAlias aliases, TypeObj base, TypeObj unuse) {
    if( aliases==BitsAlias.FULL ) return this;
    TypeObj tos[] = new TypeObj[Math.max(_aliases.length,aliases.max()+1)];
    tos[1]=base;
    for( int i=2; i<tos.length; i++ ) {
      TypeObj to = at(i);
      tos[i] = aliases.test_recur(i) || to==TypeObj.UNUSED ? to : unuse;
    }
    return make0(tos);
  }

  // Sharpen a dull pointer against this memory.
  public TypeMemPtr sharpen( TypeMemPtr dull ) {
    assert dull==dull.simple_ptr();
    if( _sharp_cache != null ) { // Check the cache first
      TypeMemPtr sharp = _sharp_cache.get(dull);
      if( sharp != null ) return sharp;
    }
    // Switch to TypeStruct for building recursive structures.
    return TypeStruct.sharpen(this,dull);
  }
  TypeMemPtr sharp_get( TypeMemPtr tmp ) { return _sharp_cache==null ? null : _sharp_cache.get(tmp); }
  TypeMemPtr sharput( TypeMemPtr dull, TypeMemPtr sharp ) {
    assert dull.interned() && sharp.interned();
    if( _sharp_cache==null ) _sharp_cache = new HashMap<>();
    _sharp_cache.put(dull,sharp);
    return sharp;               // return new not old
  }
  // Sharpen if a maybe-pointer
  @Override public Type sharptr( Type ptr ) { return ptr instanceof TypeMemPtr ? sharpen((TypeMemPtr)ptr) : ptr; }

  // Widen (lose info), to make it suitable as the default memory.
  public TypeMem crush() {
    TypeObj[] oops = _aliases.clone();
    for( int i=1; i<oops.length; i++ )
      if( oops[i]!=null ) oops[i] = oops[i].crush();
    return TypeMem.make0(oops);
  }

  // Returns the same memory, with aliases not in the split set to either XOBJ
  // or UNUSED.
  public TypeMem split_by_alias(BitSet split) {
    int max = Math.max(len(),split.length());
    TypeObj[] mems = new TypeObj[max];
    mems[1] = at(1);            // Set base
    for( int alias=2; alias<max; alias++ ) {
      TypeObj to = at(alias);
      mems[alias] = (to==TypeObj.UNUSED || split.get(alias)) ? to : TypeObj.XOBJ;
    }
    return TypeMem.make0(mems);
  }

  // Merge memories, left or right by alias
  public TypeMem merge_by_alias(TypeMem rhs, BitSet split) {
    int max = Math.max(rhs.len(),Math.max(len(),split.length()));
    TypeObj[] mems = new TypeObj[max];
    mems[1] = at(1);            // Set base from LHS
    for( int alias=2; alias<max; alias++ )
      mems[alias] = merge_one_lhs(split,alias,rhs.at(alias));
    return TypeMem.make0(mems);
  }
  // If split right, take rhs.
  // If split left, and rhs has no answer, take lhs.
  // Else lhs has no answer, so take rhs.
  public TypeObj merge_one_lhs(BitSet split, int alias, TypeObj rhs) {
    if( split.get(alias) ) return rhs;          // Split right, always take right
    // Split left.  See if this is a New alias
    TypeObj lhs = at(alias);
    return merge_pick(lhs,rhs);
  }
  public static TypeObj merge_pick(TypeObj lhs, TypeObj rhs) {
    if( rhs == TypeObj.UNUSED ) return rhs; // Keep an UNUSED
    if( lhs != TypeObj.UNUSED && lhs != TypeObj.XOBJ ) return lhs; // LHS has something
    if( rhs == TypeObj.XOBJ ) return lhs; // RHS has no answer
    return rhs;                 // RHS made a New or an Unused
  }

  // Whole object Store at an alias.  Just merge with the parent.
  public TypeMem st( int alias, TypeObj obj ) {
    TypeObj to = at(alias);     // Current value for alias
    if( to==obj ) return this;  // Shortcut
    int max = Math.max(_aliases.length,alias+1);
    TypeObj[] tos = Arrays.copyOf(_aliases,max);
    tos[alias] = (TypeObj)to.meet(obj);
    return TypeMem.make0(tos);
  }

  // Field store into a conservative set of aliases.
  public TypeMem st( BitsAlias aliases, byte fin, String fld, Type val ) {
    int max = Math.max(_aliases.length,aliases.max()+1);
    TypeObj[] tos = Arrays.copyOf(_aliases,max);
    for( int alias : aliases )
      if( alias != 0 )
        tos[alias] = at(alias).update(fin,fld,val);
    return make0(tos);
  }

  // Whole object Set at an alias.
  public TypeMem set( int alias, TypeObj obj ) {
    if( at(alias)==obj ) return this; // Shortcut
    int max = Math.max(_aliases.length,alias+1);
    TypeObj[] tos = Arrays.copyOf(_aliases,max);
    tos[alias] = obj;
    return make0(tos);
  }

  // This-isa-mem only on the given aliases
  public boolean isa_escape( TypeMem mem, BitsAlias escapes ) {
    for( int alias : escapes )
      if( alias > 0 )
        for( int kid=alias; kid!=0; kid=BitsAlias.next_kid(alias,kid) )
          if( !at(kid).isa(mem.at(kid)) )
            return false;
    return true;
  }

  @Override public boolean above_center() {
    for( TypeObj alias : _aliases )
      if( alias != null && !alias.above_center() && !alias.is_con() )
        return false;
    return true;
  }
  @Override public boolean may_be_con()   { return false;}
  @Override public boolean is_con()       { return false;}
  @Override public boolean must_nil() { return false; } // never a nil
  @Override Type not_nil() { return this; }

  // For node liveness, anything alive means the node is alive
  public boolean is_live() { return this!=DEAD; }

}
