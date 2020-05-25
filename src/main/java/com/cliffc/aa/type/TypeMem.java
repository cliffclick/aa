package com.cliffc.aa.type;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.AryInt;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.Arrays;

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
  public TypeObj at(int alias) { return _aliases[at_idx(alias)]; }
  // Alias-at index
  public int at_idx(int alias) {
    while( true ) {
      if( alias==0 ) return 0;
      if( alias < _aliases.length && _aliases[alias] != null )
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

  // Walk all reachable aliases from this set of aliases, and
  // include them all in the returned memory.
  private TypeMem _slice_all_aliases_plus_children(BitsAlias aliases) {
    AryInt work = new AryInt();
    Ary<TypeObj> tos = new Ary<>(new TypeObj[]{null,TypeObj.UNUSED});
    for( int alias : aliases )
      for( int kid=alias; kid!=0; kid = BitsAlias.next_kid(alias,kid) ) {
        work.push(kid);
        tos.setX(kid,at(kid));
      }

    while( !work.isEmpty() ) {
      int alias=work.pop();
      TypeObj to = at(alias);
      if( to==TypeObj.OBJ || to==TypeObj.ISUSED )
        return this;            // All structs with all possible pointers
      if( !(to instanceof TypeStruct) ) continue;
      TypeStruct ts = (TypeStruct)to;
      for( int i=0; i<ts._ts.length; i++ ) {
        Type fld = ts._ts[i];
        if( TypeMemPtr.OOP.isa(fld) )
          fld = TypeMemPtr.OOP;                      // All possible pointers
        if( !(fld instanceof TypeMemPtr) ) continue; // Not a pointer, no more aliases
        if( ((TypeMemPtr)fld)._aliases.test(1) )
          return this;          // All possible pointers
        // Walk the possible pointers, and include them in the slice
        for( int ptralias : ((TypeMemPtr)fld)._aliases ) {
          for( int kid=ptralias; kid!=0; kid = BitsAlias.next_kid(ptralias,kid) ) {
            if( tos.atX(kid) != null ) continue;
            work.push(kid);
            tos.setX(kid,at(kid));
          }
        }
      }
    }

    return make0(tos.asAry());
  }

  // Report back just the given aliases (plus children)
  public TypeMem slice_all_aliases_plus_children(BitsAlias aliases) {
    return _slice_all_aliases_plus_children(aliases);
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
  public static final TypeMem DEAD; // Sentinel for liveness flow; not part of lattice
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

    // All memory.  Includes breakouts for all structs and all strings.
    // Triggers BitsAlias.<clinit> which makes all the initial alias splits.
    // Not currently including closures
    TypeObj[] tos = new TypeObj[Math.max(BitsAlias.RECORD,BitsAlias.ABC)+1];
    tos[BitsAlias.ALL] = TypeObj.OBJ;
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
    if( ptr._aliases == BitsAlias.EMPTY || ptr._aliases == BitsAlias.NIL )
      return above_center() ? TypeObj.XOBJ : TypeObj.OBJ;
    if( this== FULL ) return TypeObj. OBJ;
    if( this==EMPTY ) return TypeObj.XOBJ;
    boolean any = ptr.above_center();
    // Any alias, plus all of its children, are meet/joined.  This does a
    // tree-based scan on the inner loop.
    TypeObj obj1 = any ? TypeObj.OBJ : TypeObj.XOBJ;
    for( int alias : ptr._aliases )
      for( int kid=alias; kid!=0; kid=BitsAlias.next_kid(alias,kid) ) {
        TypeObj x = at(kid);
        obj1 = (TypeObj)(any ? obj1.join(x) : obj1.meet(x));
      }
    return obj1;
  }
  // TODO: Implement this.  Needed when checking complex actuals against
  // complex formals.
  public TypeObj ld_deep( TypeMemPtr ptr ) {
    return ld(ptr);
  }

  // Whole object Store at an alias.  Just merge with the parent.
  public TypeMem st( int alias, TypeObj obj ) {
    TypeObj to = at(alias);     // Current value for alias
    int max = Math.max(_aliases.length,alias+1);
    TypeObj[] tos = Arrays.copyOf(_aliases,max);
    tos[alias] = (TypeObj)to.meet(obj);
    return TypeMem.make0(tos);
  }

  // Whole object Set at an alias.
  public TypeMem set( int alias, TypeObj obj ) {
    if( at(alias)==obj ) return this; // Shortcut
    int max = Math.max(_aliases.length,alias+1);
    TypeObj[] tos = Arrays.copyOf(_aliases,max);
    tos[alias] = obj;
    return TypeMem.make0(tos);
  }

  // This-isa-mem only on the given aliases
  public boolean isa_escape( TypeMem mem, BitsAlias escapes ) {
    for( int alias : escapes )
      if( alias > 0 )
        if( !at(alias).isa(mem.at(alias)) )
          return false;
    return true;
  }


  // Support for SESE flow optimizations.  Mark all memory as being clean (not
  // modified in this function).  Recursive.
  public TypeMem clean() {
    if( this==XMEM ) return XMEM;
    TypeObj[] ts = _aliases.clone();
    for( int i=1; i<ts.length; i++ )
      if( ts[i] != null )
        ts[i] = (TypeObj)ts[i].clean();
    return make0(ts);
  }

  // Support for SESE flow optimizations.  True if all looked-at memory is
  // clean.  Allows a Load to bypass calls.
  public boolean is_clean( BitsAlias aliases, String fld ) {
    for( int alias : aliases )
      if( alias != 0 && !at(alias).is_clean(fld) )
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
