package com.cliffc.aa.type;

import com.cliffc.aa.util.*;

import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;

import static com.cliffc.aa.AA.TODO;
import static com.cliffc.aa.type.TypeFld.Access;

/**
   Memory type; the state of all memory; memory edges order memory ops.
   Produced at the program start, consumed by all function calls, consumed be
   Loads, consumed and produced by Stores.  Can be broken out in the
   "equivalence class" (Alias#) model of memory over a bulk memory to allow
   more fine-grained knowledge.  Memory is accessed via Alias#s, where all
   TypeObjs in an Alias class are Meet together as an approximation.

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
   to the call (and are reachable from those) - but we need a convenient
   Bottom type.  Missing aliases default to TypeObj.

   The representation is a collection of TypeObjs indexed by alias#.  Missing
   aliases are always equal to their nearest present parent.  The root at
   alias#1 is only either TypeObj.BOT or TOP.  Alias#0 is nil and is always
   missing.  The structure is canonicalized; if a child is a dup of a parent it
   is removed (since an ask will yield the correct value from the parent).

   There is no meet/join relationship between parent and child; a child can be
   precisely updated independently of the parent and other siblings.

   CNC - Observe that the alias Trees on Fields applies to Indices on arrays as
   well - if we can group indices in a tree-like access pattern (obvious one
   being All vs some Constants).
*/
public class TypeMem extends Type<TypeMem> {

  // Mapping from alias#s to the current known alias state.  TypeMem is never a
  // nil.  Slot#0 is always nil.  Slot#1 is the Parent-Of-All aliases and is
  // the default value.  Default values are replaced with null during
  // canonicalization.
  private TypeStruct[] _objs;

  // A cache of sharpened pointers.  Pointers get sharpened by looking up their
  // aliases in this memory (perhaps merging several aliases).  The process is
  // recursive and "deeply" sharpens pointers, and is somewhat expensive.
  // Maintain a cache of prior results.  Not related to the object's Type, so
  // not part of the hash/equals checks.  Optional.  Lazily filled in.
  private HashMap<BitsAlias,TypeMemPtr> _sharp_cache;

  private TypeMem init(TypeStruct[] objs) {
    super.init();
    assert check(objs);    // Caller has canonicalized arrays already
    _objs = objs;
    return this;
  }
  // False if not 'tight' (no trailing null pairs) or any matching pairs (should
  // collapse to their parent) or any mixed parent/child.
  private static boolean check(TypeStruct[] as) {
    if( as.length < 2 ) return false;
    if( as[0]!=null ) return false;
    if( as[1]!=TypeStruct.ISUSED && as[1]!=TypeStruct.UNUSED && as[1]!= null )
      return false;             // Only 2 choices
    if( as.length==2 ) return true; // Trivial all of memory
    // "tight" - something in the last slot
    if( as[as.length-1] == null ) return false;
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
  @Override public long static_hash( ) { return _objs.length; }

  // ----------
  @Override long compute_hash() {
    Util.add_hash(super.static_hash() ^ ((long) _objs.length <<2));
    for( TypeStruct ts : _objs )
      if( ts!=null )
        Util.add_hash(ts._hash);
    return Util.get_hash();
  }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeMem tf) ) return false;
    if( _objs.length != tf._objs.length ) return false;
    for( int i = 0; i< _objs.length; i++ )
      if( _objs[i] != tf._objs[i] ) // note '==' and NOT '.equals()'
        return false;
    return true;
  }
  // Never part of a cycle, so the normal check works
  @Override public boolean cycle_equals( Type o ) { return equals(o); }

  @Override public void _str_dups( PENV P ) {
    if( P.mem )
      for( int i = 1; i< _objs.length; i++ )
        if( _objs[i]!=null )
          _objs[i]._str_dups(P);
  }

  @Override PENV _str0( PENV P ) {
    if( this==ALLMEM  ) return P.p("[[_all_]]");
    if( this==ANYMEM  ) return P.p("[[_any_]]");
    if( !P.mem ) return P.p("[[MEM]]");

    P.p("[[");
    if( P.indent ) P.sb.ii(1).nl(); // Indent memory
    for( int i = 1; i< _objs.length; i++ )
      if( _objs[i] != null ) {
        if( P.indent ) P.sb.i();
        _objs[i]._str(P.p(i).p(':')).p(',');
        if( P.indent ) P.nl();
      }
    if( P.indent ) P.sb.di(1).i();
    else P.sb.unchar();
    return P.p("]]");
  }


  static TypeMem valueOf(Parse P, String cid ) {
    if( P.peek("_all_]]") ) return ALLMEM;
    if( P.peek("_any_]]") ) return ANYMEM;
    Ary<TypeStruct> objs  = new Ary<>( new TypeStruct[1],0);
    objs.push(null);
    while( true ) {
      int alias = (int)P._num();
      P.require(':');
      TypeStruct obj = (TypeStruct)Cyclic.install(P.type(),null);
      objs.setX(alias,obj);
      if( !P.peek(',') ) break;
    }
    return make0(objs.asAry());
  }

  // Alias-at.  Out of bounds or null uses the parent value.
  public TypeStruct at(int alias) { return at( _objs,alias); }
  static TypeStruct at(TypeStruct[] tos, int alias) { return tos[at_idx(tos,alias)]; }
  // Alias-at index
  static int at_idx(TypeStruct[]tos, int alias) {
    if( alias==0 ) return 1;    // Either base memory, or assert
    while( true ) {
      if( alias < tos.length && tos[alias] != null )
        return alias;
      alias = BitsAlias.TREE.parent(alias);
      assert alias!=0;
    }
  }
  //
  public TypeStruct[] alias2objs() { return _objs; }
  public int len() { return _objs.length; }

  static { new Pool(TMEM,new TypeMem()); }
  private static TypeMem make(TypeStruct[] objs) {
    Pool P = POOLS[TMEM];
    TypeMem t1 = P.malloc();
    return t1.init(objs).hashcons_free();
  }

  // Canonicalize memory before making.  Unless specified, the default memory is "do not care"
  public static TypeMem make0( TypeStruct[] as ) {
    if( as[1]==null ) as[1] = TypeStruct.UNUSED;
    return make(dedup(as));
  }
  private static TypeStruct[] dedup( TypeStruct[] as ) {
    int len = as.length;
    if( len <= 2 ) return as;
    // No dups of a parent
    for( int i=1; i<len; i++ )
      if( as[i] != null )
        for( int par = BitsAlias.TREE.parent(i); par!=0; par = BitsAlias.TREE.parent(par) )
          if( as[par] != null ) {
            if( as[par] == as[i] ) as[i] = null;
            break;
          }
    // Remove trailing nulls; make the array "tight"
    while( as[len-1] == null ) len--;
    if( as.length!=len ) as = Arrays.copyOf(as,len);
    return as;
  }

  // Precise single alias.  Other aliases are "do not care".  Nil not allowed.
  // Both "do not care" and this alias are exact.
  public static TypeMem make(int alias, TypeStruct oop ) {
    TypeStruct[] as = new TypeStruct[alias+1];
    as[1] = TypeStruct.UNUSED;
    as[alias] = oop;
    return make(as);
  }
  public static TypeMem make(BitsAlias aliases, TypeStruct oop ) {
    TypeStruct[] as = new TypeStruct[aliases.max()+1];
    as[1] = TypeStruct.UNUSED;
    for( int alias : aliases )
      if( alias != 0 )
        as[alias] = oop;
    return make0(as);
  }
  // Set 'alias' to 'oop', and all parent aliases to unused in this memory.
  public TypeMem make_from_unused(int alias, TypeStruct oop) {
    TypeStruct[] as = Arrays.copyOf( _objs,Math.max( _objs.length,alias+1));
    as[alias] = oop;
    for( int par = BitsAlias.TREE.parent(alias); par!=1; par = BitsAlias.TREE.parent(par) )
      as[par] = TypeStruct.UNUSED;
    return make0(as);
  }
  public TypeMem make_from(int alias, TypeStruct oop) {
    TypeStruct[] as = Arrays.copyOf( _objs,Math.max( _objs.length,alias+1));
    as[alias] = oop;
    return make0(as);    
  }

  public static final TypeMem ANYMEM,ALLMEM,EXTMEM; // Every alias is unused (so above XOBJ or below OBJ)
  public static final TypeMem STRMEM; // Every alias is unused except string

  static {
    // Every alias is used in the worst way
    ALLMEM = make0(new TypeStruct[]{null,TypeStruct.ISUSED});
    ANYMEM = ALLMEM.dual();
    EXTMEM = make(BitsAlias.EXTX,TypeStruct.ISUSED);
    STRMEM = make(BitsAlias.STRX,TypeStruct.ISUSED);
  }
  static final TypeMem[] TYPES = new TypeMem[]{ALLMEM,STRMEM};

  // All mapped memories remain, but each memory flips internally.
  @Override protected TypeMem xdual() {
    TypeStruct[] objs = new TypeStruct[_objs.length];
    for( int i = 0; i< _objs.length; i++ )
      if( _objs[i] != null )
        objs[i] = _objs[i].dual();
    return POOLS[TMEM].<TypeMem>malloc().init(objs);
  }
  @Override protected Type xmeet( Type t ) {
    TypeMem tm = (TypeMem)t;
    int  len = Math.max(_objs.length,tm._objs.length);
    int mlen = Math.min(_objs.length,tm._objs.length);

    TypeStruct[] objs = new TypeStruct[len];
    for( int i=1; i<len; i++ )
      objs[i] = i<mlen && _objs[i]==null && tm._objs[i]==null // Shortcut null-vs-null
        ? null : (TypeStruct)at(_objs,i).meet(at(tm._objs,i));   // meet element-by-element
    return make0(objs);
  }

  // Any alias is not UNUSED?
  public boolean has_used(BitSet aliases) {
    for( int alias = aliases.nextSetBit(0); alias != -1; alias = aliases.nextSetBit(alias + 1))
      if( at(alias)!= TypeStruct.UNUSED )
        return true;            // Has a not-unused (some used) type
    return false;
  }

  // Shallow meet of all possible loadable values.  Used in Node.value calls, so must be monotonic.
  public TypeStruct ld( TypeNil ptr ) {
    if( ptr._nil )
      return TypeStruct.UNUSED; // Loading from nil
    if( ptr._aliases == BitsAlias.EMPTY ) {
      // If aliases are added, we'll fall
      return TypeStruct.UNUSED;
      //return ptr._obj.oob(TypeStruct.ISUSED);
    }
    if( ptr._aliases == BitsAlias.NALL )
      return TypeStruct.ISUSED;
    if( this==ALLMEM ) return TypeStruct.ISUSED;
    if( this==ANYMEM ) return TypeStruct.UNUSED;
    return ld( _objs,ptr._aliases);
  }
  private static TypeStruct ld( TypeStruct[] tos, BitsAlias aliases ) {
    boolean any = aliases.above_center();
    // Any alias, plus all of its children, are meet/joined.  This does a
    // tree-based scan on the inner loop.
    TypeStruct obj1 = any ? TypeStruct.ISUSED : TypeStruct.UNUSED;
    for( int alias : aliases )
      for( int kid=alias; kid!=0; kid=BitsAlias.next_kid(alias,kid) ) {
        TypeStruct x = at(tos,kid);
        obj1 = (TypeStruct)(any ? obj1.join(x) : obj1.meet(x));
      }
    return obj1;
  }

  // Transitively walk all reachable aliases from this set of aliases, and
  // return the complete set.
  public BitsAlias all_reaching_aliases(BitsAlias aliases) {
    if( aliases==BitsAlias.EMPTY ) return BitsAlias.EMPTY;
    if( aliases==BitsAlias.NALL  ) return aliases;
    AryInt work = new AryInt();
    VBitSet visit = new VBitSet();
    _add_all(aliases,visit,work,aliases);

    while( !work.isEmpty() ) {
      if( aliases==BitsAlias.NALL ) return aliases; // Already full
      TypeStruct ts = at(work.pop());
      if( ts==TypeStruct.ISUSED )
        aliases = _add_one(BitsAlias.EXTX,visit,work,aliases);
      for( TypeFld tfld : ts ) {
        Type fld = tfld._t;
        // Called function returns are also tracked
        while( fld instanceof TypeFunPtr fptr && fptr._ret != fptr ) fld = fptr._ret;
        // If below a TMP, use the worst TMP
        if( TypeMemPtr.ISUSED.isa(fld) )
          fld = TypeMemPtr.ISUSED;
        if( !(fld instanceof TypeMemPtr tmp) ) continue; // Not a pointer, no more aliases
        aliases = _add_all(tmp._aliases,visit,work,aliases);
      }
    }
    return aliases;
  }

  private BitsAlias _add_all( BitsAlias bits, VBitSet visit, AryInt work, BitsAlias aliases ) {
    for( int alias : bits )
      for( int kid=alias; kid != 0; kid=BitsAlias.next_kid(alias,kid) )
        aliases = _add_one( alias, visit, work, aliases );
    return aliases;
  }
  private BitsAlias _add_one( int alias, VBitSet visit, AryInt work, BitsAlias aliases ) {
    if( visit.tset(alias) ) return aliases;
    work.push(alias);
    return aliases.set(alias);
  }


  // Slice memory by aliases; unnamed aliases are replaced with ~use.
  public TypeMem slice_reaching_aliases(BitsAlias aliases) {
    if( aliases==BitsAlias.NALL ) return this;
    if( aliases==BitsAlias.NANY ) return ANYMEM;
    TypeStruct[] tos = new TypeStruct[Math.max( _objs.length,aliases.max()+1)];
    tos[1] = TypeStruct.UNUSED;
    for( int i=2; i<tos.length; i++ )
      tos[i] = aliases.test_recur(i) ? TypeStruct.ISUSED : null;
    return make0(tos);
  }

  // --------------------------------------------------------------------------
  // Sharpen a dull pointer against this memory.
  public TypeMemPtr sharpen( TypeMemPtr dull ) {
    assert dull.is_simple_ptr();
    if( _sharp_cache != null ) { // Check the cache first
      TypeMemPtr sharp = _sharp_cache.get(dull._aliases);
      if( sharp != null ) return sharp;
    }

    // Build a (recursively) sharpened pointer from memory.  Alias sets can be
    // looked-up directly in a map from BitsAlias to TypeObjs.  This is useful
    // for resolving all the deep pointer structures at a point in the program
    // (i.e., error checking arguments).  Given a TypeMem and a BitsAlias it
    // returns a TypeObj (and extends the HashMap for future calls).  The TypeObj
    // may contain deep pointers to other deep TypeObjs, including cyclic types.
    // This function is monotonic in its arguments.

    // Pass 1:  fill "dull" cache
    HashMap<BitsAlias,TypeMemPtr> dull_cache = new HashMap<>();
    _dull(dull,dull_cache);

    // Pass 2: Stitch together structs with dull pointers to make a possibly cyclic result.
    TypeMemPtr sharp = (TypeMemPtr)_sharp(dull,dull_cache,new VBitSet());
    assert sharp.interned() == dull_cache.isEmpty();
    // See if we need to cycle-install any cyclic types
    if( dull_cache.isEmpty() )
      return sharp;
    // On exit, cyclic-intern all cyclic things; remove from dull cache and sharpen all
    TypeStruct mt = Cyclic.install(sharp._obj, dull_cache);
    // Move from sharpened dull cache to sharp cache
    for( TypeMemPtr tmp : dull_cache.values() )
      sharput(tmp._aliases,tmp);
    return sharp_get(dull._aliases);
  }
  TypeMemPtr sharp_get( BitsAlias aliases ) { return _sharp_cache==null ? null : _sharp_cache.get(aliases); }
  void sharput( BitsAlias aliases, TypeMemPtr sharp ) {
    assert sharp.interned();
    if( _sharp_cache==null ) _sharp_cache = new HashMap<>();
    _sharp_cache.put(aliases,sharp);
  }
  // Sharpen if a maybe-pointer
  @Override public Type sharptr( Type ptr ) { return ptr.sharptr2(this); }

  // Pass 1:  fill "dull" cache
  //   Check "dull" & "sharp" cache for hit; if so return.
  //   Walk all aliases;
  //     Get obj from mem; it is "dull".
  //     MEET "dull" objs.
  //   If meet is sharp, put in sharp cache & return.
  //   Put dull ptr to dull meet in dull cache.
  //   Walk dull fields; for all dull TMPs, recurse.
  private static final BitSetSparse DULLV = new BitSetSparse();
  void _dull( Type dull, final HashMap<BitsAlias,TypeMemPtr> dull_cache ) {
    if( !(dull instanceof Cyclic) ) return; // Nothing to sharpen
    // Check caches and return
    if( dull instanceof TypeMemPtr tmp && tmp.is_simple_ptr() ) {
      BitsAlias aliases = tmp._aliases;
      if( sharp_get(aliases) != null ) return;
      if( dull_cache.get(aliases) != null ) return;
      // Walk and meet "dull" fields; all TMPs will point to ISUSED (hence are dull).
      if( aliases.above_center() ) throw TODO();
      TypeStruct t = TypeStruct.UNUSED;
      for( int alias : aliases )
        for( int kid=alias; kid != 0; kid=BitsAlias.next_kid(alias,kid) )
          t = (TypeStruct)t.meet(at(kid));

      DULLV.clear();
      if( _is_sharp(t)==null )       // If sharp, install and return
        { sharput(aliases, tmp.make_from(t)); return; }
      // Install in dull result in dull cache BEFORE recursing.  We might see
      // it again if cyclic types.
      TypeMemPtr dptr = tmp.malloc_from(t);
      dull_cache.put(tmp._aliases,dptr);
      dull = t;
    }
    // Visit all dull pointers and recursively collect
    dull.walk((fld,ignore) -> _dull(fld,dull_cache));
  }
  // Not-null if found a dull ptr, null if all ptrs sharp
  private static TypeMemPtr _is_sharp(Type t) {
    if( DULLV.tset(t._uid) ) return null;
    if( !(t instanceof Cyclic) ) return null;
    if( t instanceof TypeMemPtr tmp && tmp.is_simple_ptr() ) return tmp;
    return t.walk((fld,ignore) -> _is_sharp(fld), (x,y)-> x==null ? y : x);
  }


  // Pass 2: stitch together structs of dull pointers to make a possibly cyclic type.
  //  Check for hit in sharp cache; if so return it.
  //  Get from dull cache; if not interned, flag as cyclic & return it.
  //  Put not-interned dull clone in dull cache.
  //    Walk all fields.
  //  If not cyclic, all fields already interned; standard intern, put in sharp; remove dull; & return.
  //  If cyclic, then some field is not interned, put on cyclic list?
  //  Return not-interned value.
  Type _sharp(Type dull, final HashMap<BitsAlias,TypeMemPtr> dull_cache, final VBitSet visit ) {
    if( !(dull instanceof Cyclic) ) return dull; // Nothing to sharpen
    Type t;
    if( dull instanceof TypeMemPtr tmp ) {
      if( tmp.is_simple_ptr() ) {
        t = sharp_get(tmp._aliases);
        if( t !=null ) return t;
        t = dull_cache.get(tmp._aliases);
        if( visit.tset(t._uid) ) return t;
      } else {
        assert tmp.is_prim();
        return dull;
      }
    } else if( dull instanceof TypeStruct dullts ) {
      t = dullts.copy2();
    } else {
      t = dull.copy();
    }
    assert !t.interned();
    t.walk_update( fld -> _sharp(fld,dull_cache,visit));
    return t;
  }


  // Whole object Set at an alias.
  public TypeMem set( int alias, TypeStruct obj ) {
    if( at(alias)==obj && _set_fast(alias) )
      return this; // Shortcut
    assert _objs[0] == null;
    int max = Math.max( _objs.length,alias+1);
    TypeStruct[] tos = Arrays.copyOf( _objs,max);
    for( int kid=alias; kid != 0; kid=BitsAlias.next_kid(alias,kid) )
      if( kid < max ) tos[kid] = null;
    tos[alias] = obj;
    return make0(tos);
  }
  private boolean _set_fast(int alias ) {
    for( int kid=alias; kid != 0; kid=BitsAlias.next_kid(alias,kid) )
      if( kid < _objs.length && _objs[kid]!=null )
        return false;           // Need to clean up
    return true;
  }

  
  // Struct store into a conservative set of aliases.
  // 'precise' is replace, imprecise is MEET.
  public TypeMem update( TypeMemPtr tmp, TypeStruct tvs ) {
    // If precise, just replace whole struct
    if( tmp.is_con() )
      return set(tmp._aliases.getbit(),tvs);
    
    // Must do struct-by-struct updates, doing inprecise meets
    Ary<TypeStruct> ss = new Ary<>( _objs.clone());
    for( int alias : tmp._aliases )
      if( alias != 0 )
        for( int kid=alias; kid != 0; kid=BitsAlias.next_kid(alias,kid) )
          ss.setX(kid,(TypeStruct)at(kid).meet(tvs));
    return make0(ss.asAry());
  }

  // Field store into a conservative set of aliases.
  // 'precise' is replace, imprecise is MEET.
  public TypeMem update( TypeMemPtr tmp, TypeFld fld ) {
    if( tmp.is_con() ) {
      int alias = tmp._aliases.getbit();
      //return set(alias,at(alias).update());
      throw TODO();
    }
    
    // Must do struct-by-struct updates
    Ary<TypeStruct> ss = new Ary<>( _objs.clone());
    for( int alias : tmp._aliases )
      if( alias != 0 )
        for( int kid=alias; kid != 0; kid=BitsAlias.next_kid(alias,kid) )
          ss.setX(kid,at(kid).update(fld,tmp.is_con()));
    return make0(ss.asAry());
  }

  

  // Everything in the 'escs' set is flattened to UNUSED.
  public TypeMem kill(BitsAlias escs) {
    if( escs==BitsAlias.EMPTY ) return this;
    if( escs==BitsAlias.NALL  ) throw com.cliffc.aa.AA.TODO(); // Shortcut
    // See if any changes
    boolean found=false;
    for( int alias : escs )
      if( at(alias)!=TypeStruct.UNUSED )
        { found=true; break; }
    if( !found ) return this;

    assert _objs[0] == null;
    TypeStruct[] tos = _objs.clone();
    for( int alias : escs ) {
      if( alias >= tos.length )
        tos = Arrays.copyOf(_objs,alias*2);
      tos[alias] = TypeStruct.UNUSED;
    }
    return make0(tos);
  }

  // The fld in the alias set is flattened to set to ANY
  public TypeMem kill(BitsAlias escs, String fld) {
    assert escs.above_center();
    //assert _objs[1]==TypeStruct.UNUSED;
    // See if any changes
    boolean found=false;
    for( int alias : escs ) {
      TypeStruct ts = at(alias);
      int idx = ts.find(fld);
      if( idx!= -1 && at(idx) != Type.ANY )
        { found=true; break; }
    }
    if( !found ) return this;
    
    TypeStruct[] tos = _objs.clone();
    tos[0] = null;
    for( int alias : escs )
      if( alias < tos.length && tos[alias]!=null )
        tos[alias] = tos[alias].kill(fld);
    return make0(tos);
  }

  
  // False if field is modifiable across any alias
  public boolean fld_not_mod( BitsAlias aliases, String name) {
    for( int alias : aliases ) {
      if( alias != 0 ) {
        TypeFld fld = at(alias).get(name);
        if( fld!=null && fld._access == Access.RW )
          return false;
      }
    }
    return true;                // Not modified in any alias
  }

  // Everything NOT in the 'escs' is flattened to UNUSED.
  // Everything YES in the 'escs' is flattened for live.
  public TypeMem remove_no_escapes( BitsAlias escs ) {
    TypeStruct[] tos = new TypeStruct[Math.max( _objs.length,escs.max()+1)];
    for( int i=1; i<tos.length; i++ )
      tos[i] = escs.test_recur(i) ? at(i).flatten_live_fields() : TypeStruct.UNUSED;
    return make0(tos);
  }


  // For live-ness purposes, flatten all field contents.
  // Only need per-field ANY/ALL.
  public TypeMem flatten_live_fields() {
    TypeStruct to, tof=null;
    int i; for( i=1; i< _objs.length; i++ ) {
      if( (to = _objs[i]) != null && (tof = to.flatten_live_fields())!=to )
        break;
    }
    if( i== _objs.length ) return this;

    TypeStruct[] tos = _objs.clone();
    tos[0] = null;
    tos[i++] = tof;
    for( ; i< _objs.length; i++ )
      if( tos[i] != null )
        tos[i] = tos[i].flatten_live_fields();
    return make0(tos);
  }

  @Override public boolean above_center() { return _objs[1].above_center(); }
  @Override public boolean is_con()       { return false;}
}
