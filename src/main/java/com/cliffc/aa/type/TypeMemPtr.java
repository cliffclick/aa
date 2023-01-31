package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.*;

import java.util.HashMap;
import java.util.function.BinaryOperator;

// Pointers-to-memory; these can be both the address and the value part of
// Loads and Stores.  They carry a set of aliased TypeObjs.

public final class TypeMemPtr extends TypeNil<TypeMemPtr> implements Cyclic {
  // List of known memory aliases.  Zero is nil.
  public BitsAlias _aliases;

  // The _obj field is unused (trivially OBJ or XOBJ) for TMPs used as graph
  // node results, because memory contents are modified in TypeMems and
  // TypeStructs and NOT in pointers - hence this field "goes stale" rapidly as
  // graph nodes manipulate the state of memory.
  //
  // The _obj field can be filled out accurately with a TypeMem.sharpen call,
  // and is used to e.g. check pointer types at type assertions (including
  // function call args).
  public TypeStruct _obj; // Meet/join of aliases.  Unused in simple_ptrs in graph nodes.

  private TypeMemPtr _init( BitsAlias aliases, TypeStruct obj ) {
    assert !aliases.test(0); // No nil in aliases, use nil/sub instead
    _aliases = aliases;
    _obj=obj;
    return this;
  }
  private TypeMemPtr init(boolean any, boolean haz_nil, BitsAlias aliases, TypeStruct obj ) {
    super.init(any,haz_nil);
    return _init(aliases,obj);
  }
  private TypeMemPtr init(boolean any, boolean nil, boolean sub, BitsAlias aliases, TypeStruct obj ) {
    super.init(any, nil, sub);
    return _init(aliases,obj);
  }
  @Override TypeMemPtr copy() { return _copy().init(_any, _nil, _sub, _aliases,_obj); }

  @Override public TypeMemPtr walk( TypeStrMap map, BinaryOperator<TypeMemPtr> reduce ) { return map.map(_obj,"obj"); }
  @Override public long lwalk( LongStringFunc map, LongOp reduce ) { return map.run(_obj,"obj"); }
  @Override public void walk( TypeStrRun map ) { map.run(_obj,"obj"); }
  @Override public void walk_update( TypeMap map ) { _obj = (TypeStruct)map.map(_obj); }
  @Override public Cyclic.Link _path_diff0(Type t, NonBlockingHashMapLong<Link> links) {
    return Cyclic._path_diff(_obj,((TypeMemPtr)t)._obj,links);
  }

  @Override long static_hash() { return Util.mix_hash(super.static_hash(),_aliases._hash); }

  // Static properties equals.  Already known to be the same class and
  // not-equals.  Ignore edges.
  @Override boolean static_eq(TypeMemPtr t) { return super.static_eq(t) && _aliases == t._aliases; }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeMemPtr tf) ) return false;
    return cycle_equals(tf);
  }
  @Override public boolean cycle_equals( Type o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeMemPtr t2) ) return false;
    if( !super.equals(t2) ) return false;
    if( _aliases != t2._aliases ) return false;
    return _obj == t2._obj || _obj.cycle_equals(t2._obj);
  }

  @Override public void _str_dups( VBitSet visit, NonBlockingHashMapLong<String> dups, UCnt ucnt ) {
    if( visit.tset(_uid) ) {
      if( !dups.containsKey(_uid) )
        dups.put(_uid,"P"+(char)('A'+ucnt._tmp++));
      return;
    }
    _obj._str_dups(visit,dups,ucnt);
  }

  @Override SB _str0( VBitSet visit, NonBlockingHashMapLong<String> dups, SB sb, boolean debug, boolean indent ) {
    if( _any ) sb.p('~');
    sb.p('*');
    if( debug ) _aliases.str(sb);
    sb = _obj._str(visit,dups, sb, debug, indent);
    return _str_nil(sb);
  }

  @Override boolean _str_complex0(VBitSet visit, NonBlockingHashMapLong<String> dups) { return _obj._str_complex(visit,dups); }

  static TypeMemPtr valueOf(Parse P, String cid, boolean any) {
    P.require('*');
    var aliases = P.bits(BitsAlias.EMPTY);
    TypeMemPtr tmp = malloc(any, aliases.test(0),aliases.clear(0),null);
    if( cid!=null ) P._dups.put(cid,tmp);
    assert !tmp.interned();
    tmp._obj = (TypeStruct)P.type();
    return tmp.val_nil(P);
  }


  static { new Pool(TMEMPTR,new TypeMemPtr()); }
  public static TypeMemPtr malloc(boolean any, boolean haz_nil, BitsAlias aliases, TypeStruct obj ) {
    TypeMemPtr t1 = POOLS[TMEMPTR].malloc();
    return t1.init(any,haz_nil,aliases,obj);
  }
  public static TypeMemPtr make(boolean haz_nil, BitsAlias aliases, TypeStruct obj ) {
    assert !aliases.is_empty(); // Ambiguous
    return malloc(aliases.above_center(),haz_nil,aliases,obj).hashcons_free();
  }
  public static TypeMemPtr make(boolean any, boolean haz_nil, BitsAlias aliases, TypeStruct obj ) {
    return malloc(any,haz_nil,aliases,obj).hashcons_free();
  }
  public static TypeMemPtr malloc(boolean any, boolean nil, boolean sub, BitsAlias aliases, TypeStruct obj ) {
    TypeMemPtr t1 = POOLS[TMEMPTR].malloc();
    return t1.init(any,nil,sub,aliases,obj);
  }
  TypeMemPtr malloc_from(TypeStruct obj) {
    return malloc(_any, _nil, _sub,_aliases,obj);
  }

  public static TypeMemPtr make( int alias, TypeStruct obj ) { return make(false,BitsAlias.make0(alias),obj); }
  public static TypeMemPtr make_nil( int alias, TypeStruct obj ) { return make(true,BitsAlias.make0(alias),obj); }
  public TypeMemPtr make_from( TypeStruct obj ) { return _obj==obj ? this : malloc_from(obj).hashcons_free(); }
  public TypeMemPtr make_from( BitsAlias aliases ) { return _aliases==aliases ? this : make(aliases.test(0),aliases.clear(0),_obj); }
  @Override TypeMemPtr make_from( boolean nil, boolean sub ) { return malloc(_any,nil,sub,_aliases,_obj).hashcons_free(); }

  // Legacy constructor for legacy HM tests
  public static final int STR_ALIAS = 4; // Legacy str ptr value
  public static TypeMemPtr make_str(String s) { return make_str(TypeInt.con(s.length()>0 ? s.charAt(0):0)); }
  public static TypeMemPtr make_str(Type t) { return make_str(BitsAlias.make0(STR_ALIAS),t); }
  public static TypeMemPtr make_str(BitsAlias aliases, Type t) {
    TypeStruct ts = TypeStruct.make(TypeFld.make_tup(t, AA.ARG_IDX)).set_name("str:");
    return TypeMemPtr.make(aliases.test(0),aliases.clear(0),ts);
  }
  public boolean is_str() { return _obj.is_str(); }

  // The display is a self-recursive structure: slot 0 is a ptr to a Display.
  // To break class-init cycle, this is made here, now.
  public static final TypeStruct DISPLAY;
  public static final TypeMemPtr DISPLAY_PTR;
  public static final TypeFld    DISP_FLD;
  public static final TypeNil    NO_DISP= TypeNil.XSCALAR;
  static {
    // Install a (to be cyclic) DISPLAY.  Not cyclic during the install, since
    // we cannot build the cycle all at once.
    DISP_FLD = TypeFld.malloc("^",null,TypeFld.Access.Final);
    TypeStruct.RECURSIVE_MEET++;
    TypeFld[] flds = TypeFlds.make(DISP_FLD);
    TypeStruct.RECURSIVE_MEET--;
    DISPLAY = TypeStruct.malloc(false,"",ALL,flds);
    DISPLAY_PTR = malloc(false,false,BitsAlias.NALL,DISPLAY);
    DISP_FLD.setX(DISPLAY_PTR);
    TypeStruct ds = Cyclic.install(DISPLAY);
    assert ds==DISPLAY;
  }

  public  static final TypeMemPtr ISUSED0= make(true ,BitsAlias.NALL,TypeStruct.ISUSED); // Includes nil
  public  static final TypeMemPtr ISUSED = make(false,BitsAlias.NALL,TypeStruct.ISUSED); // Excludes nil
  public  static final TypeMemPtr EMTPTR = malloc(false,false,BitsAlias.EMPTY,TypeStruct.UNUSED).hashcons_free();
  public  static final TypeMemPtr DISP_SIMPLE= make(false,BitsAlias.NALL,TypeStruct.ISUSED); // closed display
  public  static final TypeMemPtr STRPTR = make_str(TypeInt.INT8); // For legacy HM tests

  static final Type[] TYPES = new Type[]{ISUSED0,EMTPTR,DISPLAY,DISPLAY_PTR};

  @Override protected TypeMemPtr xdual() {
    BitsAlias ad = _aliases.dual();
    TypeStruct od = _obj.dual();
    boolean xor = _nil == _sub;
    return malloc(!_any,_nil^xor,_sub^xor,ad,od);
  }
  @Override void rdual() { _dual._obj = _obj._dual; }
  @Override protected TypeMemPtr xmeet( Type t ) {
    // Meet of aliases
    TypeMemPtr ptr = (TypeMemPtr)t;
    BitsAlias aliases = _aliases.meet(ptr._aliases);
    TypeStruct to = (TypeStruct)_obj.meet(ptr._obj);
    boolean any = _any & ptr._any;
    boolean nil = _nil & ptr._nil;
    boolean sub = _sub & ptr._sub;
    return malloc(any,nil,sub,aliases, to).hashcons_free();
  }

  // Widens, not lowers.
  @Override public TypeMemPtr simple_ptr() {
    if( _obj.len()==0 ) return this;
    return make_from(_obj.oob(TypeStruct.ISUSED).set_name(_obj._clz));
  }
  // Value types have a named prototype, and locally carry their fields in the
  // Type, i.e. are not a simple_ptr.  Reference types also have a named
  // prototype, but locally carry their fields in memory and so always use a
  // simple ptr.
  public boolean is_valtype() {
    return _obj._clz.length()>0; // Not a simple ptr
  }

  public BitsAlias aliases() { return _aliases; }

  // Build a mapping from types to their depth in a shortest-path walk from the
  // root.  Only counts depth on TypeStructs with the matching alias.  Does not
  // bump the depth of a backedge.
  public HashMap<Type,Integer> depth() {
    HashMap<Type,Integer> ds = new HashMap<>();
    Work<Type> t0 = new Work<>(), t1 = new Work<>();
    t0.add(_obj);
    int d=0;                    // Current depth
    ds.put(this,d);             //
    while( !t0.isEmpty() ) {
      for( Type t=t0.pop(); t!=null; t=t0.pop() )
        if( t instanceof Cyclic &&
            ds.putIfAbsent(t,d) ==null ) {
          final Work<Type> ft0=t0, ft1=t1;
          t.walk((tc,label)->(tc instanceof TypeMemPtr tmp && tmp._aliases.overlaps(_aliases) ? ft1 : ft0).add(tc));
        }
      // Swap worklists, raise depth
      Work<Type> tmp = t0; t0 = t1; t1 = tmp; // Swap t0,t1
      d++;                                    // Raise depth
    }
    return ds;
  }

  // Build a mapping from aliases to their max repeats in a shortest-path walk
  // from the root.  Does a breadth-first search.
  public void depth2(NonBlockingHashMapLong<Integer> ds) {
    VBitSet bs0 = new VBitSet(), bs1 = new VBitSet();
    Work<Type> t0 = new Work<>(), t1 = new Work<>();
    t0.add(this);
    while( !t0.isEmpty() ) {
      // Once per depth, bump all the aliases' depths
      bs1.clr();
      for( int i=0; i<t0.len(); i++ )
        if( t0.at(i) instanceof TypeMemPtr tmp )
          for( int alias : tmp._aliases )
            if( !bs1.tset(alias) ) { // Once per depth
              Integer ii = ds.get(alias);
              ds.put(alias,(ii==null ? 0 : ii)+1);
            }

      // Populate the next depth in the breadth-first search
      final Work<Type> ft1=t1; Type t;
      while( (t=t0.pop())!=null )
        if( t instanceof Cyclic )
          t.walk((tc,ignore)-> { if( !bs0.tset(tc._uid) ) ft1.add(tc);} );

      // Swap worklists, raise depth
      Work<Type> tmp = t0; t0 = t1; t1 = tmp; // Swap t0,t1
    }
  }

  // Only used for testing.  Max depth of struct, with a matching alias TMP
  // that is not a backedge.
  public int max(HashMap<Type,Integer> ds) {
    int max = -1;
    for( Type t : ds.keySet() )
      if( t instanceof TypeMemPtr tmp && tmp._aliases.overlaps(_aliases) ) {
        int dtmp = ds.get(t);
        Integer dstr = ds.get(tmp._obj);
        if( dstr==null || dtmp<=dstr ) // Disallow backedge
          max = Math.max(max,dtmp);
      }
    return max;
  }

  // Make a Type, replacing all dull pointers from the matching types in mem.
  @Override public Type make_from(Type head, TypeMem mem, VBitSet visit) {
    if( this!=head ) {
      TypeStruct[] pubs = mem.alias2objs();
      boolean mapped=true;
      for( int alias : _aliases )
        if( pubs[alias]==null )
          { mapped=false; break; }
      if( mapped ) {
        TypeStruct obj = mem.ld(this);
        if( obj!=TypeStruct.UNUSED )
          return make_from(obj);
      }
    }
    TypeStruct obj = _obj.make_from(head,mem,visit);
    return obj == null ? this : make_from(obj);
  }

  @Override public Type sharptr2( TypeMem mem ) { return mem.sharpen(this); }
  
  @Override BitsFun _all_reaching_fidxs( TypeMem tmem) {
    BitsFun fidxs = BitsFun.EMPTY;
    if( Type.ARF.tset(_uid) || tmem==null ) return fidxs;
    for( int alias : _aliases )
      if( alias!=0 )
        fidxs = fidxs.meet(tmem.at(alias)._all_reaching_fidxs(tmem));
    return fidxs;
  }

  @Override public Type widen() { return this; }

  // Used for assertions
  @Override boolean intern_check1() { return _obj.intern_get()!=null; }
}
