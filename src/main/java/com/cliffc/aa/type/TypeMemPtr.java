package com.cliffc.aa.type;

import com.cliffc.aa.util.*;

import java.util.HashMap;
import java.util.function.BinaryOperator;

// Pointers-to-memory; these can be both the address and the value part of
// Loads and Stores.  They carry a set of aliased TypeObjs.

public final class TypeMemPtr extends TypeNil<TypeMemPtr> implements Cyclic {
  // IFF the _aliases is a single bit, then also the ptr (and hence _obj) is unique.
  public boolean _con;

  // The _obj field is unused (trivially OBJ or XOBJ) for TMPs used as graph
  // node results, because memory contents are modified in TypeMems and
  // TypeStructs and NOT in pointers - hence this field "goes stale" rapidly as
  // graph nodes manipulate the state of memory.
  //
  // The _obj field can be filled out accurately with a TypeMem.sharpen call,
  // and is used to e.g. check pointer types at type assertions (including
  // function call args).
  public TypeStruct _obj; // Meet/join of aliases.  Unused in simple_ptrs in graph nodes.

  private TypeMemPtr init(boolean any, boolean nil, boolean sub, BitsAlias aliases, boolean con, TypeStruct obj ) {
    super.init(any, nil, sub, aliases, BitsFun.EMPTY);
    assert !aliases.test(0); // No nil in aliases, use nil/sub instead
    //assert con || aliases!=BitsAlias.EMPTY; // Empty is a "constant"
    assert !con || (aliases.abit()!= -1 && !BitsAlias.TREE.is_parent(Math.abs(aliases.abit())));
    _con=con;
    _obj=obj;
    return this;
  }
  @Override TypeMemPtr copy() {
    TypeMemPtr tmp = super.copy();
    tmp._aliases = _aliases;
    tmp._con = _con;
    tmp._obj = _obj;
    return tmp;
  }

  @Override public TypeMemPtr walk( TypeStrMap map, BinaryOperator<TypeMemPtr> reduce ) { return map.map(_obj,"obj"); }
  @Override public long lwalk( LongStringFunc map, LongOp reduce ) { return map.run(_obj,"obj"); }
  @Override public void walk( TypeStrRun map ) { map.run(_obj,"obj"); }
  @Override public void walk_update( TypeMap map ) { _obj = (TypeStruct)map.map(_obj); }
  @Override public Cyclic.Link _path_diff0(Type t, NonBlockingHashMapLong<Link> links) {
    return Cyclic._path_diff(_obj,((TypeMemPtr)t)._obj,links);
  }

  @Override long static_hash() { return Util.mix_hash(super.static_hash(),_aliases._hash); }
  @Override long compute_hash() {
    long hash = lwalk( (fld,str) -> (fld==null ? 0 : fld._cyc_hash) ^ str.hashCode(),
                       (hash0,hash1) -> hash0 ^ hash1 );
    return Util.mix_hash(hash,static_hash());
  }

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
    if( _aliases != t2._aliases || _con != t2._con ) return false;
    return _obj == t2._obj || (_obj!=null && t2._obj!=null && _obj.cycle_equals(t2._obj));
  }

  @Override public void _str_dups( PENV P ) {
    if( P.visit.tset(_uid) ) {
      if( !P.dups.containsKey(_uid) )
        P.dups.put(_uid,"P"+(char)('A'+P._tmp++));
      return;
    }
    if( _obj!=null ) _obj._str_dups(P);
  }

  @Override PENV _str0( PENV P ) {
    if( _any ) P.p('~');
    // Shortcut for printing boxed primitives
    if( is_clz_ptr() ) return P.p("*CLZ");
    P.p('*');
    if( _con ) P.p('#');
    if( P.debug ) _aliases.str(P.sb);
    return _obj==null ? P.p("()") : _obj._str(P).p(_str_nil());
  }

  @Override boolean _str_complex0(PENV P) { return _obj!=null && _obj._str_complex(P); }

  boolean is_clz_ptr() { return this==Cons.CLZ_TMP; }

  static TypeMemPtr valueOf(Parse P, String cid, boolean any) {
    P.require('*');
    boolean con = P.peek('#');
    var aliases = P.bits(BitsAlias.EMPTY);
    boolean haz_nil = aliases.test(0);
    boolean nil = any &  haz_nil;
    boolean sub = any | !haz_nil;
    TypeMemPtr tmp = malloc(any, nil, sub, aliases.clear(0),con, (TypeStruct)null);
    if( cid!=null ) P._dups.put(cid,tmp);
    assert !tmp.interned();
    tmp._obj = (TypeStruct)P.type();
    return tmp.val_nil(P);
  }


  static { new Pool(TMEMPTR,new TypeMemPtr()); }
  static TypeMemPtr malloc(boolean any, boolean nil, boolean sub, BitsAlias aliases, boolean con, TypeStruct obj ) {
    TypeMemPtr t1 = POOLS[TMEMPTR].malloc();
    return t1.init(any,nil,sub,aliases,con,obj);
  }
  // Convenience for some callers, supports half as many choices
  public static TypeMemPtr malloc(boolean any, boolean haz_nil, BitsAlias aliases, boolean con, TypeStruct obj ) {
    return malloc(any, any & haz_nil, any | !haz_nil, aliases, con, obj );
  }

  public static TypeMemPtr make(boolean haz_nil, BitsAlias aliases, boolean con, TypeStruct obj ) {
    assert !aliases.is_empty(); // Ambiguous
    return malloc(aliases.above_center(),haz_nil,aliases,con,obj).hashcons_free();
  }
  public static TypeMemPtr make(boolean any, boolean haz_nil, BitsAlias aliases, boolean con, TypeStruct obj ) {
    return malloc(any,haz_nil,aliases,con,obj).hashcons_free();
  }
  public static TypeMemPtr make(boolean any, boolean nil, boolean sub, BitsAlias aliases, boolean con, TypeStruct obj ) {
    return malloc(any,nil,sub,aliases,con,obj).hashcons_free();
  }
  TypeMemPtr malloc_from(TypeStruct obj) {
    return malloc(_any, _nil, _sub, _aliases, _con, obj);
  }

  public static TypeMemPtr make( int alias, TypeStruct obj ) { return make(false,BitsAlias.make0(alias),true,obj); }
  public static TypeMemPtr make_simple( int alias ) { return make(alias,null); }
  public static TypeMemPtr make_nil( int alias, TypeStruct obj ) { return make(true,BitsAlias.make0(alias),true,obj); }
  public TypeMemPtr make_from( TypeStruct obj ) { return _obj==obj ? this : malloc_from(obj).hashcons_free(); }
  public TypeMemPtr make_from( BitsAlias aliases ) { return _aliases==aliases ? this : make(aliases.test(0),aliases.clear(0),_con,_obj); }

  // Legacy constructor for legacy HM tests
  public static TypeMemPtr make_str(String s) { return make_str(TypeInt.con(s.length()),TypeInt.con( s.isEmpty() ? 0 : s.charAt(0))); }
  public static TypeMemPtr make_str(TypeInt len, TypeInt char0) { return make_str(BitsAlias.make0(BitsAlias.STRX),len,char0); }
  public static TypeMemPtr make_str(BitsAlias aliases, TypeInt len, TypeInt char0) {
    // Make a string object
    TypeStruct ts = TypeStruct.make_prim(TypeFld.make_clz(TypeStruct.XSTRZ()),TypeFld.make_prim(len));
    return TypeMemPtr.make(aliases.test(0),aliases.clear(0),false,ts);
  }
  public boolean is_str() { return _obj.is_str(); }

  // The display is a self-recursive structure: slot 0 is a ptr to a Display.
  // To break class-init cycle, this is made here, now.
  public static final TypeStruct DISPLAY;
  public static final TypeMemPtr DISPLAY_PTR;
  public static final TypeFld    DISP_FLD;
  static {
    // Install a (to be cyclic) DISPLAY.  Not cyclic during installation, since
    // we cannot build the cycle all at once.
    DISP_FLD = TypeFld.malloc(TypeFld.CLZ,null,TypeFld.Access.Final);
    TypeStruct.RECURSIVE_MEET++;
    TypeFld[] flds = TypeFlds.make(DISP_FLD);
    TypeStruct.RECURSIVE_MEET--;
    DISPLAY = TypeStruct.malloc(false,ALL,flds);
    DISPLAY_PTR = malloc(false,false,BitsAlias.NALL,false,DISPLAY);
    DISP_FLD.setX(DISPLAY_PTR);
    TypeStruct ds = Cyclic.install(DISPLAY);
    assert ds==DISPLAY;
  }

  public  static final TypeMemPtr ISUSED0= make(true ,BitsAlias.NALL,false,TypeStruct.ISUSED); // Includes nil
  public  static final TypeMemPtr ISUSED = make(false,BitsAlias.NALL,false,TypeStruct.ISUSED); // Excludes nil
  public  static final TypeMemPtr EMTPTR = malloc(false,false,BitsAlias.EMPTY,false,TypeStruct.UNUSED).hashcons_free();
  public  static final TypeMemPtr DISP_SIMPLE= make(false,BitsAlias.NALL,false,TypeStruct.ISUSED); // closed display
  public  static final TypeMemPtr INTPTR = make(BitsAlias.INTX,TypeStruct.ISUSED);   // Simple ptr-to-wrapped int
  public  static final TypeMemPtr FLTPTR = make(BitsAlias.FLTX,TypeStruct.ISUSED);   // Simple ptr-to-wrapped flt
  public  static final TypeMemPtr STRPTR = make_str(TypeInt.INT8,TypeInt.con('A'));

  static final Type[] TYPES = new Type[]{ISUSED0,EMTPTR,DISPLAY,DISPLAY_PTR};
  public static void init1( HashMap<String,TypeNil> types ) {
    types.put("str",STRPTR);
  }

  @Override protected TypeMemPtr xdual() {
    BitsAlias ad = _aliases.dual();
    TypeStruct od = _obj==null ? null : _obj._dual;
    boolean xor = _nil == _sub;
    return malloc(!_any,_nil^xor,_sub^xor,ad,_con,od);
  }
  @Override void rdual() { _dual._obj = _obj._dual; }
  @Override protected TypeMemPtr xmeet( Type t ) {
    // Meet of aliases
    TypeMemPtr ptr = (TypeMemPtr)t;
    BitsAlias aliases = _aliases.meet(ptr._aliases);
    TypeStruct to = _obj==null || ptr._obj==null ? null : (TypeStruct)_obj.meet(ptr._obj);
    boolean any = _any & ptr._any;
    boolean nil = _nil & ptr._nil;
    boolean sub = _sub & ptr._sub;
    boolean con = (_con&ptr._con) | (_con&ptr._any) | (_any&ptr._con);
    con &= (aliases.abit()!=-1);
    return malloc(any, nil, sub, aliases, con, to).hashcons_free();
  }

  // Widens, not lowers.
  @Override public TypeMemPtr simple_ptr() {
    return _obj==null ? this : make_from((TypeStruct)null);
  }
  public final boolean is_simple_ptr() { return _obj==null; }

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

  @Override public Type sharptr2( TypeMem mem ) {
    return mem.sharpen(this);
  }

  @Override BitsFun _all_reaching_fidxs( TypeMem tmem) {
    BitsFun fidxs = BitsFun.EMPTY;
    if( Type.ARF.tset(_uid) || tmem==null ) return fidxs;
    for( int alias : _aliases )
      if( alias!=0 )
        fidxs = fidxs.meet(tmem.at(alias)._all_reaching_fidxs(tmem));
    return fidxs;
  }

  // Only a constant if the pointer AND object is a constant; we might have
  // dulled a precise constant object and the result is not a constant.
  @Override public boolean is_con(BitsAlias cons) {
    if( !above_center() && _aliases!=BitsAlias.EMPTY ) {
      int alias = _aliases.abit();
      if( alias== -1 ) return false;
      //if( !cons.test(alias) ) return false;
      if( !_con ) return false;
    }
    return _obj!=null && _obj.is_con(cons);
  }

  @Override public Type hack_dsp() { return make_from(_obj.hack_dsp()); }

  // Used for assertions
  @Override boolean intern_check1() { return _obj==null || _obj.intern_get()!=null; }
}
