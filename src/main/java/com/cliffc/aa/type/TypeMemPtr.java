package com.cliffc.aa.type;

import com.cliffc.aa.util.*;

import java.util.HashMap;
import java.util.function.*;

import static com.cliffc.aa.AA.ARG_IDX;

// Pointers-to-memory; these can be both the address and the value part of
// Loads and Stores.  They carry a set of aliased TypeObjs.
public final class TypeMemPtr extends Type<TypeMemPtr> implements Cyclic {
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
  private boolean _cyclic; // Type is cyclic.  This is a summary property, not a part of the type, hence is not in the equals nor hash

  private TypeMemPtr init(BitsAlias aliases, TypeStruct obj ) {
    _name="";
    _cyclic = false;
    _aliases = aliases;
    _obj=obj;
    return this;
  }
  @Override TypeMemPtr copy() { return _copy().init(_aliases,_obj); }

  @Override public boolean cyclic() { return _cyclic; }
  @Override public void set_cyclic() { _cyclic = true; }
  @Override public void clr_cyclic() { _cyclic = false; }
  @Override public <T> T walk1( BiFunction<Type,String,T> map, BinaryOperator<T> reduce ) { return map.apply(_obj,"obj"); }
  @Override public void walk_update( UnaryOperator<Type> update ) { _obj = (TypeStruct)update.apply(_obj); }
  @Override public Cyclic.Link _path_diff0(Type t, NonBlockingHashMapLong<Link> links) {
    return Cyclic._path_diff(_obj,((TypeMemPtr)t)._obj,links);
  }

  int _hash() { return Util.hash_spread(super.static_hash() + _aliases._hash + _obj._type); }
  @Override int  static_hash() { return _hash(); } // No edges
  @Override int compute_hash() { assert  _obj._hash!=0;  return _hash() + _obj._hash; } // Always edges
  // Static properties equals.  Already known to be the same class and
  // not-equals.  Ignore edges.
  @Override boolean static_eq(TypeMemPtr t) { return _aliases == t._aliases && _obj._type == t._obj._type; }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeMemPtr tf) ) return false;
    return cycle_equals(tf);
  }
  @Override public boolean cycle_equals( Type o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeMemPtr t2) ) return false;
    if( _aliases != t2._aliases ) return false;
    return _obj == t2._obj || _obj.cycle_equals(t2._obj);
  }

  @Override void _str_dups( VBitSet visit, NonBlockingHashMapLong<String> dups, UCnt ucnt ) {
    if( visit.tset(_uid) ) {
      if( !dups.containsKey(_uid) )
        dups.put(_uid,"P"+(char)('A'+ucnt._tmp++));
      return;
    }
    _obj._str_dups(visit,dups,ucnt);
  }

  @Override SB _str0( VBitSet visit, NonBlockingHashMapLong<String> dups, SB sb, boolean debug, boolean indent ) {
    sb.p('*');
    if( debug ) _aliases.str(sb);
    return _obj._str(visit,dups, sb, debug, indent);
  }

  @Override boolean _str_complex0(VBitSet visit, NonBlockingHashMapLong<String> dups) { return _obj._str_complex(visit,dups); }

  static TypeMemPtr valueOf(Parse P, String cid) {
    P.require('*');
    var aliases = P.bits(BitsAlias.EMPTY);
    TypeMemPtr tmp = malloc(aliases,null);
    if( cid!=null ) P._dups.put(cid,tmp);
    tmp._obj = (TypeStruct)P.type();
    return tmp;
  }


  static { new Pool(TMEMPTR,new TypeMemPtr()); }
  public static TypeMemPtr make(BitsAlias aliases, TypeStruct obj ) {
    TypeMemPtr t1 = POOLS[TMEMPTR].malloc();
    return t1.init(aliases,obj).hashcons_free();
  }

  static TypeMemPtr malloc(BitsAlias aliases, TypeStruct ts ) {  TypeMemPtr t1 = POOLS[TMEMPTR].malloc(); return t1.init(aliases,ts); }
  TypeMemPtr malloc_from(TypeStruct ts) {  TypeMemPtr t1 = POOLS[TMEMPTR].malloc(); return t1.init(_aliases,ts); }
  public static TypeMemPtr make( int alias, TypeStruct obj ) { return make(BitsAlias.make0(alias),obj); }
  public static TypeMemPtr make_nil( int alias, TypeStruct obj ) { return make(BitsAlias.make0(alias).meet_nil(),obj); }
  public TypeMemPtr make_from( TypeStruct obj ) { return _obj==obj ? this : make(_aliases,obj); }
  public TypeMemPtr make_from( BitsAlias aliases ) { return _aliases==aliases ? this : make(aliases,_obj); }
  public TypeMemPtr make_from_nil( BitsAlias aliases ) {
    if( _aliases==aliases ) return this;
    if( _aliases.test(0) != aliases.test(0) )
      aliases = _aliases.test(0) ? aliases.clear(0) : aliases.set(0);
    return make(aliases,_obj);
  }

  // Legacy constructor for legacy HM tests
  public static TypeMemPtr make_str(String s) { return make_str(TypeInt.con(s.charAt(0))); }
  public static TypeMemPtr make_str(Type t) { return make_str(BitsAlias.make0(4),t); }
  public static TypeMemPtr make_str(BitsAlias aliases, Type t) {
    TypeFld c0 = TypeFld.make_tup(t,ARG_IDX);
    TypeStruct ts = TypeStruct.make("str:",false,c0);
    return TypeMemPtr.make(aliases,ts);
  }
  public boolean is_str() { return Util.eq(_obj._name,"str:"); }

  // The display is a self-recursive structure: slot 0 is a ptr to a Display.
  // To break class-init cycle, this is made here, now.
  public static final TypeStruct DISPLAY;
  public static final TypeMemPtr DISPLAY_PTR;
  public static final TypeFld    DISP_FLD;
  public static final Type       NO_DISP= Type.ANY;
  static {
    // Install a (to be cyclic) DISPLAY.  Not cyclic during the install, since
    // we cannot build the cycle all at once.
    DISPLAY = TypeStruct.malloc_test(TypeFld.make_dsp(Type.ANY));
    TypeStruct.RECURSIVE_MEET++;
    DISPLAY_PTR = TypeMemPtr.make(BitsAlias.NALL,DISPLAY); // Normal create
    DISP_FLD = TypeFld.make_dsp(DISPLAY_PTR);              // Normal create
    DISPLAY.set_fld(DISP_FLD);                             // Change field without changing hash
    TypeStruct.RECURSIVE_MEET--;
    TypeStruct ds = Cyclic.install(DISPLAY);
    assert ds==DISPLAY;
  }

  public  static final TypeMemPtr ISUSED0= make(BitsAlias.ALL0 ,TypeStruct.ISUSED); // Includes nil
  public  static final TypeMemPtr ISUSED = make(BitsAlias.NALL ,TypeStruct.ISUSED); // Excludes nil
  public  static final TypeMemPtr EMTPTR = make(BitsAlias.EMPTY,TypeStruct.UNUSED);
  public  static final TypeMemPtr DISP_SIMPLE= make(BitsAlias.NALL,TypeStruct.ISUSED); // closed display
  public  static final TypeMemPtr STRPTR = make(4,TypeStruct.ISUSED.set_name("str:")); // For legacy HM tests
  public  static final TypeStruct OOP_OOP = TypeStruct.args(ISUSED0,ISUSED0); // { ptr? ptr? -> }

  static final Type[] TYPES = new Type[]{ISUSED0,EMTPTR,DISPLAY,DISPLAY_PTR,OOP_OOP};

  @Override protected TypeMemPtr xdual() {
    BitsAlias ad = _aliases.dual();
    TypeStruct od = _obj.dual();
    if( ad==_aliases && od==_obj )
      return this;              // Centerline TMP
    return POOLS[TMEMPTR].<TypeMemPtr>malloc().init(ad,od);
  }
  @Override TypeMemPtr rdual() {
    assert _hash!=0;
    if( _dual != null ) return _dual;
    TypeMemPtr dual = _dual = POOLS[TMEMPTR].<TypeMemPtr>malloc().init(_aliases.dual(),_obj.rdual());
    dual._dual = this;
    dual._hash = dual.compute_hash();
    return dual;
  }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TMEMPTR:break;
    case TFLT:
    case TINT:
    case TFUNPTR:
    case TRPC:   return cross_nil(t);
    case TARY:
    case TFLD:
    case TSTRUCT:
    case TTUPLE:
    case TMEM:   return ALL;
    default: throw typerr(t);   // All else should not happen
    }
    // Meet of aliases
    TypeMemPtr ptr = (TypeMemPtr)t;
    BitsAlias aliases = _aliases.meet(ptr._aliases);
    TypeStruct to = (TypeStruct)_obj.meet(ptr._obj);
    return make(aliases, to);
  }

  // Widens, not lowers.
  @Override public TypeMemPtr simple_ptr() {
    if( _obj.len()==0 ) return this;
    return make_from(_obj.oob(TypeStruct.ISUSED).set_name(_obj._name));
  }
  // Value types have a named prototype, and locally carry their fields in the
  // Type, i.e. are not a simple_ptr.  Reference types also have a named
  // prototype, but locally carry their fields in memory and so always use a
  // simple ptr.
  public boolean is_valtype() {
    return _obj._name.length()>0;
  }

  @Override public boolean above_center() { return _aliases.above_center(); }
  // Aliases represent *classes* of pointers and are thus never constants.
  // nil is a constant.
  @Override public boolean may_be_con()   { return may_nil(); }
  @Override public boolean is_con()       { return _aliases==BitsAlias.NIL || _aliases==BitsAlias.XNIL; } // only nil
  @Override public boolean must_nil() { return _aliases.test(0) && !above_center(); }
  @Override public boolean may_nil() { return _aliases.may_nil(); }
  @Override Type not_nil() {
    BitsAlias bits = _aliases.not_nil();
    return bits==_aliases ? this : make(bits,_obj);
  }
  @Override public Type remove_nil() {
    BitsAlias bits = _aliases.clear(0);
    return bits==_aliases ? this : make(bits,_obj);
  }
  @Override public Type meet_nil(Type nil) {
    assert nil==NIL || nil==XNIL;
    // See testLattice15.
    if( nil==XNIL )
      return _aliases.test(0) ? (_aliases.above_center() ? XNIL : SCALAR) : NSCALR;
    if( _aliases.above_center() ) return make(BitsAlias.NIL,_obj);
    BitsAlias aliases = _aliases.above_center() ? _aliases.dual() : _aliases;
    return make(aliases.set(0),_obj);
  }
  // Used during approximations, with a not-interned 'this'.
  // Updates-in-place.
  public Type ax_meet_nil(Type nil) {
    if( _aliases.isa(BitsAlias.XNIL) ) {
      if( _obj.above_center() && nil==XNIL )  return XNIL;
      if( nil==NIL ) return NIL;
    }
    _aliases = _aliases.meet(BitsAlias.NIL);
    return this;
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
        if( t instanceof Cyclic cyc &&
            ds.putIfAbsent(t,d) ==null ) {
          final Work<Type> ft0=t0, ft1=t1;
          cyc.walk1((tc,label)->(tc instanceof TypeMemPtr tmp && tmp._aliases.overlaps(_aliases) ? ft1 : ft0).add(tc), (x,y)->null);
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
        if( t instanceof Cyclic cyc )
          cyc.walk1((tc,ignore)-> bs0.tset(tc._uid) ? null : ft1.add(tc), (x,y)->null );

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

  @SuppressWarnings("unchecked")
  @Override public void walk( Predicate<Type> p ) { if( p.test(this) ) _obj.walk(p); }

  // Widen for primitive specialization and H-M unification.  H-M distinguishes
  // ptr-to-array (and string) from ptr-to-record.  Must keep types at the same
  // resolution as H-M, so pointers all permit nil (unless I track a H-M type
  // which disallows nil).
  @Override TypeMemPtr _widen() {
    //if( above_center() ) return this;
    return make(_aliases.widen(),_obj._widen());
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


  @Override TypeStruct repeats_in_cycles(TypeStruct head, VBitSet bs) { return _obj.repeats_in_cycles(head,bs); }

  @Override BitsFun _all_reaching_fidxs( TypeMem tmem) {
    BitsFun fidxs = BitsFun.EMPTY;
    if( Type.ARF.tset(_uid) || tmem==null ) return fidxs;
    for( int alias : _aliases )
      if( alias!=0 )
        fidxs = fidxs.meet(tmem.at(alias)._all_reaching_fidxs(tmem));
    return fidxs;
  }

  // Used for assertions
  @Override boolean intern_check1() { return _obj.intern_lookup()!=null; }
}
