package com.cliffc.aa.type;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;
import java.util.HashMap;
import java.util.function.Predicate;

// Pointers-to-memory; these can be both the address and the value part of
// Loads and Stores.  They carry a set of aliased TypeObjs.
public final class TypeMemPtr extends Type<TypeMemPtr> {
  // List of known memory aliases.  Zero is nil.
  public BitsAlias _aliases;
  // 4 states of public-vs-private, mixed & unknown in a tiny lattice:
  //     UNK -> {PRIV,PUB} -> MIXED
  public static final byte PMIX=0, PRIV=1, PUB=2, PUNK=3;
  private static byte pdual(byte priv) { return (byte)(priv==PMIX || priv==PUNK ? (3-priv) : priv); }
  private static byte pmeet(byte p0, byte p1) { return (byte)(p0&p1); }

  // Loads & Stores thru private pointers can use the sharper private memory.
  public byte _priv;

  // The _obj field is unused (trivially OBJ or XOBJ) for TMPs used as graph
  // node results, because memory contents are modified in TypeMems and
  // TypeObjs and NOT in pointers - hence this field "goes stale" rapidly as
  // graph nodes manipulate the state of memory.
  //
  // The _obj field can be filled out accurately with a TypeMem.sharpen call,
  // and is used to e.g. check pointer types at type assertions (including
  // function call args).
  public TypeObj _obj;          // Meet/join of aliases.  Unused in simple_ptrs in graph nodes.

  private TypeMemPtr(BitsAlias aliases, byte priv, TypeObj obj ) { super     (TMEMPTR); init(aliases,priv,obj); }
  private void init (BitsAlias aliases, byte priv, TypeObj obj ) { super.init(TMEMPTR); _aliases = aliases; _priv=priv; _obj=obj; }
  @Override int compute_hash() {
    assert _obj._hash != 0;
    return (TMEMPTR + _aliases._hash + _priv + _obj._hash)|1;
  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeMemPtr) ) return false;
    TypeMemPtr tf = (TypeMemPtr)o;
    return cycle_equals(tf);
  }
  @Override public boolean cycle_equals( Type o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeMemPtr) ) return false;
    TypeMemPtr t2 = (TypeMemPtr)o;
    if( _aliases != t2._aliases || _priv!=t2._priv ) return false;
    return _obj == t2._obj || _obj.cycle_equals(t2._obj);
  }
  @Override String str( VBitSet dups) {
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return "$"; // Break recursive printing cycle
    if( _aliases==BitsAlias.NIL || _aliases==BitsAlias.NIL.dual() ) return "*0";
    SB sb = new SB().p('*').p(priv_str(_priv));
    _aliases.toString(sb);
    if( _aliases.test(0) ) sb.p('?');
    return sb.toString();
  }
  @Override SB dstr( SB sb, VBitSet dups ) {
    sb.p('_').p(_uid);
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return sb.p('$'); // Break recursive printing cycle
    return _obj.dstr(_aliases.toString(sb.p('*').p(priv_str(_priv))).p("->"),dups);
  }
  @Override public SB str(SB sb, VBitSet dups, TypeMem mem) {
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return sb.p('$'); // Break recursive printing cycle
    if( _aliases==BitsAlias.NIL || _aliases==BitsAlias.NIL.dual() ) return sb.p("*0");
    TypeObj to = (mem == null || _aliases==BitsAlias.RECORD_BITS) ? _obj : mem.ld(this);
    if( to == TypeObj.XOBJ ) to = _obj;
    to.str(_aliases.toString(sb.p('*').p(priv_str(_priv))),dups,mem);
    if( _aliases.test(0) ) sb.p('?');
    return sb;
  }
  private static String priv_str(byte priv) {
    switch(priv) {
    case PMIX: return "!";         // Mixed
    case PRIV: return "_";         // Private
    case PUB : return "";          // Public
    case PUNK: return "#";         // Unknown
    default: return "BAD_PRIV";
    }
  }

  private static TypeMemPtr FREE=null;
  @Override protected TypeMemPtr free( TypeMemPtr ret ) { FREE=this; return ret; }
  public static TypeMemPtr make(BitsAlias aliases, byte priv, TypeObj obj ) {
    TypeMemPtr t1 = FREE;
    if( t1 == null ) t1 = new TypeMemPtr(aliases,priv,obj);
    else { FREE = null;          t1.init(aliases,priv,obj); }
    TypeMemPtr t2 = (TypeMemPtr)t1.hashcons();
    return t1==t2 ? t1 : t1.free(t2);
  }

  public static TypeMemPtr make( int alias, TypeObj obj ) { return make(BitsAlias.make0(alias),PUB,obj); }
  public static TypeMemPtr make_nil( int alias, TypeObj obj ) { return make(BitsAlias.make0(alias).meet_nil(),PUB,obj); }
  public TypeMemPtr make_from( TypeObj obj ) { return make(_aliases,_priv,obj); }
  public TypeMemPtr make_from_public( ) { return make(_aliases,PUB,_obj); }
  public TypeMemPtr make_from_priv( ) { return make(_aliases,PRIV,_obj); }

  public  static final TypeMemPtr DISPLAY_PTR= new TypeMemPtr(BitsAlias.RECORD_BITS0,PMIX,TypeStruct.DISPLAY );
  static {
    DISPLAY_PTR._hash = DISPLAY_PTR.compute_hash(); // Filled in during DISPLAY.install_cyclic
  }
  public  static final TypeMemPtr OOP0   = make(BitsAlias.FULL    ,PMIX,TypeObj.OBJ); // Includes nil
  public  static final TypeMemPtr OOP    = make(BitsAlias.NZERO   ,PMIX,TypeObj.OBJ); // Excludes nil
  public  static final TypeMemPtr ISUSED = make(BitsAlias.NZERO   ,PMIX,TypeObj.ISUSED); // Excludes nil
  public  static final TypeMemPtr STRPTR = make(BitsAlias.STRBITS ,PMIX,TypeStr.STR);
  public  static final TypeMemPtr STR0   = make(BitsAlias.STRBITS0,PMIX,TypeStr.STR);
  public  static final TypeMemPtr ABCPTR = make(BitsAlias.ABC     ,     TypeStr.ABC);
  public  static final TypeMemPtr ABC0   = make(ABCPTR._aliases.meet_nil(),PUB,TypeStr.ABC);
  public  static final TypeMemPtr STRUCT = make(BitsAlias.RECORD_BITS ,PMIX,TypeStruct.ALLSTRUCT);
  public  static final TypeMemPtr STRUCT0= make(BitsAlias.RECORD_BITS0,PMIX,TypeStruct.ALLSTRUCT);
  public  static final TypeMemPtr NO_DISP= make(BitsAlias.NIL,PRIV,TypeStr.NO_DISP); // Above [0]->obj, below center
  public  static final TypeMemPtr DISP_SIMPLE= make(BitsAlias.RECORD_BITS0,PMIX,TypeObj.ISUSED); // closed display
  public  static final TypeMemPtr USE0   = make(BitsAlias.FULL    ,PMIX,TypeObj.ISUSED); // Includes nil
  static final TypeMemPtr[] TYPES = new TypeMemPtr[]{OOP0,STR0,STRPTR,ABCPTR,STRUCT,NO_DISP};

  @Override public boolean is_display_ptr() {
    BitsAlias x = _aliases.strip_nil();
    if( x==BitsAlias.EMPTY ) return true; // Just a NIL
    int alias1 = x.abit();                 // Just a single alias
    // The GENERIC function allows the generic record, otherwise must be on the display list
    if( alias1 != -1 )
      return Math.abs(alias1)==BitsAlias.RECORD || com.cliffc.aa.Env.DISPLAYS.test_recur(Math.abs(alias1));
    // If closures are being used, can be multiple valid displays
    for( int alias : _aliases )
      if( alias != 0 && !com.cliffc.aa.Env.DISPLAYS.test_recur(alias) )
        return false;           // This alias is not on the DISPLAYS list
    return true;
  }

  @Override protected TypeMemPtr xdual() {
    return new TypeMemPtr(_aliases.dual(),pdual(_priv),(TypeObj)_obj.dual());
  }
  @Override TypeMemPtr rdual() {
    if( _dual != null ) return _dual;
    TypeMemPtr dual = _dual = new TypeMemPtr(_aliases.dual(),pdual(_priv),(TypeObj)_obj.rdual());
    dual._dual = this;
    if( _hash != 0 ) dual._hash = dual.compute_hash();
    return dual;
  }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TMEMPTR:break;
    case TFLT:
    case TINT:
    case TFUNPTR:
    case TRPC:   return cross_nil(t);
    case TFUNSIG:
    case TLIVE:
    case TOBJ:
    case TSTR:
    case TSTRUCT:
    case TTUPLE:
    case TMEM:   return ALL;
    default: throw typerr(t);   // All else should not happen
    }
    // Meet of aliases
    TypeMemPtr ptr = (TypeMemPtr)t;
    BitsAlias aliases = _aliases.meet(ptr._aliases);
    TypeObj to = (TypeObj)_obj.meet(ptr._obj);
    byte pmeet = pmeet(_priv,ptr._priv);
    return make(aliases, pmeet, to);
  }
  // Widens, not lowers.
  @Override public Type simple_ptr() {
    if( _obj==TypeObj.ISUSED || _obj==TypeObj.UNUSED || _obj==TypeStr.NO_DISP ) return this;
    if( _obj==TypeObj.OBJ || _obj==TypeObj.XOBJ ) return this;
    return make(_aliases,_priv,oob(TypeObj.ISUSED));
  }
  @Override public boolean above_center() {
    return _aliases.above_center();
  }
  @Override public Type bound_impl(Type t) {
    if( !(t instanceof TypeMemPtr) ) return oob();
    TypeMemPtr tmp = (TypeMemPtr)t;
    // Deep bounds; keep the in-bounds _aliases but bound the _obj.
    if( tmp._aliases.dual().isa(_aliases) && _aliases.isa(tmp._aliases) )
      return _obj.bound_impl(tmp._obj);
    // Aliases OOB
    return oob();
  }
  // Aliases represent *classes* of pointers and are thus never constants.
  // nil is a constant.
  @Override public boolean may_be_con()   { return may_nil(); }
  @Override public boolean is_con()       { return _aliases==BitsAlias.NIL; } // only nil
  @Override public boolean must_nil() { return _aliases.test(0) && !above_center(); }
  @Override public boolean may_nil() { return _aliases.may_nil(); }
  @Override Type not_nil() {
    BitsAlias bits = _aliases.not_nil();
    return bits==_aliases ? this : make(bits,_priv,_obj);
  }
  @Override public Type meet_nil(Type nil) {
    // See testLattice15.  The UNSIGNED NIL tests as a lattice:
    //    [~0]->~obj  ==>  NIL  ==>  [0]-> obj
    // But loses the pointed-at type down to OBJ.
    // So using SIGNED NIL, which also tests as a lattice:
    //    [~0]->~obj ==>  XNIL  ==>  [0]->~obj
    //    [~0]-> obj ==>   NIL  ==>  [0]-> obj

    if( _aliases.isa(BitsAlias.NIL.dual()) ) {
      if( _obj.above_center() && nil==XNIL )  return XNIL;
      if( nil==NIL ) return NIL;
    }
    return make(_aliases.meet(BitsAlias.NIL),_priv,nil==NIL ? TypeObj.OBJ : _obj);
  }
  // Used during approximations, with a not-interned 'this'.
  // Updates-in-place.
  public Type ax_meet_nil(Type nil) {
    if( _aliases.isa(BitsAlias.NIL.dual()) ) {
      if( _obj==TypeObj.XOBJ && nil==XNIL )  return XNIL;
      if( nil==NIL ) return NIL;
    }
    _aliases = _aliases.meet(BitsAlias.NIL);
    if( nil==NIL ) _obj = TypeObj.OBJ;
    return this;
  }

  public BitsAlias aliases() { return _aliases; }

  // Build a mapping from types to their depth in a shortest-path walk from the
  // root.  Only counts depth on TypeStructs with the matching alias.  Only
  // used for testing.
  HashMap<Type,Integer> depth() {
    int alias = _aliases.getbit();
    HashMap<Type,Integer> ds = new HashMap<>();
    Ary<TypeStruct> t0 = new Ary<>(new TypeStruct[]{(TypeStruct)_obj});
    Ary<TypeStruct> t1 = new Ary<>(new TypeStruct[1],0);
    int d=0;                    // Current depth
    while( !t0.isEmpty() ) {
      while( !t0.isEmpty() ) {
        TypeStruct ts = t0.pop();
        if( ds.putIfAbsent(ts,d) == null )
          for( Type tf : ts._ts ) {
            if( ds.putIfAbsent(tf,d) == null &&  // Everything in ts is in the current depth
                tf instanceof TypeMemPtr ) {
              TypeMemPtr tmp = (TypeMemPtr)tf;
              if( tmp._obj instanceof TypeStruct )
                (tmp._aliases.test(alias) ? t1 : t0).push((TypeStruct)tmp._obj);
            }
          }
      }
      Ary<TypeStruct> tmp = t0; t0 = t1; t1 = tmp; // Swap t0,t1
      d++;                                         // Raise depth
    }
    return ds;
  }

  // Max depth of struct, with a matching alias TMP
  static int max(int alias, HashMap<Type,Integer> ds) {
    int max = -1;
    for( Type t : ds.keySet() )
      if( (t instanceof TypeMemPtr) && ((TypeMemPtr)t)._aliases.test(alias) )
        max = Math.max(max,ds.get(t));
    return max+1;               // Struct is 1 more depth than TMP
  }

  // Lattice of conversions:
  // -1 unknown; top; might fail, might be free (Scalar->Int); Scalar might lift
  //    to e.g. Float and require a user-provided rounding conversion from F64->Int.
  //  0 requires no/free conversion (Int8->Int64, F32->F64)
  // +1 requires a bit-changing conversion (Int->Flt)
  // 99 Bottom; No free converts; e.g. Flt->Int requires explicit rounding
  @Override public byte isBitShape(Type t) {
    return (byte)(t instanceof TypeMemPtr ? 0 : 99);  // Mixing TMP and a non-ptr
  }
  @SuppressWarnings("unchecked")
  @Override void walk( Predicate<Type> p ) { if( p.test(this) ) _obj.walk(p); }
  public int getbit() { return _aliases.getbit(); }
  @Override TypeMemPtr crush_fld_impl(String fld) {
    return make(_aliases,_priv,(TypeObj)_obj.crush_fld_impl(fld)); // TODO: _priv should be PUB or PMIX?
  }
  @Override public TypeMemPtr widen() {
    // Flatten to either all-structs or all-strings, unless both.
    boolean rec = _aliases.isa(BitsAlias.RECORD_BITS0);
    boolean str = _aliases.isa(BitsAlias.STRBITS0);
    BitsAlias bs = rec ? (str
                          ? BitsAlias.FULL
                          : BitsAlias.RECORD_BITS0)
      : BitsAlias.STRBITS0;
    return make(bs,_priv,(TypeObj)_obj.widen());
  }
}
