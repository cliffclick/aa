package com.cliffc.aa.type;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.HashMap;
import java.util.function.Predicate;

import static com.cliffc.aa.type.TypeFld.Access;

/**
 * Pointers-to-memory; these can be both the address and the value part of
 * Loads and Stores.  They carry a set of aliased TypeObjs.
 */
public final class TypeMemPtr extends Type<TypeMemPtr> {
  // List of known memory aliases.  Zero is nil.
  public BitsAlias _aliases;

  /**
   * The _obj field is unused (trivially OBJ or XOBJ) for TMPs used as graph
   * node results, because memory contents are modified in TypeMems and
   * TypeObjs and NOT in pointers - hence this field "goes stale" rapidly as
   * graph nodes manipulate the state of memory.
   * The _obj field can be filled out accurately with a TypeMem.sharpen call,
   * and is used to e.g. check pointer types at type assertions (including
   * function call args).
   */
  public TypeObj _obj;          // Meet/join of aliases.  Unused in simple_ptrs in graph nodes.

  private TypeMemPtr init(BitsAlias aliases, TypeObj obj ) {
    super.init(TMEMPTR,"");
    _aliases = aliases;
    _obj=obj;
    return this;
  }
  @Override int compute_hash() {
    assert _obj._hash != 0;
    return (TMEMPTR + _aliases._hash + _obj._hash)|1;
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
    if( _aliases != t2._aliases ) return false;
    return _obj == t2._obj || _obj.cycle_equals(t2._obj);
  }

  @Override public SB str( SB sb, VBitSet dups, TypeMem mem, boolean debug ) {
    //if( debug ) sb.p('_').p(_uid);
    if( dups.tset(_uid) ) return sb.p('$'); // Break recursive printing cycle
    //if( _aliases==BitsAlias.NIL || _aliases==BitsAlias.NIL.dual() ) return sb.p(debug ? " 0" : "0");
    TypeObj to = (mem == null || _aliases==BitsAlias.RECORD_BITS) ? _obj : mem.ld(this);
    if( to == TypeObj.XOBJ ) to = _obj;
    sb.p('*');
    if( debug ) _aliases.str(sb);
    to.str(sb,dups,mem,debug);
    if( _aliases.test(0) ) sb.p('?');
    return sb;
  }

  static { new Pool(TMEMPTR,new TypeMemPtr()); }
  public static TypeMemPtr make(BitsAlias aliases, TypeObj obj ) {
    TypeMemPtr t1 = POOLS[TMEMPTR].malloc();
    return t1.init(aliases,obj).hashcons_free();
  }

  public static TypeMemPtr make( int alias, TypeObj obj ) { return make(BitsAlias.make0(alias),obj); }
  public static TypeMemPtr make_nil( int alias, TypeObj obj ) { return make(BitsAlias.make0(alias).meet_nil(),obj); }
  public TypeMemPtr make_from( TypeObj obj ) { return make(_aliases,obj); }

  // The display is a self-recursive structure: slot 0 is a ptr to a Display.
  // To break class-init cycle, this is made here, now.
  public static final TypeFld    DISP_FLD= TypeFld.malloc("^",Type.NIL,Access.Final,0);
  public static final TypeStruct DISPLAY = TypeStruct.malloc("",false,TypeFlds.ts(DISP_FLD),true);
  public static final TypeMemPtr DISPLAY_PTR= new TypeMemPtr().init(BitsAlias.RECORD_BITS0,DISPLAY );
  public static final Type       NO_DISP= Type.ANY;
  static {
    DISP_FLD._hash = DISP_FLD.compute_hash();
    DISPLAY._hash = DISPLAY.compute_hash();
    DISPLAY_PTR._hash = DISPLAY_PTR.compute_hash(); // Filled in during DISPLAY.install_cyclic
    assert DISPLAY.at(0) == Type.NIL;
    DISP_FLD.setX(TypeMemPtr.DISPLAY_PTR);
    DISPLAY.install_cyclic(new Ary<>(Types.ts(DISPLAY ,TypeMemPtr.DISPLAY_PTR)));
    assert DISPLAY.is_display();
  }

  public  static final TypeMemPtr ISUSED0= make(BitsAlias.FULL    ,TypeObj.ISUSED); // Includes nil
  public  static final TypeMemPtr ISUSED = make(BitsAlias.NZERO   ,TypeObj.ISUSED); // Excludes nil
  public  static final TypeMemPtr OOP0   = make(BitsAlias.FULL    ,TypeObj.OBJ); // Includes nil
  public  static final TypeMemPtr OOP    = make(BitsAlias.NZERO   ,TypeObj.OBJ); // Excludes nil
  public  static final TypeMemPtr ARYPTR = make(BitsAlias.ARYBITS ,TypeAry.ARY);
  public  static final TypeMemPtr ARY0   = make(BitsAlias.ARYBITS0,TypeAry.ARY);
  public  static final TypeMemPtr STRPTR = make(BitsAlias.STRBITS ,TypeStr.STR);
  public  static final TypeMemPtr STR0   = make(BitsAlias.STRBITS0,TypeStr.STR);
  public  static final TypeMemPtr ABCPTR = make(BitsAlias.ABC     ,TypeStr.ABC);
  public  static final TypeMemPtr ABC0   = make(ABCPTR._aliases.meet_nil(),TypeStr.ABC);
  public  static final TypeMemPtr STRUCT = make(BitsAlias.RECORD_BITS ,TypeStruct.ALLSTRUCT);
  public  static final TypeMemPtr STRUCT0= make(BitsAlias.RECORD_BITS0,TypeStruct.ALLSTRUCT);
  public  static final TypeMemPtr NILPTR = make(BitsAlias.NIL,TypeObj.ISUSED);
  public  static final TypeMemPtr EMTPTR = make(BitsAlias.EMPTY,TypeObj.UNUSED);
  public  static final TypeMemPtr DISP_SIMPLE= make(BitsAlias.RECORD_BITS0,TypeObj.ISUSED); // closed display
  static final Type[] TYPES = new Type[]{OOP0,STR0,STRPTR,ABCPTR,STRUCT,EMTPTR,DISPLAY,DISPLAY_PTR};

  @Override public boolean is_display_ptr() {
    BitsAlias x = _aliases.strip_nil();
    if( x==BitsAlias.EMPTY ) return true; // Just a NIL
    int alias1 = x.abit();                 // Just a single alias
    // The GENERIC function allows the generic record, otherwise must be on the display list
    if( alias1 != -1 )
      return Math.abs(alias1)==BitsAlias.REC || com.cliffc.aa.Env.ALL_DISPLAYS.test_recur(Math.abs(alias1));
    // If closures are being used, can be multiple valid displays
    for( int alias : _aliases )
      if( alias != 0 && !com.cliffc.aa.Env.ALL_DISPLAYS.test_recur(alias) )
        return false;           // This alias is not on the DISPLAYS list
    return true;
  }

  @Override protected TypeMemPtr xdual() {
    BitsAlias ad = _aliases.dual();
    TypeObj od = (TypeObj)_obj.dual();
    if( ad==_aliases && od==_obj )
      return this;              // Centerline TMP
    return new TypeMemPtr().init(ad,od);
  }
  @Override TypeMemPtr rdual() {
    if( _dual != null ) return _dual;
    TypeMemPtr dual = _dual = new TypeMemPtr().init(_aliases.dual(),(TypeObj)_obj.rdual());
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
    case TARY:
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
    return make(aliases, to);
  }
  // Widens, not lowers.
  @Override public Type simple_ptr() {
    if( _obj==TypeObj.ISUSED || _obj==TypeObj.UNUSED ) return this;
    return make(_aliases,_aliases.above_center() ? TypeObj.UNUSED : TypeObj.ISUSED);
  }
  @Override public boolean above_center() {
    return _aliases.above_center();
  }
  @Override public Type oop_deep_impl(Type t) {
    if( !(t instanceof TypeMemPtr) ) return oob();
    TypeMemPtr tmp = (TypeMemPtr)t;
    // Deep bounds; keep the in-bounds _aliases but bound the _obj.
    if( tmp._aliases.dual().isa(_aliases) && _aliases.isa(tmp._aliases) )
      return _obj.oop_deep_impl(tmp._obj);
    // Aliases OOB
    return oob();
  }
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
  @Override public Type meet_nil(Type nil) {
    assert nil==NIL || nil==XNIL;
    // See testLattice15.  The UNSIGNED NIL tests as a lattice:
    //    [~0]->~obj  ==>  NIL  ==>  [0]-> obj
    // But loses the pointed-at type down to OBJ.
    // So using SIGNED NIL, which also tests as a lattice:
    //    [~0]->~obj ==>  XNIL  ==>  [0]->~obj
    //    [~0]-> obj ==>   NIL  ==>  [0]-> obj

    if( _aliases.isa(BitsAlias.XNIL) ) {
      if( _obj.above_center() && nil==XNIL )  return XNIL;
      if( nil==NIL ) return NIL;
    }
    return make(_aliases.meet(BitsAlias.NIL),_obj);
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

  // Only used for testing.  Build a mapping from types to their depth in a
  // shortest-path walk from the root.  Only counts depth on TypeStructs with
  // the matching alias.
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
          for( TypeFld fld : ts.flds() ) {
            if( ds.putIfAbsent(fld._t,d) == null &&  // Everything in flds is in the current depth
                fld._t instanceof TypeMemPtr ) {
              TypeMemPtr tmp = (TypeMemPtr)fld._t;
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

  // Only used for testing.  Max depth of struct, with a matching alias TMP.
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
    if( t == Type.SCALAR ) return 0; // Scalar function arg; generally dead or just passed along blindly.
    return (byte)(t instanceof TypeMemPtr ? 0 : 99);  // Mixing TMP and a non-ptr
  }
  @SuppressWarnings("unchecked")
  @Override public void walk( Predicate<Type> p ) { if( p.test(this) ) _obj.walk(p); }
  public int getbit() { return _aliases.getbit(); }
  public int getbit0() { return _aliases.strip_nil().getbit(); }

  // Widen for primitive specialization and H-M unification.  H-M distinguishes
  // ptr-to-array (and string) from ptr-to-record.  Must keep types at the same
  // resolution as H-M, so pointers all permit nil (unless I track a H-M type
  // which disallows nil).
  @Override public TypeMemPtr widen() {
    // Flatten to either all-structs or all-strings, unless both.
    BitsAlias bs = null;
    if( _aliases.isa(BitsAlias.RECORD_BITS0) )  bs = BitsAlias.RECORD_BITS0;
    if( _aliases.isa(BitsAlias.STRBITS0) ) bs = bs==null ? BitsAlias.STRBITS0 : BitsAlias.FULL;
    if( _aliases.isa(BitsAlias.ARYBITS0) ) bs = bs==null ? BitsAlias.ARYBITS0 : BitsAlias.FULL;
    if( bs==null ) return this; // Already plenty wide
    return make(bs,_obj.widen());
  }

  // Make a Type, replacing all dull pointers from the matching types in mem.
  @Override public Type make_from(Type head, TypeMem mem, VBitSet visit) {
    if( this!=head ) {
      TypeObj[] pubs = mem.alias2objs();
      boolean mapped=true;
      for( int alias : _aliases )
        if( pubs[alias]==null )
          { mapped=false; break; }
      if( mapped ) {
        TypeObj obj = mem.ld(this);
        if( obj!=TypeObj.XOBJ )
          return make_from(obj);
      }
    }
    TypeObj obj = (TypeObj)_obj.make_from(head,mem,visit);
    return obj == null ? this : make_from(obj);
  }

  // Used for assertions
  @Override boolean intern_check1() { return _obj.intern_lookup()!=null; }

}
