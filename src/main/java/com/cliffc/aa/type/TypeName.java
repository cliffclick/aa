package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.Util;
import com.cliffc.aa.util.VBitSet;

// Named types are essentially a subclass of the named type.
// They also must be used to make recursive types.  Examples:
//   A.B.int << B.int << int   // Subtypes
//     B.int.isa(int)
//   A.B.int.isa(B.int)
//     C.int.meet(B.int) == int
//   A.B.int.meet(C.int) == int
//
//   A.B.~int.join(B.~int) == A.B.~int
//     C.~int.join(B.~int) ==     ~int
//
//   B. int.meet(  ~int) == B. int.meet(B.~int) == B.int
//   B.~int.meet(   int) ==    int
//   B.~int.meet(C. int) ==    int
//   B.~int.meet(B. int) == B. int
//   B.~int.meet(C.~int) ==    int // Nothing in common, fall to int
//   B.~int.meet(  ~int) == B.~int
// A.B.~int.meet(B.~int) == A.B.~int // both high, keep long; short guy high, keep long
// A.B.~int.meet(B. int) ==   B. int // one low, keep low   ; short guy  low, keep short
// A.B. int.meet(B.~int) == A.B. int // one low, keep low   ; short guy high, keep long
// A.B. int.meet(B. int) ==   B. int // both low, keep short; short guy  low, keep short
//
// A.B.~int.meet(D.B.~int) == B.int // Nothing in common, fall to int

public class TypeName extends TypeObj<TypeName> {
  public  String _name;         // Name!
  public  int _lex;             // Unique type-name number, which is also an alias so overloads TypeMemPtr
  public  Type _t;              // Named type
  public  short _depth;         // Nested depth of TypeNames
  // Named type variable
  private TypeName ( String name, Type t, short depth ) { super(TNAME,false); init(name,t,depth); }
  private void init( String name, Type t, short depth ) {
    super.init(TNAME,false);
    assert name!=null;
    _name=name; _lex = -99; _t=t; _depth = depth; assert depth >= -1;
  }
  private static short depth( Type t ) { return(short)(t instanceof TypeName ? ((TypeName)t)._depth+1 : 0); }
  int pdepth() { return Math.max(0,_depth); }
  @Override int compute_hash() { assert _lex != -99 && _t._hash != 0; return super.compute_hash() + _name.hashCode() + _lex + _t._hash; }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeName) ) return false;
    TypeName t2 = (TypeName)o;
    return _lex == t2._lex && Util.eq(_name,t2._name) && _t==t2._t && _depth == t2._depth;
  }
  @Override String str( VBitSet dups) { return _name+":"+_t.str(dups); }
  @Override SB dstr( SB sb, VBitSet dups ) { return _t.dstr(sb.p('_').p(_uid).p(_name).p(':'),dups); }

  private static TypeName FREE=null;
  @Override protected TypeName free( TypeName ret ) { FREE=this; return ret; }
  private static TypeName malloc( String name, Type t, short depth) {
    TypeName t1 = FREE;
    if( t1 == null ) t1 = new TypeName(name,t,depth);
    else { FREE = null;        t1.init(name,t,depth); }
    return t1;
  }
  private TypeName hashcons(int lex) {
    _lex = lex;
    TypeName t2 = (TypeName)hashcons();
    return this==t2 ? this : free(t2);
  }
  public static TypeName make( String name, int lex, Type t) { return malloc(name,t,depth(t)).hashcons(lex); }
  public static TypeName make_new_type( String name, Type t) {
    TypeName tn = malloc(name,t,depth(t));
    return tn.hashcons(BitsAlias.type_alias(BitsAlias.REC,tn));
  }
  // Make a duplicate with the new alias
  public TypeName make(int alias) {
    return make(_name,alias,_t);
  }

  public static TypeName make_forward_def_type( String name ) {
    TypeName tn = malloc(name,TypeStruct.ALLSTRUCT,(short)-1);
    return tn.hashcons(BitsAlias.type_alias(BitsAlias.REC,tn));
  }
  public TypeName make( Type t) { return malloc(_name,t,_depth).hashcons(_lex); }

          static final TypeName TEST_ENUM = make_new_type("__test_enum"  ,TypeInt.INT8);
          static final TypeName TEST_FLT  = make_new_type("__test_flt"   ,TypeFlt.FLT32);
          static final TypeName TEST_E2   = make_new_type("__test_e2"    ,TEST_ENUM);
  public  static final TypeName TEST_STRUCT=make_new_type("__test_struct",TypeStruct.POINT);

  static final TypeName[] TYPES = new TypeName[]{TEST_ENUM,TEST_FLT,TEST_E2,TEST_STRUCT};

  @Override protected TypeName xdual() { TypeName tn = new TypeName(_name,_t. dual(),_depth); tn._lex = _lex; return tn; }
  //@Override TypeName rdual() {
  //  if( _dual != null ) return _dual;
  //  TypeName dual = _dual = new TypeName(_name,_lex,_t.rdual(),_depth);
  //  dual._dual = this;
  //  dual._hash = compute_hash();
  //  dual._cyclic = true;
  //  return dual;
  //}
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TNIL:
      // Cannot swap args and go again, because it screws up the cyclic_meet.
      // This means we handle name-meet-nil right here.
      return meet_nil();

    case TNAME:
      // Matching inner names can be kept.  If one side is an extension of the
      // other, we keep the low-side prefix (long or short).  If there is no
      // match on a name, then the result must fall- even if both inner types
      // and names are the same (but high).
      TypeName tn = (TypeName)t;
      // Recursive on depth until depths are equal
      if( _depth > tn._depth ) return extend(t);
      if( tn._depth > _depth ) return tn.extend(this);
      Type mt = _t.meet(tn._t);
      if( _name.equals(tn._name) )   // Equal names?
        return make(mt);             // Peel name and meet
      // Unequal names
      if( !mt.above_center() ) return mt;
      // Unequal high names... fall to the highest value below-center
      return off_center(mt);

    default:
      return extend(t);
    }
  }

  // Longer side is 'this'.  Shorter side is 't'.
  private Type extend(Type t) {
    Type x = _t.meet(t); // Recursive, removing longer name
    int xnd = x instanceof TypeName ? ((TypeName)x)._depth : -1;
    int tnd = t instanceof TypeName ? ((TypeName)t)._depth : -1;
    if( xnd < tnd ) return x; // No common prefix
    if( x==Type.ALL || x==Type.NSCALR || x==Type.SCALAR || x==TypeObj.OBJ ) return x;
    // Same strategy as TypeStruct and extra fields...
    // short guy high, keep long
    // short guy  low, keep short
    if( t.above_center() ) return make(x);
    // Fails lattice if 'x' is a constant because cannot add names...
    // Force 'x' to not be a constant.
    return off_center(x);
  }

  // Must fall to the 1st thing just below center
  private static Type off_center(Type mt) {
    if( !mt.above_center() && !mt.is_con() ) return mt; // Already below-center
    switch( mt._type ) {
    case TXNUM: case TXNNUM: case TXREAL: case TXNREAL:
    case TINT:  case TFLT:
      // Return a number that is not-null (to preserve any not-null-number
      // property) but forces a move off the centerline.
      return mt.must_nil() ? TypeInt.BOOL : TypeInt.make(-1,1,1);
    case TNAME:
      return mt;
    case TSTRUCT:
      return mt;
    default: throw AA.unimpl();
    }
  }

  // 'this' is a forward ref type definition; the actual type-def is 't' which
  // may include embedded references to 'this'
  public TypeName merge_recursive_type( Type t ) {
    if( _depth >= 0 ) return null; // Not a recursive type-def
    assert _t==TypeStruct.ALLSTRUCT;
    // Remove from INTERN table, since hacking type will not match hash
    untern()._dual.untern();
    // Hack type and it's dual.  Type is now recursive.
    _t = t;
    _depth = _dual._depth = depth(t);
    _dual._t = t._dual;
    _hash  = _dual._hash  = 0;  // Trigger any asserts
    _hash = compute_hash();
    _dual._hash = _dual.compute_hash();
    // Back into the INTERN table
    retern()._dual.retern();

    return this;
  }

  @Override public TypeObj lift_final() { return _t instanceof TypeObj ? make(((TypeObj)_t).lift_final()) : this; }
  @Override public boolean above_center() { return _t.above_center(); }
  @Override public boolean may_be_con() { return _t.may_be_con(); }
  @Override public boolean is_con()   { return _t.is_con(); }
  @Override public double getd  () { return _t.getd  (); }
  @Override public long   getl  () { return _t.getl  (); }
  @Override public String getstr() { return _t.getstr(); }
  @Override public boolean must_nil() { return _t.must_nil(); }
  @Override Type not_nil() { return make(_t.not_nil()); }
  // Since meeting an unnamed NIL, end result is never high and never named
  @Override public Type meet_nil() { return _t.meet_nil(); }
  @Override public TypeObj startype() { return make(_t.startype()); }
  @Override public byte isBitShape(Type t) {
    if( t instanceof TypeName ) {
      if( ((TypeName)t)._name.equals(_name) ) return _t.isBitShape(((TypeName)t)._t);
      return 99; // Incompatible names do not mix
    }
    return _t.isBitShape(t); // Strip name and try again
  }
  //@Override TypeName make_recur(TypeName tn, int d, VBitSet bs ) {
  //  if( bs.get(_uid) ) return this; // Looping on some other recursive type
  //  bs.set(_uid);
  //  // Make a (possibly cyclic & infinite) named type.  Prevent the infinite
  //  // unrolling of names by not allowing a named-type with depth >= D from
  //  // holding (recursively) the head of a named-type cycle.  We need to cap the
  //  // unroll, to prevent loops/recursion from infinitely unrolling.
  //  int D = 5;
  //  if( _lex==tn._lex && _name.equals(tn._name) && d++ == D )
  //    return above_center() ? tn.dual() : tn;
  //  Type t2 = _t.make_recur(tn,d,bs);
  //  return t2==_t ? this : make(t2);
  //}
  //// Mark if part of a cycle
  //@Override void mark_cycle( Type head, VBitSet visit, BitSet cycle ) {
  //  if( visit.tset(_uid) ) return;
  //  if( this==head ) { cycle.set(_uid); _cyclic=_dual._cyclic=true; }
  //  _t.mark_cycle(head,visit,cycle);
  //  if( cycle.get(_t._uid) )
  //    { cycle.set(_uid); _cyclic=_dual._cyclic=true; }
  //}

  // Iterate over any nested child types
  //@Override public void iter( Consumer<Type> c ) { c.accept(_t); }
  @Override boolean contains( Type t, VBitSet bs ) { return _t == t || _t.contains(t, bs); }
  //@SuppressWarnings("unchecked")
  //@Override int depth( NonBlockingHashMapLong<Integer> ds ) { return _t.depth(ds); }
  //@SuppressWarnings("unchecked")
  //@Override void walk( Predicate<Type> p ) { if( p.test(this) ) _t.walk(p); }
  //@Override TypeStruct repeats_in_cycles(TypeStruct head, VBitSet bs) { return _cyclic ? _t.repeats_in_cycles(head,bs) : null; }
}
