package com.cliffc.aa.type;

import com.cliffc.aa.AA;

import java.util.BitSet;
import java.util.HashMap;
import java.util.function.Consumer;
import java.util.function.Predicate;

// Named types are essentially a subclass of the named type.
// They also must be used to make recursive types.
public class TypeName extends TypeObj<TypeName> {
  public  String _name;
  public  HashMap<String,Type> _lex; // Lexical scope of this named type
  public  Type _t;                // Named type
  private short _depth; // Nested depth of TypeNames, or -1/ for a forward-ref type-var, -2 for type-cycle head
  // Named type variable
  private TypeName ( String name, HashMap<String,Type> lex, Type t, short depth ) { super(TNAME,false); init(name,lex,t,depth); }
  private void init( String name, HashMap<String,Type> lex, Type t, short depth ) { super.init(TNAME,false); assert name!=null && lex !=null; _name=name; _lex=lex; _t=t; _depth = depth; }
  private static short depth( Type t ) { return(short)(t instanceof TypeName ? ((TypeName)t)._depth+1 : 0); }
  // Hash does not depend on other types.
  // No recursion on _t to break type cycles
  @Override int compute_hash() { return super.compute_hash() + _name.hashCode(); }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeName) ) return false;
    TypeName t2 = (TypeName)o;
    if( _lex != t2._lex  || !_name.equals(t2._name) || _t!=t2._t ) return false;
    if( _depth==t2._depth ) return true;
    // Also return true for comparing TypeName(name,type) where the types
    // match, but the 'this' TypeName is depth 0 vs depth -1 - this detects
    // simple cycles and lets the interning close the loop.
    return (t2._depth<0 ? 0 : t2._depth) == (_depth<0 ? 0 :_depth);
  }
  @Override public boolean cycle_equals( Type o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeName) ) return false;
    TypeName t2 = (TypeName)o;
    if( _lex != t2._lex  || !_name.equals(t2._name) ) return false;
    if( _t!=t2._t && !_t.cycle_equals(t2._t) ) return false;
    if( _depth==t2._depth ) return true;
    // Also return true for comparing TypeName(name,type) where the types
    // match, but the 'this' TypeName is depth 0 vs depth -1 - this detects
    // simple cycles and lets the interning close the loop.
    return (t2._depth<0 ? 0 : t2._depth) == (_depth<0 ? 0 :_depth);
  }
  @Override String str( BitSet dups) {
    if( _depth < 0 ) {          // Only for recursive-type-heads
      if( dups == null ) dups = new BitSet();
      else if( dups.get(_uid) ) return _name; // Break recursive cycle
      dups.set(_uid);
    }
    return _name+":"+_t.str(dups);
  }
  
  private static TypeName FREE=null;
  @Override protected TypeName free( TypeName ret ) { FREE=this; return ret; }
  private static TypeName make0( String name, HashMap<String,Type> lex, Type t, short depth) {
    assert !(t instanceof TypeNil); // No named nils (but ok to nil a named type)
    TypeName t1 = FREE;
    if( t1 == null ) t1 = new TypeName(name,lex,t,depth);
    else { FREE = null; t1.init(name,lex,t,depth); }
    TypeName t2 = (TypeName)t1.hashcons();
    // Close some recursions: keep -2 and -1 depths vs 0
    if( t1._depth < t2._depth )
      t2._depth = t1._depth;    // keep deeper depth
    return t1==t2 ? t1 : t1.free(t2);
  }

  public static TypeName make( String name, HashMap<String,Type> lex, Type t) {
    TypeName tn0 = make0(name,lex,t,depth(t));
    TypeName tn1 = (TypeName)lex.get(name);
    if( tn1==null || tn1._depth!= -2 || RECURSIVE_MEET>0 ) return tn0;
    return tn0.make_recur(tn1,0,new BitSet());
  }
  public TypeName make( Type t) { return make(_name,_lex,t); }
  public static TypeName make_forward_def_type( String name, HashMap<String,Type> lex ) { return make0(name,lex,Type.SCALAR,(short)-1); }

          static final HashMap<String,Type> TEST_SCOPE = new HashMap<>();
          static final TypeName TEST_ENUM = make("__test_enum",TEST_SCOPE,TypeInt.INT8);
  private static final TypeName TEST_FLT  = make("__test_flt" ,TEST_SCOPE,TypeFlt.FLT32);
  private static final TypeName TEST_E2   = make("__test_e2"  ,TEST_SCOPE,TEST_ENUM);
  public  static final TypeName TEST_STRUCT=make("__test_struct",TEST_SCOPE,TypeStruct.POINT);
  
  static final TypeName[] TYPES = new TypeName[]{TEST_ENUM,TEST_FLT,TEST_E2,TEST_STRUCT};

  @Override protected TypeName xdual() { return new TypeName(_name,_lex,_t. dual(),_depth); }
  @Override TypeName rdual() {
    if( _dual != null ) return _dual;
    TypeName dual = _dual = new TypeName(_name,_lex,_t.rdual(),_depth);
    dual._dual = this;
    dual._cyclic = true;
    return dual;
  }
  @Override protected Type xmeet( Type t ) {
    assert !(base() instanceof TypeNil); // No name-wrapping-nils
    switch( t._type ) {
    case TNIL:
      // Cannot swap args and go again, because it screws up the cyclic_meet.
      // This means we handle name-meet-nil right here.
      //return t.xmeet(this);
      if( t == TypeNil.NIL ) return meet_nil();
      Type nmt = meet(((TypeNil)t)._t);
      return t.above_center() ? nmt : TypeNil.make(nmt);

    case TNAME:
      TypeName tn = (TypeName)t;
      int thisd =    _depth<0 ? 0 :   _depth;
      int thatd = tn._depth<0 ? 0 : tn._depth;
      if( thatd > thisd ) return tn.xmeet(this); // Deeper on 'this'
      if( thatd== thisd && _name.equals(tn._name) )
        return make(_name,_lex,_t.meet(tn._t)); // Peel name and meet
      t = tn.drop_name(t);      // Names or depth unequal; treat as unnamed
      break;
    default:
      if( t.above_center() ) { // t is high
        Type mt = _t.meet(t);  // If meet fails to be anything, drop the name
        if( mt==ALL ) return ALL;
        if( mt==SCALAR || mt==NSCALR ) return SCALAR;
        if( mt==TypeObj.OBJ ) return TypeObj.OBJ;
        return make(_name,_lex,mt);
      }
      if( t==TypeNil.NIL ) return TypeNil.make(this);
      // Special case: close the recursive type loop, instead of falling
      if( _t==t && _depth == -2 )
        return this;
    }
    Type t0 = drop_name(t);
    return t0.meet(t);
  }

  // Drop in lattice, until we can drop the name.  Generally means we must drop
  // from above_center to exactly 1 step below center.  Types already below
  // center can just drop the name, which drops them 1 step in the lattice.
  private Type drop_name(Type t) {
    Type tx = _t;
    if( !tx.may_be_con() ) return tx; // Already below centerline; can just drop the name
    // If at or above the centerline, just dropping the name amounts to a
    // lift/join of the type - not allowed, can only fall.
    switch( tx._type ) {
    case TXNUM: case TXNNUM: case TXREAL: case TXNREAL: case TINT: case TFLT: {
      // Return a number that is not-null (to preserve any not-null-number
      // property) but forces a move off the centerline.
      return must_nil() ? TypeInt.BOOL : TypeInt.TRUE;
    }
    // Recursively drop multiple names
    case TNAME:    return ((TypeName)tx).drop_name(t);
    case TXSCALAR:
    case TXNSCALR: return t;
    case TOBJ:
    case TSTRUCT:  return tx.dual();
    default: throw AA.unimpl();
    }
  }
  
  // 'this' is a forward ref type definition; the actual type-def is 't' which
  // may include embedded references to 'this'
  @Override public TypeName merge_recursive_type( Type t ) {
    if( _depth >= 0 ) return null; // Not a recursive type-def
    assert _t==Type.SCALAR;
    // Remove from INTERN table, since hacking type will not match hash
    untern()._dual.untern();
    // Hack type and it's dual.  Type is now recursive.
    _t = t;
    _dual._t = t._dual;
    _depth = _dual._depth = -2;
    // Flag all as cyclic
    t.mark_cycle(this,new BitSet(),new BitSet());
    // Back into the INTERN table
    retern()._dual.retern();

    return this;
  }

  @Override public boolean above_center() { return _t.above_center(); }
  @Override public boolean may_be_con() { return _depth >= 0 && _t.may_be_con(); }
  @Override public boolean is_con()   { return _depth >= 0 && _t.is_con(); } // No recursive structure is a constant
  @Override public double getd  () { return _t.getd  (); }
  @Override public long   getl  () { return _t.getl  (); }
  @Override public String getstr() { return _t.getstr(); }
  @Override public boolean must_nil() { return _t.above_center() || _t.must_nil(); }
  @Override Type not_nil() {
    Type nn = _t.not_nil();
    if( base().must_nil() ) return nn; // Cannot remove all nils and keep the name, so lose the name
    return make(_name,_lex,nn);
  }
  @Override public Type meet_nil() {
    Type x = _t.meet_nil();     // Compute meet-nil without the name
    if( x instanceof TypeNil ) return TypeNil.make(TypeName.make(_name,_lex,((TypeNil)x)._t));
    else                       return              TypeName.make(_name,_lex,          x); // Just name-wrap
  }
  @Override public TypeObj startype() {
    return make(_name,_lex,_t.startype());
  }
  @Override public byte isBitShape(Type t) {
    if( t instanceof TypeNil ) t = ((TypeNil)t)._t; // Strip nil and go again
    if( t instanceof TypeName ) {
      if( ((TypeName)t)._name.equals(_name) ) return _t.isBitShape(((TypeName)t)._t);
      return 99; // Incompatible names do not mix
    }
    return _t.isBitShape(t); // Strip name and try again
  }
  @Override TypeName make_recur(TypeName tn, int d, BitSet bs ) {
    if( bs.get(_uid) ) return this; // Looping on some other recursive type
    bs.set(_uid);
    // Make a (possibly cyclic & infinite) named type.  Prevent the infinite
    // unrolling of names by not allowing a named-type with depth >= D from
    // holding (recursively) the head of a named-type cycle.  We need to cap the
    // unroll, to prevent loops/recursion from infinitely unrolling.
    int D = 5;
    if( _lex==tn._lex && _name.equals(tn._name) && d++ == D )
      return above_center() ? tn.dual() : tn;
    Type t2 = _t.make_recur(tn,d,bs);
    return t2==_t ? this : make0(_name,_lex,t2,_depth);
  }
  // Mark if part of a cycle
  @Override void mark_cycle( Type head, BitSet visit, BitSet cycle ) {
    if( visit.get(_uid) ) return;
    visit.set(_uid);
    if( this==head ) { cycle.set(_uid); _cyclic=_dual._cyclic=true; }
    _t.mark_cycle(head,visit,cycle);
    if( cycle.get(_t._uid) )
      { cycle.set(_uid); _cyclic=_dual._cyclic=true; }
  }

  // Iterate over any nested child types
  @Override public void iter( Consumer<Type> c ) { c.accept(_t); }
  @Override boolean contains( Type t, BitSet bs ) { return _t == t || _t.contains(t, bs); }
  @Override int depth( BitSet bs ) { return 1+_t.depth(bs); }
  @SuppressWarnings("unchecked")
  @Override Type replace( Type old, Type nnn, HashMap<Type,Type> MEETS  ) {
    Type x = _t.replace(old,nnn,MEETS);
    if( x==_t ) return this;
    Type rez = make(_name,_lex,x);
    rez._cyclic=true;
    return rez;
  }

  @SuppressWarnings("unchecked")
  @Override void walk( Predicate<Type> p ) { if( p.test(this) ) _t.walk(p); }
  @Override TypeStruct repeats_in_cycles(TypeStruct head, BitSet bs) { return _cyclic ? _t.repeats_in_cycles(head,bs) : null; }
}
