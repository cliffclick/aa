package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.node.ScopeNode;

import java.util.BitSet;

// Named types are essentially a subclass of the named type.
// They also must be used to make recursive types.
public class TypeName extends Type<TypeName> {
  public  String _name;
  public  ScopeNode _lex;         // Lexical scope of this named type
  public  Type _t;                // Named type
  private short _depth; // Nested depth of TypeNames, or -1/ for a forward-ref type-var, -2 for type-cycle head
  // Named type variable
  private TypeName ( String name, ScopeNode lex, Type t, short depth ) { super(TNAME); init(name,lex,t,depth); }
  private void init( String name, ScopeNode lex, Type t, short depth ) { assert name!=null && lex !=null; _name=name; _lex=lex; _t=t; _depth = depth; }
  private static short depth( Type t ) { return(short)(t instanceof TypeName ? ((TypeName)t)._depth+1 : 0); }
  @Override public int hashCode( ) { return TNAME+_name.hashCode();  } // No recursion on _t to break type cycles
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
  private static TypeName make0( String name, ScopeNode lex, Type t, short depth) {
    assert !(t instanceof TypeNil); // No named nils (but ok to nil a named type)
    TypeName t1 = FREE;
    if( t1 == null ) t1 = new TypeName(name,lex,t,depth);
    else { FREE = null; t1.init(name,lex,t,depth); }
    TypeName t2 = (TypeName)t1.hashcons();
    // Close some recursions: keep -2 and -1 depths vs 0
    if( t1!=t2 && t1._depth < t2._depth )
      t2._depth = t1._depth;    // If equals() on depth, then keep deeper depth
    return t1==t2 ? t1 : t1.free(t2);
  }
  // Make a (posssibly cyclic & infinite) named type.  Prevent the infinite
  // unrolling of names by not allowing a named-type with depth >= D from
  // holding (recursively) the head of a named-type cycle.  We need to cap the
  // unroll, to prevent loops/recursion from infinitely unrolling.
  private static int D=0;
  public static TypeName make( String name, ScopeNode lex, Type t) {
    TypeName tn0 = make0(name,lex,t,depth(t));
    TypeName tn1 = (TypeName)lex.get_type(name);
    if( tn1==null || tn1._depth!= -2 ) return tn0;
    return tn0.make_recur(tn1,0,new BitSet());
  }
  @Override TypeName make_recur(TypeName tn, int d, BitSet bs ) {
    if( bs.get(_uid) ) return this; // Looping on some other recursive type
    bs.set(_uid);
    if( _lex==tn._lex && _name.equals(tn._name) )
      if( d++ == D ) return above_center() ? tn.dual() : tn;
    Type t2 = _t.make_recur(tn,d,bs);
    return t2==_t ? this : make0(_name,_lex,t2,_depth);
  }
  public static TypeName make_forward_def_type( String name, ScopeNode lex ) { return make0(name,lex,Type.SCALAR,(short)-1); }
  public        boolean is_forward_def_type( ) { return _depth==-1; }

  public  static final ScopeNode TEST_SCOPE = new ScopeNode();
  public  static final TypeName TEST_ENUM = make("__test_enum",TEST_SCOPE,TypeInt.INT8);
  private static final TypeName TEST_FLT  = make("__test_flt" ,TEST_SCOPE,TypeFlt.FLT32);
  private static final TypeName TEST_E2   = make("__test_e2"  ,TEST_SCOPE,TEST_ENUM);
  
  static final TypeName[] TYPES = new TypeName[]{TEST_ENUM,TEST_FLT,TEST_E2};

  @Override protected TypeName xdual() { return new TypeName(_name,_lex,_t.dual(),_depth); }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TNAME:
      TypeName tn = (TypeName)t;
      int thisd =    _depth<0 ? 0 :   _depth;
      int thatd = tn._depth<0 ? 0 : tn._depth;
      if( thatd > thisd ) return tn.xmeet(this); // Deeper on 'this'
      if( thatd== thisd && _name.equals(tn._name) )
        return make(_name,_lex,_t.meet(tn._t)); // Peel name and meet
      t = tn.drop_name();       // Names or depth unequal; treat as unnamed
      break;
    default:
      if( t.above_center() ) { // 't' can fall to a matching name
        if( t.isa(_t) ) return make(_name,_lex,_t.meet(t));
      }
      if( t==TypeNil.NIL ) return TypeNil.make(this);
      // Special case: close the recursive type loop, instead of falling
      if( _t==t && _depth == -2 )
        return this;
    }
    Type t0 = drop_name();
    return t0.meet(t);
  }

  // Drop in lattice, until we can drop the name.  Generally means we must drop
  // from above_center to exactly 1 step below center.  Types already below
  // center can just drop the name, which drops them 1 step in the lattice.
  private Type drop_name() {
    Type t = _t;
    if( !t.may_be_con() ) return t; // Already below centerline; can just drop the name
    // If at or above the centerline, just dropping the name amounts to a
    // lift/join of the type - not allowed, can only fall.
    switch( t._type ) {
    case TXNUM: case TXREAL: case TINT: case TFLT:
      return TypeInt.BOOL;      // Least number below the centerline
    // Recursively drop multiple names
    case TNAME: return ((TypeName)t).drop_name();
    case TXSCALAR: return TypeNil.NIL;
    default: throw AA.unimpl();
    }
  }
  
  // 'this' is a forward ref type definition; the actual type-def is 't' which
  // may include embedded references to 'this'
  @Override public TypeName merge_recursive_type( Type t ) {
    if( _depth >= 0 ) return null; // Not a recursive type-def
    assert _t==Type.SCALAR;
    // Remove from INTERN table, since hacking type will not match hash
    untern();
    _dual.untern();
    // Hack type and it's dual.  Type is now recursive.
    _t = t;
    _dual._t = t._dual;
    _depth = _dual._depth = -2;
    // Back into the INTERN table
    retern();
    _dual.retern();
    return this;
  }
  
  @Override public boolean above_center() { return _t.above_center(); }
  @Override public boolean may_be_con() { return _depth >= 0 && _t.may_be_con(); }
  @Override public boolean is_con()   { return _depth >= 0 && _t.is_con(); } // No recursive structure is a constant
  @Override public double getd  () { return _t.getd  (); }
  @Override public long   getl  () { return _t.getl  (); }
  @Override public String getstr() { return _t.getstr(); }
  @Override public byte isBitShape(Type t) {
    if( t instanceof TypeName ) {
      if( ((TypeName)t)._name.equals(_name) ) return _t.isBitShape(((TypeName)t)._t);
      return 99; // Incompatible names do not mix
    }
    return _t.isBitShape(t); // Strip name and try again
  }
}
