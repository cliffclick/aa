package com.cliffc.aa.type;

import com.cliffc.aa.util.*;
import org.jetbrains.annotations.NotNull;

import java.util.function.*;

import static com.cliffc.aa.AA.DSP_IDX;


// A field in a TypeStruct, with a type and a name and an Access.  Field
// accesses make a small lattice of: {choice,r/w,final,r-o}.  Note that mixing
// r/w and final moves to r-o and loses the final property.  No field order.
public class TypeFld extends Type<TypeFld> implements Cyclic {
  // Field names are never null, and never zero-length.  Names can be fldTop or fldBot.
  public String _fld;           // The field name
  public Type _t;               // Field type.  Usually some type of Scalar, or ANY or ALL.
  public Access _access;        // Field access type: read/write, final, read/only
  public int _order;            // Field order in the struct, or -1 for undefined (Bot) or -2 for conforming (top)
  boolean _cyclic; // Type is cyclic.  This is a summary property, not a part of the type, hence is not in the equals nor hash

  private TypeFld init( @NotNull String fld, Type t, Access access, int order ) {
    assert !(t instanceof TypeFld);
    super.init("");
    _cyclic = false;
    _fld=fld; _t=t; _access=access;
    _order=oBot;//order; // Claim 'order' is not a property of types; instead field layout is a backend property.
    return this;
  }
  @Override public TypeFld copy() { return _copy().init(_fld,_t,_access,_order); }

  @Override public boolean cyclic() { return _cyclic; }
  @Override public void set_cyclic() { _cyclic = true; }
  @Override public void clr_cyclic() { _cyclic = false; }
  @Override public <T> T walk1( BiFunction<Type,String,T> map, BinaryOperator<T> reduce ) { return map.apply(_t,"t"); }
  @Override public void walk_update( UnaryOperator<Type> map ) { _t = map.apply(_t); }
  @Override public Cyclic.Link _path_diff0(Type t, NonBlockingHashMapLong<Link> links) {
    return Cyclic._path_diff(_t,((TypeFld)t)._t,links);
  }

  // Ignore edges hash
  int _hash() { return Util.hash_spread(super.static_hash() + _fld.hashCode() + _access.hashCode( ) + _order); }
  @Override int  static_hash() { return _hash(); } // No edges
  @Override int compute_hash() { assert _t._hash!=0; return _hash() + _t._hash; } // Always edges

  // Returns 1 for definitely equals, 0 for definitely unequals and -1 for needing the circular test.
  int cmp(TypeFld t) {
    if( this==t ) return 1;
    if( !Util.eq(_fld,t._fld) || _access!=t._access || _order!=t._order ) return 0; // Definitely not equals without recursion
    if( _t==t._t ) return 1;    // All fields bitwise equals.
    if( _t==null || t._t==null ) return 0; // Mid-construction (during cycle building), declare unequal
    if( _t._type!=t._t._type ) return 0; // Last chance to avoid cycle check; types have a chance of being equal
    // Some type pointer-not-equals, needs a cycle check
    return -1;
  }

  // Static properties equals; not-interned edges are ignored.
  // 0 is false, either 1 or -1 is true.
  @Override boolean static_eq(TypeFld t) { return cmp(t)!=0; }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFld) ) return false;
    // Check for obviously equals or not-equals
    int x = cmp((TypeFld)o);
    return x==-1 ? cycle_equals((TypeFld)o) : (x==1);
  }

  @Override public boolean cycle_equals( Type o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFld) ) return false;
    int cmp = cmp((TypeFld)o);
    if( cmp!= -1 ) return cmp==1;
    return _t.cycle_equals(((TypeFld)o)._t);
  }

  @SuppressWarnings("unchecked")
  @Override void _str_dups( VBitSet visit, NonBlockingHashMapLong<String> dups, UCnt ucnt ) {
    if( visit.tset(_uid) ) {
      if( !dups.containsKey(_uid) )
        dups.put(_uid,"F"+(char)('A'+ucnt._fld++));
      return;
    }
    if( _t!=null ) _t._str_dups(visit,dups,ucnt);
  }

  @SuppressWarnings("unchecked")
  @Override SB _str0( VBitSet visit, NonBlockingHashMapLong<String> dups, SB sb, boolean debug, boolean indent ) {
    if( !TypeStruct.isDigit(_fld.charAt(0)) ) // Do not print number-named fields for tuples
      _access.str(sb.p(_fld));
    return _t==null ? sb.p('!') : (_t._str(visit, dups, sb, debug, indent));
  }

  static TypeFld valueOfArg(Parse P, int order, String fid) {
    int oldx=P._x;
    String id = P.id();
    if( !P.peek('=') ) { assert fid==null; P._x=oldx; return null; } // No such field
    return _valueOf(P,order,fid,id);
  }
  static TypeFld valueOfTup(Parse P, int order, String fid) {  return _valueOf(P,order,fid,TUPS[order]);  }
  static TypeFld _valueOf(Parse P, int order, String fid, String fname) {
    TypeFld fld = TypeFld.malloc(fname,null,Access.Final,order);
    if( fid!=null ) P._dups.put(fid,fld);
    return fld.setX(P.type());
  }
  
  static { new Pool(TFLD,new TypeFld()); }
  public static TypeFld malloc( String fld, Type t, Access access, int order ) { return POOLS[TFLD].<TypeFld>malloc().init(fld,t,access,order); }
  public static TypeFld malloc( String fld ) { return POOLS[TFLD].<TypeFld>malloc().init(fld,null,Access.Final,oBot); }
  public static TypeFld make( String fld, Type t, Access access, int order ) { return malloc(fld,t,access,order).hashcons_free(); }
  public static TypeFld make( String fld, Type t, int order ) { return make(fld,t,Access.Final,order); }
  public static TypeFld make( String fld, Type t ) { return make(fld,t,Access.Final,oBot); }
  public static TypeFld make( String fld ) { return make(fld,Type.SCALAR,Access.Final,oBot); }
  public static TypeFld make_dsp(Type t) { return make("^",t,Access.Final,DSP_IDX); }
  // Make a not-interned version for building cyclic types
  public TypeFld malloc_from() { return malloc(_fld,_t,_access,_order); }

  // Some convenient default constructors
  static final String[] ARGS = new String[]{" ctl", " mem", "^","x","y","z"};
  static final String[] TUPS = new String[]{" ctl", " mem", "^","0","1","2"};
  public static TypeFld make_arg( Type t, int order ) { return make(ARGS[order],t,Access.Final,order);  }
  public static TypeFld make_tup( Type t, int order ) { return make(TUPS[order],t,Access.Final,order);  }
  public TypeFld make_from(Type t) { return t==_t ? this : make(_fld,t,_access,_order); }
  public TypeFld make_from(Type t, Access a) { return (t==_t && a==_access) ? this : make(_fld,t,a,_order); }

  public static final TypeFld NO_DSP = TypeFld.make_dsp(TypeMemPtr.NO_DISP);

  @Override protected TypeFld xdual() {
    if( Util.eq(_fld,sdual(_fld)) && _t==_t.dual() && _order==odual(_order) && _access==_access.dual() )
      return this;              // Self symmetric
    return POOLS[TFLD].<TypeFld>malloc().init(sdual(_fld),_t.dual(),_access.dual(),odual(_order));
  }
  @Override protected TypeFld rdual() {
    assert _hash!=0;
    if( _dual != null ) return _dual;
    TypeFld dual = _dual = POOLS[TFLD].<TypeFld>malloc().init(sdual(_fld),_t==null ? null : _t.rdual(),_access.dual(),odual(_order));
    dual._dual = this;
    dual._hash = dual.compute_hash();
    return dual;
  }

  @Override protected TypeFld xmeet( Type tf ) {
    if( this==tf ) return this;
    if( tf._type != TFLD ) throw typerr(tf);
    TypeFld f = (TypeFld)tf;
    String fld   = smeet(_fld,  f._fld)  ;
    Type   t     = _t     .meet(f._t     );
    Access access= _access.meet(f._access);
    int    order = omeet(_order,f._order );
    return make(fld,t,access,order);
  }

  private static TypeFld malloc( String fld, Access a, int order ) {
    TypeFld tfld = POOLS[TFLD].malloc();
    return tfld.init(fld,null,a,order);
  }


  // Used during cyclic struct meets, either side (but not both) might be null,
  // and the _t field is not filled in.  A new TypeFld is returned.
  static TypeFld cmeet(TypeFld f0, TypeFld f1) {
    if( f0==null ) return malloc(f1._fld,f1._access, f1._order);
    if( f1==null ) return malloc(f0._fld,f0._access, f0._order);
    String fld   = smeet(f0._fld,  f1._fld);
    Access access= f0._access.meet(f1._access);
    int    order = omeet(f0._order,f1._order);
    return malloc(fld,access,order);
  }
  // Used during cyclic struct meets.  The LHS is meeted into directly.
  // The _t field is not filled in.
  void cmeet(TypeFld f) {
    assert _hash==0; // Not interned, hash is changing
    _fld    = smeet(_fld,f._fld);
    _access = _access.meet(f._access);
    _order  = omeet(_order,f._order);
  }

  public enum Access {
    ReadOnly,                   // Read-Only; other threads can Write
    RW,                         // Read/Write
    Final,                      // No future load will ever see a different value than any final store
    NoAccess,                   // Cannot access (either read or write)
    HiReadWrite,
    HiFinal,
    HiNoAccess;
    public static final Access[] values = values();
    static Access bot() { return ReadOnly; }
    public Access dual() { return values[("6453120".charAt(ordinal()))-'0']; }
    private static final String[] FMEET = {
      /*    0123456 */
      /*0*/"0000000",
      /*1*/"0101111",
      /*2*/"0022222",
      /*3*/"0123333",
      /*4*/"0123434",
      /*5*/"0123355",
      /*6*/"0123456",
    };
    Access meet(Access a) { return values[FMEET[ordinal()].charAt(a.ordinal())-'0']; }
    private static final String[] SHORTS = new String[]{"==",":=","=","~=","!:=!","!=!","!~=!"};
    private static final String[] LONGS  = new String[]{"read-only","read/write","final","noaccess","!:=!","!=!","!~=!"};
    @Override public String toString() { return LONGS[ordinal()]; }
    public SB str(SB sb) { return sb.p(SHORTS[ordinal()]); }
  }

  // Field names
  public static final String fldTop = "\\";
  public static final String fldBot = "." ;
  // String dual
  private static String sdual(String s) {
    if( Util.eq(s,fldTop) ) return fldBot;
    if( Util.eq(s,fldBot) ) return fldTop;
    return s;
  }
  // String meet
  private static String smeet( String s0, String s1 ) {
    if( Util.eq(s0,s1) ) return s0;
    if( Util.eq(s0,fldTop) ) return s1;
    if( Util.eq(s1,fldTop) ) return s0;
    return fldBot;
  }

  // Field order, -1 is undefined (bot) and -2 is conforming (top)
  public static final int oTop = -1;
  public static final int oBot = -2;
  private static int odual( int order ) {
    if( order==oTop ) return oBot;
    if( order==oBot ) return oTop;
    return order;
  }
  private static int omeet( int o0, int o1 ) {
    if( o0==o1 ) return o0;
    if( o0==oTop ) return o1;
    if( o1==oTop ) return o0;
    return oBot;
  }

  public static final TypeFld NO_DISP = make("^",Type.ANY,Access.Final,DSP_IDX);

  // Setting the type during recursive construction.
  public TypeFld setX(Type t) {
    if( _t==t) return this; // No change
    _t = t;
    assert _hash==0 || _hash==compute_hash();  // Not hashed, since hash just changed
    return this;
  }
  public TypeFld setX(Type t, Access access) {
    if( _t==t && _access==access ) return this; // No change
    assert _dual==null;     // Not interned
    _t = t;
    _access = access;
    return this;
  }
  public TypeFld setX(Type t, int order) {
    if( _t==t && _order==order ) return this; // No change
    _t = t;
    _order = order;
    assert _hash==0;  // Not hashed, since hash just changed
    return this;
  }

  @Override public boolean above_center() { return _t.above_center(); }
  @Override public TypeFld simple_ptr() { return make_from(_t.simple_ptr()); }
  @SuppressWarnings("unchecked")
  @Override public void walk( Predicate<Type> p ) { if( p.test(this) ) _t.walk(p); }

  // Make a Type, replacing all dull pointers from the matching types in mem.
  @Override public TypeFld make_from(Type head, TypeMem mem, VBitSet visit) {
    return make_from(_t.make_from(head,mem,visit));
  }

  @Override TypeStruct repeats_in_cycles(TypeStruct head, VBitSet bs) { return _t.repeats_in_cycles(head,bs); }

  // Used for assertions
  @Override boolean intern_check1() { return _t.intern_lookup()!=null; }
}

