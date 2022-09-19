package com.cliffc.aa.type;

import com.cliffc.aa.util.NonBlockingHashMapLong;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.Util;
import com.cliffc.aa.util.VBitSet;
import org.jetbrains.annotations.NotNull;

import java.util.function.BinaryOperator;


// A field in a TypeStruct, with a type and a name and an Access.  Field
// accesses make a small lattice of: {choice,r/w,final,r-o}.  Note that mixing
// r/w and final moves to r-o and loses the final property.  No field order.
public class TypeFld extends Type<TypeFld> implements Cyclic {
  // Field names are never null, and never zero-length.  Names can be fldTop or fldBot.
  public String _fld;           // The field name
  public Type _t;               // Field type.  Usually some type of Scalar, or ANY or ALL.
  public Access _access;        // Field access type: read/write, final, read/only

  private TypeFld init( @NotNull String fld, Type t, Access access ) {
    assert !(t instanceof TypeFld);
    super.init();
    _fld = fld;
    _t = t;
    _access = access;
    return this;
  }
  @Override public TypeFld copy() { return _copy().init(_fld,_t,_access); }

  @Override public TypeMemPtr walk( TypeStrMap map, BinaryOperator<TypeMemPtr> reduce ) { return map.map(_t,"t"); }
  @Override public long lwalk( LongStringFunc map, LongOp reduce ) { return map.run(_t,"t"); }
  @Override public void walk( TypeStrRun map ) { map.run(_t,"t"); }
  @Override public void walk_update( TypeMap map ) { _t = map.map(_t); }
  @Override public Cyclic.Link _path_diff0(Type t, NonBlockingHashMapLong<Link> links) {
    return Cyclic._path_diff(_t,((TypeFld)t)._t,links);
  }

  // Ignore edges hash
  @Override long static_hash() { return Util.mix_hash(super.static_hash(),_fld.hashCode(),_access.hashCode()); }

  // Returns 1 for definitely equals, 0 for definitely unequals and -1 for needing the circular test.
  int cmp(TypeFld t) {
    if( this==t ) return 1;
    if( !Util.eq(_fld,t._fld) || _access!=t._access ) return 0; // Definitely not equals without recursion
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

  @Override void _str_dups( VBitSet visit, NonBlockingHashMapLong<String> dups, UCnt ucnt ) {
    if( visit.tset(_uid) ) {
      if( !dups.containsKey(_uid) )
        dups.put(_uid,"F"+(char)('A'+ucnt._fld++));
      return;
    }
    if( _t!=null ) _t._str_dups(visit,dups,ucnt);
  }

  @Override SB _str0( VBitSet visit, NonBlockingHashMapLong<String> dups, SB sb, boolean debug, boolean indent ) {
    if( !TypeStruct.isDigit(_fld.charAt(0)) || // Do not print number-named fields for tuples, unless dups are involved
        dups.get(_uid)!=null || _t==null || dups.get(_t._uid)!=null ) // DUP:_t is ambiguous with DUP:0=_t and 0=DUP:_t; so print field name
      _access.str(sb.p(_fld));                                        // Print "field="
    return _t==null ? sb.p('!') : (_t._str(visit, dups, sb, debug, indent));
  }

  // Parse "=type" and all variants of "=" in SHORTS, or return null.
  // Passed in any "DUP:" string as cid.  Passed in the field name and number.
  static TypeFld valueOf(Parse P, String cid, boolean any, String fld, int fld_num) {
    assert !any;                // Discovered via SHORTS
    assert fld_num>=0;          // Only called in a field context
    String[] eqs = Access.SHORTS;
    int i; for( i=0; i<eqs.length; i++ ) // Find assignment flavor
      if( P.peek(eqs[i]) )
        break;
    if( i==eqs.length ) return null; // Not a assignment flavor
    TypeFld tf = malloc(fld,null,Access.values[i]); // Make TypeFld without type yet
    if( cid!=null ) P._dups.put(cid,tf);            // Close cyclic types
    tf._t = P.type();                               // Fill in field type
    return tf;
  }

  static { new Pool(TFLD,new TypeFld()); }
  public static TypeFld malloc( String fld, Type t, Access access ) { return POOLS[TFLD].<TypeFld>malloc().init(fld,t,access); }
  public static TypeFld malloc( String fld ) { return POOLS[TFLD].<TypeFld>malloc().init(fld,null,Access.Final); }
  public static TypeFld make( String fld, Type t, Access access ) { return malloc(fld,t,access).hashcons_free(); }
  public static TypeFld make( String fld, Type t ) { return make(fld,t,Access.Final); }
  public static TypeFld make( String fld ) { return make(fld,TypeNil.SCALAR,Access.Final); }
  public static TypeFld make( Type def ) { return make(fldBot,def,Access.Final); }
  public static TypeFld make_dsp(Type t) { return make("^",t,Access.Final); }
  // Make a not-interned version for building cyclic types
  public TypeFld malloc_from() { return malloc(_fld,_t,_access); }

  // Some convenient default constructors
  static final String[] ARGS = new String[]{" ctl", " mem", "^","x","y","z"};
  static final String[] TUPS = new String[]{" ctl", " mem", "^","0","1","2"};
  public static TypeFld make_arg( Type t, int order ) { return make(ARGS[order],t,Access.Final);  }
  public static TypeFld make_tup( Type t, int order ) { return make(TUPS[order],t,Access.Final);  }
  public TypeFld make_from(Type t) { return t==_t ? this : make(_fld,t,_access); }
  public TypeFld make_from(Type t, Access a) { return (t==_t && a==_access) ? this : make(_fld,t,a); }
  // For some tests
  public static final TypeFld ANY_DSP = TypeFld.make_dsp(Type.ANY);
  public static final TypeFld NO_DSP  = TypeFld.make_dsp(TypeMemPtr.NO_DISP);

  @Override protected TypeFld xdual() {
    if( Util.eq(_fld,sdual(_fld)) && _t==_t.dual() && _access==_access.dual() )
      return this;              // Self symmetric
    return POOLS[TFLD].<TypeFld>malloc().init(sdual(_fld),_t.dual(),_access.dual());
  }
  @Override protected void rdual() { _dual._t = _t._dual; }

  @Override protected TypeFld xmeet( Type tf ) {
    if( this==tf ) return this;
    if( tf._type != TFLD ) throw typerr(tf);
    TypeFld f = (TypeFld)tf;
    String fld   = smeet(_fld,  f._fld)  ;
    Type   t     = _t     .meet(f._t     );
    Access access= _access.meet(f._access);
    return make(fld,t,access);
  }

  private static TypeFld malloc( String fld, Access a ) {
    TypeFld tfld = POOLS[TFLD].malloc();
    return tfld.init(fld,null,a);
  }

  // Used during cyclic struct meets, either side (but not both) might be null,
  // and the _t field is not filled in.  A new TypeFld is returned.
  static TypeFld cmeet(TypeFld f0, TypeFld f1) {
    if( f0==null ) return malloc(f1._fld,f1._access);
    if( f1==null ) return malloc(f0._fld,f0._access);
    String fld   = smeet(f0._fld,  f1._fld);
    Access access= f0._access.meet(f1._access);
    return malloc(fld,access);
  }

  public enum Access {
    RW,                         // Read/Write; other threads can change, I can change
    ReadOnly,                   // Read-Only ; other threads can change
    Final,                      // No future load will ever see a different value than any final store
    NoAccess,                   // Cannot access (either read or write)
    HiFinal,
    HiReadOnly,
    HiReadWrite;
    public static final Access[] values = values();
    static Access bot() { return RW; }
    public Access dual() { return values[6-ordinal()]; }
    Access meet(Access a) { return values[Math.min(ordinal(),a.ordinal())]; }
    private static final String[] SHORTS = new String[]{":="        ,"=="       ,"="    ,"~="      ,"!=!","!==!","!:=!"};
    private static final String[] LONGS  = new String[]{"read/write","read-only","final","noaccess","!=!","!==!","!:=!"};
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
  public static String smeet( String s0, String s1 ) {
    if( Util.eq(s0,s1) ) return s0;
    if( Util.eq(s0,fldTop) ) return s1;
    if( Util.eq(s1,fldTop) ) return s0;
    return fldBot;
  }
  // True if fld0 < fld1
  static boolean sbefore(TypeFld fld0, TypeFld fld1) {
    if( fld0==null ) return false;
    if( fld1==null ) return true ;
    if( Util.eq(fld0._fld,fldTop) ) return true;
    if( Util.eq(fld0._fld,fldBot) ) return true;
    if( Util.eq(fld1._fld,fldTop) ) return false;
    if( Util.eq(fld1._fld,fldBot) ) return false;
    return fld0._fld.compareTo(fld1._fld)<0;
  }

  public static final TypeFld NO_DISP = make("^",Type.ANY,Access.Final);

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

  @Override public boolean above_center() { return _t.above_center(); }
  @Override public boolean is_con() { return _t.is_con(); }
  @Override public TypeFld simple_ptr() { return make_from(_t.simple_ptr()); }

  // Make a Type, replacing all dull pointers from the matching types in mem.
  @Override public TypeFld make_from(Type head, TypeMem mem, VBitSet visit) {
    return make_from(_t.make_from(head,mem,visit));
  }

  // Used for assertions
  @Override boolean intern_check1() { return _t.intern_get()!=null; }
}

