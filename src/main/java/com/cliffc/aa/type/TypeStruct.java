package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.*;
import org.jetbrains.annotations.NotNull;

import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.function.Predicate;

/** A memory-based collection of optionally named fields.  This is a recursive
 *  type, only produced by NewNode and structure or tuple constants.  Fields
 *  can be indexed by field name or numeric constant (i.e. tuples), but NOT by
 *  a general number - thats an Array.  Field access mods make a small lattice
 *  of: {choice,r/w,final,r-o}.  Note that mixing r/w and final moves to r-o and
 *  loses the final property.  Fields can be individually alive or clean (not
 *  modified in this function).
 *
 *  The recursive type poses some interesting challenges.  It is represented as
 *  literally a cycle of pointers which must include a TypeStruct (and not a
 *  TypeTuple which only roots Types) and a TypeMemPtr (edge).  Type inference
 *  involves finding the Meet of two cyclic structures.  The cycles will not
 *  generally be of the same length.  However, each field Meets independently
 *  (and fields in one structure but not the other are not in the final Meet).
 *  This means we are NOT trying to solve the general problem of graph-
 *  equivalence (a known NP hard problem).  Instead we can solve each field
 *  independently and also intersect across common fields.
 *
 *  When solving across a single field, we will find some prefix and then
 *  possibly a cycle - conceptually the type unrolls forever.  When doing the
 *  Meet we conceptually unroll both types forever, compute the Meet element by
 *  element... but when both types have looped, we can stop and the discovered
 *  cycle is the Meet's cycle.
 */
public class TypeStruct extends TypeObj<TypeStruct> {
  // Fields are named in-order and aligned with the Tuple values.  Field names
  // are never null, and never zero-length.  If the 1st char is a '*' the field
  // is Top; a '.' is Bot; all other values are valid field names.
  public @NotNull String @NotNull[] _flds;  // The field names
  public Type[] _ts;                        // Matching field types
  private byte[] _flags; // Field mod types; see fmeet, fdual, fstr.  Clean.

  boolean _cyclic; // Type is cyclic.  This is a summary property, not a description of value sets, hence is not in the equals or hash
  private TypeStruct _uf;       // Tarjan Union-Find, used during cyclic meet
  private TypeStruct     ( String name, boolean any, String[] flds, Type[] ts, byte[] flags) { super(TSTRUCT, name, any); init(name, any, flds,ts,flags); }
  private TypeStruct init( String name, boolean any, String[] flds, Type[] ts, byte[] flags) {
    super.init(TSTRUCT, name, any);
    _flds  = flds;
    _ts    = ts;
    _flags= flags;
    _uf    = null;
    return this;
  }
  // Precomputed hash code.  Note that it can NOT depend on the field types -
  // because during recursive construction the types are not available.
  @Override int compute_hash() {
    int hash = super.compute_hash(), hash1=hash;
    for( int i=0; i<_flds.length; i++ ) hash = ((hash+(_flags[i]<<5))*_flds[i].hashCode())|(hash>>>17);
    return hash == 0 ? hash1 : hash;
  }

  private static final Ary<TypeStruct> CYCLES = new Ary<>(new TypeStruct[0]);
  private TypeStruct find_other() {
    int idx = CYCLES.find(this);
    return idx != -1 ? CYCLES.at(idx^1) : null;
  }

  // Returns 1 for definitely equals, 0 for definitely unequals, and -1 if
  // needing the cyclic test.
  private int cmp( TypeStruct t ) {
    if( !super.equals(t) ) return 0;
    if( _ts.length != t._ts.length ) return 0;
    if( _ts == t._ts && _flds == t._flds && _flags == t._flags ) return 1;
    for( int i=0; i<_ts.length; i++ )
      if( !Util.eq(_flds[i],t._flds[i]) || _flags[i]!=t._flags[i] )
        return 0;
    for( int i=0; i<_ts.length; i++ )
      if( _ts[i]!=t._ts[i] )
        return -1;              // Some not-pointer-equals child types, must do the full check
    return 1;                   // All child types are pointer-equals, so must be equals.
  }

  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeStruct) ) return false;
    TypeStruct t = (TypeStruct)o;
    // While we would like to use the notion of interned Type[] during the
    // normal Type.INTERN check, we also get here during building of cyclic
    // structures for which we'll fall into the cyclic check - as the Type[]s
    // are not interned yet.
    int x = cmp(t);
    if( x != -1 ) return x == 1;
    // Unlike all other non-cyclic structures which are built bottom-up, cyclic
    // types have to be built all-at-once, and thus hash-cons and equality-
    // tested with a cyclic-aware equals check.
    return cycle_equals(t);
  }
  @Override public boolean cycle_equals( Type o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeStruct) ) return false;
    TypeStruct t = (TypeStruct)o;
    TypeStruct t2 = find_other();
    if( t2 !=null ) return t2==t   ; // Already in cycle report equals or not
    TypeStruct t3 = t.find_other();
    if( t3 !=null ) return t3==this;// Already in cycle report equals or not
    int x = cmp(t);
    if( x != -1 ) return x == 1;

    int len = CYCLES._len;
    CYCLES.add(this).add(t);
    boolean eq=cycle_equals0(t);
    assert CYCLES._len==len+2;
    CYCLES._len=len;
    return eq;
  }
  private boolean cycle_equals0( TypeStruct t ) {
    for( int i=0; i<_ts.length; i++ )
      if( _ts[i]!=t._ts[i] &&   // Normally suffices to test ptr-equals only
          (_ts[i]==null || t._ts[i]==null || // Happens when asserting on partially-built cyclic types
           !_ts[i].cycle_equals(t._ts[i])) ) // Must do a full cycle-check
        return false;
    return true;
  }

  // Test if this is a cyclic value (and should not be interned) with internal
  // repeats.  i.e., not a minimal cycle.
  TypeStruct repeats_in_cycles() {
    assert _cyclic;
    assert _uf == null;         // Not collapsing
    return repeats_in_cycles(this,new VBitSet());
  }
  @Override TypeStruct repeats_in_cycles(TypeStruct head, VBitSet bs) {
    if( bs.tset(_uid) ) return null;
    assert _uf == null;         // Not collapsing
    if( this!=head && equals(head) ) return this;
    for( Type t : _ts ) {
      TypeStruct ts = t.repeats_in_cycles(head,bs);
      if( ts!=null ) return ts;
    }
    return null;
  }

  private static boolean isDigit(char c) { return '0' <= c && c <= '9'; }
  private boolean is_tup() { return _flds.length<=1 || fldTop(_flds[1]) || fldBot(_flds[1]) || isDigit(_flds[1].charAt(0)); }
  String str( VBitSet dups) {
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return "$"; // Break recursive printing cycle
    // Special shortcut for the all-prims display type
    if( find("!") != -1 && find("math_pi") != -1 && _ts[1] instanceof TypeFunPtr )
      return ((TypeFunPtr)_ts[1])._fidxs.above_center()
        ? "{PRIMS}" : "{LOW_PRIMS}";

    SB sb = new SB();
    if( _uf!=null ) return "=>"+_uf; // Only used mid-recursion
    if( _any ) sb.p('~');
    sb.p(_name);
    boolean is_tup = is_tup();
    sb.p(is_tup ? "(" : "@{");
    for( int i=0; i<_flds.length; i++ ) {
      if( dirty(_flags[i]) ) sb.p("!"); // Dirty field
      if( !is_tup )
        sb.p(_flds[i]).p(fstr(fmod(i))).p('='); // Field name, access mod
      Type t = at(i);
      if( t==null ) sb.p("!");  // Graceful with broken types
      else if( t==SCALAR ) ;    // Default answer, do not print
      else sb.p(t.str(dups));   // Recursively print field type
      if( i<_flds.length-1 ) sb.p(';');
    }
    sb.p(!is_tup ? "}" : ")");
    return sb.toString();
  }
  @Override SB dstr( SB sb, VBitSet dups ) {
    sb.p('_').p(_uid);
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return sb.p('$'); // Break recursive printing cycle
    // Special shortcut for the all-prims display type
    if( find("!") != -1 && find("math_pi") != -1 && _ts[1] instanceof TypeFunPtr )
      return sb.p(((TypeFunPtr)_ts[1])._fidxs.above_center()
                  ? "{PRIMS}" : "{LOW_PRIMS}");

    if( _uf!=null ) return _uf.dstr(sb.p("=>"),dups);
    if( _any ) sb.p('~');
    sb.p(_name);
    boolean is_tup = is_tup();
    if( !is_tup ) sb.p('@');    // Not a tuple
    sb.p(is_tup ? '(' : '{').nl().ii(1); // open struct, newline, increase_indent
    for( int i=0; i<_flds.length; i++ ) {
      sb.i();                   // indent, 1 field per line
      if( dirty(_flags[i]) ) sb.p("!"); // Dirty field
      Type t = at(i);
      if( !is_tup )
        sb.p(_flds[i]).p(fstr(fmod(i))).p('='); // Field name, access mod
      if( t==null ) sb.p("!");  // Graceful with broken types
      else if( t==SCALAR ) ;    // Default answer, do not print
      else t.dstr(sb,dups);     // Recursively print field type
      if( i<_flds.length-1 ) sb.p(';');
      sb.nl();                  // one field per line
    }
    return sb.di(1).i().p(!is_tup ? '}' : ')');
  }
  // Print with memory instead of recursion
  @Override public SB str(SB sb, VBitSet dups, TypeMem mem) {
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return sb.p('$'); // Break recursive printing cycle
    // Special shortcut for the all-prims display type
    if( find("!") != -1 && find("math_pi") != -1 && _ts[1] instanceof TypeFunPtr )
      return sb.p(((TypeFunPtr)_ts[1])._args._ts[0].above_center()
                  ? "{PRIMS}" : "{LOW_PRIMS}");
    if( _uf!=null ) return _uf.str(sb.p("=>"),dups,mem);
    if( _any ) sb.p('~');
    sb.p(_name);
    boolean is_tup = is_tup();
    if( !is_tup ) sb.p('@');    // Not a tuple
    sb.p(is_tup ? '(' : '{');
    for( int i=0; i<_flds.length; i++ ) {
      if( Util.eq(_flds[i],"^") ) continue; // Do not print the ever-present display
      if( dirty(_flags[i]) ) sb.p("!"); // Dirty field
      Type t = at(i);
      if( !is_tup )
        sb.p(_flds[i]).p(fstr(fmod(i))).p('='); // Field name, access mod
      if( t==null ) sb.p("!");  // Graceful with broken types
      else if( t==SCALAR ) ;    // Default answer, do not print
      else t.str(sb,dups,mem);  // Recursively print field type
      if( i<_flds.length-1 ) sb.p(';');
    }
    return sb.p(!is_tup ? '}' : ')');
  }

  // Unlike other types, TypeStruct never makes dups - instead it might make
  // cyclic types for which a DAG-like bottom-up-remove-dups approach cannot work.
  private static TypeStruct FREE=null;
  @Override protected TypeStruct free( TypeStruct ret ) { FREE=this; return ret; }
  static TypeStruct malloc( String name, boolean any, String[] flds, Type[] ts, byte[] flags ) {
    assert check_name(name);
    if( FREE == null ) return new TypeStruct(name, any,flds,ts,flags);
    TypeStruct t1 = FREE;  FREE = null;
    return t1.init(name, any,flds,ts,flags);
  }
  private TypeStruct hashcons_free() {
    _ts = TypeAry.hash_cons(_ts);
    TypeStruct t2 = (TypeStruct)hashcons();
    return this==t2 ? this : free(t2);
  }

  // Default tuple field names - all bottom-field names
  static String[] flds(String... fs) { return fs; }
  public  static final String[] ARGS_X  = flds("->","^","x"); // Used for functions of 1 arg
  public  static final String[] ARGS_XY = flds("->","^","x","y"); // Used for functions of 2 args
  public  static Type[] ts() { return TypeAry.get(0); }
  public  static Type[] ts(Type t0) { Type[] ts = TypeAry.get(1); ts[0]=t0; return ts;}
  public  static Type[] ts(Type t0, Type t1) { Type[] ts = TypeAry.get(2); ts[0]=t0; ts[1]=t1; return ts;}
  public  static Type[] ts(Type t0, Type t1, Type t2) { Type[] ts = TypeAry.get(3); ts[0]=t0; ts[1]=t1; ts[2]=t2; return ts;}
  public  static Type[] ts(Type t0, Type t1, Type t2, Type t3) { Type[] ts = TypeAry.get(4); ts[0]=t0; ts[1]=t1; ts[2]=t2; ts[3]=t3; return ts;}
  public  static Type[] ts(int n) { Type[] ts = TypeAry.get(n); Arrays.fill(ts,SCALAR); return ts; } // All Scalar fields

  // Field modifiers make a tiny non-obvious lattice:
  //           0unknown          -- dual==3
  //      1final     2read/write -- dual==unchanged
  //          3read-only         -- dual==0
  // Shows as:  fld?=val, fld==val, fld:=val, fld=val
  private static String fstr( byte f ) { return new String[]{"?","=",":",""}[f]; }
  public  static String fstring( byte f ) { return new String[]{"unknown","final","read-write","read-only"}[f]; }

  public static final byte FUNK = 0; // top
  public static final byte FFNL = 1; // centerline
  public static final byte FRW  = 2; // centerline
  public static final byte FRO  = 3; // bottom

  // Some precooked flags
          static final byte fbot_flag = make_flag(FRO ,false); // Field bottom
          static final byte  fnl_flag = make_flag(FFNL,false); // Field final
  private static final byte  frw_flag = make_flag(FRW ,true); // Field final

  // Field bottom, plus dirty flags
  public  static byte[] fbots(int n) { byte[] bs = new byte[n]; Arrays.fill(bs,fbot_flag); return bs; }
  // Field final, plus dirty flags
  public  static byte[] ffnls(int n) { byte[] bs = new byte[n]; Arrays.fill(bs, fnl_flag); return bs; }
  // Field r/w, plus dirty flags
  public  static byte[] frws (int n) { byte[] bs = new byte[n]; Arrays.fill(bs, frw_flag); return bs; }

  public  static TypeStruct make(Type[] ts) {
    String[] flds = new String[ts.length];
    Arrays.fill(flds,fldBot());
    return malloc("",false,flds,ts,fbots(ts.length)).hashcons_free();
  }
  // Generic function arguments.  Slot 0 is the return, and slot 1 is the
  // display and both fixed names.
  public static TypeStruct make_args(Type[] ts) { return make_x_args(false,ts); }
  public static TypeStruct make_x_args(boolean any, Type[] ts) {
    String[] args = new String[ts.length];
    Arrays.fill(args,any ? fldTop() : fldBot());
    args[0] = "->";
    args[1] = "^";
    return make_args(any,args,ts);
  }
  public static TypeStruct make_args(String[] flds, Type[] ts) { return make_args(false,flds,ts); }
  // First two fields are the return and the display
  public static TypeStruct make_args(boolean any, String[] flds, Type[] ts) {
    assert Util.eq(flds[0],"->");
    assert Util.eq(flds[1],"^");
    assert ts[1].is_display_ptr();
    byte[] fs = fbots(ts.length);  fs[0] = FFNL;
    return malloc("",any,flds,ts,fs).hashcons_free();
  }
  public  static TypeStruct make(String[] flds, Type[] ts) { return malloc("",false,flds,ts,fbots(ts.length)).hashcons_free(); }
  public  static TypeStruct make(String[] flds, Type[] ts, byte[] flags) { return malloc("",false,flds,ts,flags).hashcons_free(); }
  public  static TypeStruct make(String name, String[] flds, Type[] ts, byte[] flags) { return malloc(name,false,flds,ts,flags).hashcons_free(); }
  public  static TypeStruct make(boolean any, String[] flds, Type[] ts, byte[] flags) { return malloc("",any,flds,ts,flags).hashcons_free(); }

  // Generic parser struct object, slot 0 is the display and is NO_DISP post-parse.
  private static final String[][] TFLDS={{},
                                         {"^"},
                                         {"^","0"},
                                         {"^","0","1"},
                                         {"^","0","1","2"}};
  public  static TypeStruct make_tuple( Type... ts ) { return make(TFLDS[ts.length],ts,ffnls(ts.length)); }
  public static TypeStruct make_tuple(Type t1) { return make_tuple(ts(NO_DISP,t1)); }

  public  static TypeStruct make(String[] flds, byte[] flags) { return make(flds,ts(flds.length),flags); }
  // Make from prior, just updating field types
  public TypeStruct make_from( Type[] ts ) { return make_from(_any,ts,_flags); }
  public TypeStruct make_from( boolean any, Type[] ts, byte[] bs ) { return malloc(_name,any,_flds,ts,bs).hashcons_free(); }
  // Make a call TFP with the empty set of fidxs
  public TypeStruct make_from_empty( ) {
    Type[] ets = ts(_ts.length);
    Arrays.fill(ets,Type.NIL); // Has to be all NIL args to preserve monotonicity
    ets[0] = Type.XNIL;        // Function return type
    ets[1] = TypeStruct.NO_DISP; // Display type
    return make_from(true,ets,ffnls(_ts.length));
  }
  

  // Recursive meet in progress.
  // Called during class-init.
  private static class TPair {
    TypeStruct _ts0, _ts1;
    private static TPair KEY = new TPair(null,null);
    static TPair set(TypeStruct ts0, TypeStruct ts1) {KEY._ts0=ts0; KEY._ts1=ts1; return KEY; }
    TPair(TypeStruct ts0, TypeStruct ts1) { _ts0=ts0; _ts1=ts1; }
    @Override public int hashCode() { return (_ts0.hashCode()<<17) | _ts1.hashCode(); }
    @Override public boolean equals(Object o) {
      return _ts0.equals(((TPair)o)._ts0) && _ts1.equals(((TPair)o)._ts1);
    }
  }
  private static final HashMap<TPair,TypeStruct> MEETS0 = new HashMap<>();

  // The display is a self-recursive structure: slot 0 is a ptr to a Display.
  // To break class-init cycle, this is partially made here, now.
  // Then we touch TypeMemPtr, which uses this field.
  // Then we finish making DISPLAY.
  public static final TypeStruct DISPLAY = malloc("",false,new String[]{"^"},ts(NIL),ffnls(1));
  public static final TypeStruct DISPLAY0= malloc("",false,new String[]{"^"},ts(NIL),ffnls(1));
  static {
    DISPLAY ._hash = DISPLAY .compute_hash();
    DISPLAY0._hash = DISPLAY0.compute_hash();
    ALLSTRUCT = malloc("",false,new String[0],TypeAry.get(0),fbots(0)).hashcons_free();
    Type dummy = TypeMemPtr.STRPTR; // Force TypeMemPtr
    assert DISPLAY ._ts[0] == Type.NIL;
    assert DISPLAY0._ts[0] == Type.NIL;
    DISPLAY ._ts = ts(TypeMemPtr.DISPLAY_PTR);
    DISPLAY0._ts = ts(TypeMemPtr.NIL_DISPLAY);
    DISPLAY .install_cyclic(new Ary<>(ts(DISPLAY ,TypeMemPtr.DISPLAY_PTR)));
    DISPLAY0.install_cyclic(new Ary<>(ts(DISPLAY0,TypeMemPtr.NIL_DISPLAY)));
    assert DISPLAY .is_display();
    assert DISPLAY0.is_display();
  }
  @Override boolean is_display() {
    return
      this==DISPLAY || this==DISPLAY._dual ||
      this==DISPLAY0 || this==DISPLAY0._dual ||
      // Functions have their display in _ts[1] (_ts[0] reserved for the return
      // value) but displays have the linked-list pointer in _ts[0].
      (_ts.length >= 1 && _ts[0].is_display_ptr());
  }
  public static final Type NO_DISP= TypeMemPtr.NIL_DISPLAY;

  public  static final TypeStruct GENERIC = malloc("",true,new String[0],TypeAry.get(0),new byte[0]).hashcons_free();
  public  static final TypeStruct ALLSTRUCT;
  public  static final TypeStruct INT64__INT64= make_args(ARGS_X ,ts(TypeInt.INT64,NO_DISP,TypeInt.INT64)); // {int->int}
  public  static final TypeStruct INT64__FLT64= make_args(ARGS_X ,ts(TypeFlt.FLT64,NO_DISP,TypeInt.INT64)); // {int->flt}
  public  static final TypeStruct FLT64__FLT64= make_args(ARGS_X ,ts(TypeFlt.FLT64,NO_DISP,TypeFlt.FLT64)); // {flt->flt}
  public  static final TypeStruct STRPTR__STRPTR    = make_args(ARGS_X ,ts(TypeMemPtr.STRPTR,NO_DISP,TypeMemPtr.STRPTR));
  public  static final TypeStruct STRPTR__SCALAR    = make_args(ARGS_X ,ts(Type.SCALAR,NO_DISP,TypeMemPtr.STRPTR));
  public  static final TypeStruct INT64_INT64__INT64= make_args(ARGS_XY,ts(TypeInt.INT64,NO_DISP,TypeInt.INT64,TypeInt.INT64)); // {int int->int }
  public  static final TypeStruct INT64_INT64__BOOL = make_args(ARGS_XY,ts(TypeInt.BOOL ,NO_DISP,TypeInt.INT64,TypeInt.INT64)); // {int int->bool}
  public  static final TypeStruct FLT64_FLT64__FLT64= make_args(ARGS_XY,ts(TypeFlt.FLT64,NO_DISP,TypeFlt.FLT64,TypeFlt.FLT64)); // {flt flt->flt }
  public  static final TypeStruct FLT64_FLT64__BOOL = make_args(ARGS_XY,ts(TypeInt.BOOL ,NO_DISP,TypeFlt.FLT64,TypeFlt.FLT64)); // {flt flt->bool}
  public  static final TypeStruct OOP_OOP__BOOL     = make_args(ARGS_XY,ts(TypeInt.BOOL,NO_DISP,TypeMemPtr.OOP0,TypeMemPtr.OOP0));
  public  static final TypeStruct SCALAR1__BOOL     = make_args(ARGS_X ,ts(TypeInt.BOOL,NO_DISP,SCALAR));

  // A bunch of types for tests
  public static final Type NO_DISP2 = TypeMemPtr.NIL_DISPLAY;  // NIL display for *structs* not *function args*
  public  static final TypeStruct NAMEPT= make("Point:",flds("^","x","y"),ts(NO_DISP2,TypeFlt.FLT64,TypeFlt.FLT64),ffnls(3));
  public  static final TypeStruct POINT = make(flds("^","x","y"),ts(NO_DISP2,TypeFlt.FLT64,TypeFlt.FLT64));
  public  static final TypeStruct FLT64 = make(flds("^","x"),ts(NO_DISP2,TypeFlt.FLT64)); // @{x:flt}
          static final TypeStruct TFLT64= make(flds("^","."),ts(NO_DISP2,TypeFlt.FLT64 )); //  (  flt)
  public  static final TypeStruct A     = make(flds("^","a"),ts(NO_DISP2,TypeFlt.FLT64 ));
  private static final TypeStruct C0    = make(flds("^","c"),ts(NO_DISP2,TypeInt.FALSE )); // @{c:0}
  private static final TypeStruct D1    = make(flds("^","d"),ts(NO_DISP2,TypeInt.TRUE  )); // @{d:1}
  private static final TypeStruct ARW   = make(flds("^","a"),ts(NO_DISP2,TypeFlt.FLT64),new byte[]{FRW,FRW});

  static final TypeStruct[] TYPES = new TypeStruct[]{ALLSTRUCT,STRPTR__STRPTR,FLT64,POINT,NAMEPT,A,C0,D1,ARW,DISPLAY,INT64_INT64__INT64,GENERIC};

  // Extend the current struct with a new named field
  public TypeStruct add_fld( String name, byte mutable ) { return add_fld(name,mutable,Type.SCALAR); }
  public TypeStruct add_fld( String name, byte mutable, Type tfld ) {
    assert name==null || fldBot(name) || find(name)==-1;

    Type  []   ts = TypeAry.copyOf(_ts   ,_ts   .length+1);
    String[] flds = Arrays .copyOf(_flds ,_flds .length+1);
    byte[]  flags = Arrays .copyOf(_flags,_flags.length+1);
    ts   [_ts.length] = tfld;
    flds [_ts.length] = name==null ? fldBot() : name;
    flags[_ts.length] = make_flag(mutable,true);
    return make(flds,ts,flags);
  }
  public TypeStruct set_fld( int idx, Type t, byte ff ) {
    Type[] ts  = _ts;
    byte[] ffs = _flags;
    if( ts  [idx] != t  ) ( ts = TypeAry.clone(_ts))[idx] = t;
    if( fmod(idx) != ff ) (ffs = _flags .clone(   ))[idx] = set_fmod(_flags[idx],ff);
    return make(_flds,ts,ffs);
  }
  public TypeStruct del_fld( int idx ) {
    Type[] ts = TypeAry.get(_ts.length-1);
    for( int i=0; i<idx; i++ ) ts[i] = _ts[i];
    for( int i=idx; i<ts.length; i++ ) ts[i] = _ts[i+1];
    String[] flds = new String[_flds.length-1];
    for( int i=0; i<idx; i++ ) flds[i] = _flds[i];
    for( int i=idx; i<flds.length; i++ ) flds[i] = _flds[i+1];
    byte[] flags = new byte[_flags.length-1];
    for( int i=0; i<idx; i++ ) flags[i] = _flags[i];
    for( int i=idx; i<flags.length; i++ ) flags[i] = _flags[i+1];
    return make(flds,ts,flags);
  }

  //
  public TypeFunPtr make_recursive(BitsFun fidxs, TypeStruct fun_args, String fun_name) {
    throw com.cliffc.aa.AA.unimpl();
  }


  // Make a type-variable with no definition - it is assumed to be a
  // forward-reference, to be resolved before the end of parsing.
  public static Type make_forward_def_type(String tok) {
    return make((tok+":").intern(),flds("$fref"),ts(SCALAR),fbots(1));
  }
  // We have a cycle because we are unioning {t,this} and we have a graph from
  // t->...->this.  This cycle may pre-exist once closed and can be detected
  // doing a lookup after setting this===t.  The new cycle members are in the
  // INTERN table, but if a prior cycle version exists, we need to remove the
  // new cycle and use the prior one.
  public TypeStruct merge_recursive_type( TypeStruct ts ) {
    assert has_name() && Util.eq(_flds[0],"$fref");
    // Remove from INTERN table, since hacking type will not match hash
    untern()._dual.untern();
    ts.untern().dual().untern();
    // Hack type and it's dual.  Type is now recursive.
    _flds  = ts._flds ; _dual._flds = ts._dual._flds ;
    _ts    = ts._ts   ; _dual._ts   = ts._dual._ts   ;
    _flags = ts._flags; _dual._flags= ts._dual._flags;
    _cyclic= _dual._cyclic = true;
    // Hash changes, e.g. field names.
    _hash = compute_hash();  _dual._hash = _dual.compute_hash();

    // Remove the entire new cycle members and recompute their hashes.
    rehash_cyclic(new Ary<>(Type.class), this);

    // Check for a prior.  This can ONLY happen during testing, because the
    // same type name (different lexical scopes; name mangling) cannot be used
    // twice.
    TypeStruct old = (TypeStruct)intern_lookup();
    if( old != null ) { free(null);  _dual.free(null);  return old; }

    // Insert all members of the cycle into the hashcons.  If self-symmetric,
    // also replace entire cycle with self at each point.
    if( equals(_dual) ) throw AA.unimpl();
    walk( t -> { if( t.interned() ) return false;
        t.retern()._dual.retern(); return true; });

    return this;
  }
  // Classic cycle-finding algorithm.
  private void rehash_cyclic(Ary<Type> stack, Type t ) {
    if( stack._len > 0 && t==this ) {    // If visiting again... have found a cycle t->....->this
      // All on the stack are flagged as being part of a cycle
      Type st;
      for( int i=stack._len-1; (st=stack.at(i))!=t; i-- ) {
        st.untern()._dual.untern(); // Wrong hash
        if( st._type==TMEMPTR ) ((TypeMemPtr)st)._cyclic = ((TypeMemPtr)st)._dual._cyclic = true;
        else if( st._type==TFUNPTR ) ((TypeFunPtr)st)._cyclic = ((TypeFunPtr)st)._dual._cyclic = true;
        else ((TypeStruct)st)._cyclic = ((TypeStruct)st)._dual._cyclic = true;
        st._hash = st._dual._hash = 0; // Clear.  Cannot compute until all children found/cycles walked.
      }
    } else {
      if( t instanceof TypeMemPtr || t instanceof TypeFunPtr || t instanceof TypeStruct ) {
        stack.push(t);              // Push on stack, in case a cycle is found
        if( t instanceof TypeMemPtr ) {
          rehash_cyclic(stack,((TypeMemPtr)t)._obj);
          assert ((TypeMemPtr)t)._cyclic;
        } else if( t instanceof TypeFunPtr ) {
          rehash_cyclic(stack,((TypeFunPtr)t)._args);
          assert ((TypeFunPtr)t)._cyclic;
        } else {
          for( int i=1; i<((TypeStruct)t)._ts.length; i++ )
            rehash_cyclic(stack, ((TypeStruct)t)._ts[i]);
          assert ((TypeStruct)t)._cyclic;
        }
        if( t._hash==0 ) {    // If part of a cycle, hash was cleared.  Rehash.
          t      ._hash=t      .compute_hash();
          t._dual._hash=t._dual.compute_hash();
        } else                  // Some other part, not part of cycle
          assert t._hash==t.compute_hash();
        stack.pop();            // Pop, not part of anothers cycle
      } else {
        assert t._hash != 0;    // Not part of any cycle, unchanged
      }
    }
  }

  // Dual the flds, dual the tuple.
  @Override protected TypeStruct xdual() {
    String[] as = new String[_flds.length];
    Type  [] ts = TypeAry.get(_ts  .length);
    byte  [] bs = new byte  [_ts  .length];
    for( int i=0; i<as.length; i++ ) as[i] = sdual(_flds  [i]);
    for( int i=0; i<ts.length; i++ ) ts[i] = _ts[i].dual();
    for( int i=0; i<bs.length; i++ ) bs[i] = fdual(_flags[i]);
    ts = TypeAry.hash_cons(ts);
    return new TypeStruct(_name,!_any,as,ts,bs);
  }

  // Recursive dual
  @Override TypeStruct rdual() {
    if( _dual != null ) return _dual;
    String[] as = new String[_flds.length];
    Type  [] ts = TypeAry.get(_ts.length);
    byte  [] bs = new byte  [_ts  .length];
    for( int i=0; i<as.length; i++ ) as[i]=sdual(_flds[i]);
    for( int i=0; i<bs.length; i++ ) bs[i]=fdual(_flags[i]);
    TypeStruct dual = _dual = new TypeStruct(_name,!_any,as,ts,bs);
    if( _hash != 0 ) {
      assert _hash == compute_hash();
      dual._hash = dual.compute_hash(); // Compute hash before recursion
    }
    for( int i=0; i<ts.length; i++ ) ts[i] = _ts[i].rdual();
    dual._ts = TypeAry.hash_cons(ts); // hashcons cyclic arrays
    dual._dual = this;
    dual._cyclic = _cyclic;
    return dual;
  }

  // Standard Meet.  Types-meet-Types and fld-meet-fld.  Fld strings can be
  // top/bottom for tuples.  Structs with fewer fields are virtually extended
  // with either top or bottom accordingly, to Meet against the other side.
  // Field names only restrict matches and do not affect the algorithm complexity.
  //
  // Types can be in cycles: See Large Comment Above.  We effectively unroll
  // each type infinitely until both sides are cycling and take the GCD of
  // cycles.  Different fields are Meet independently and unroll independently.
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TSTRUCT:break;
    case TSTR:   return OBJ;
    case TOBJ:   return t.above_center() ? this : t;
    case TFLT:
    case TINT:
    case TTUPLE :
    case TFUNPTR:
    case TMEMPTR:
    case TRPC:
    case TMEM:   return ALL;
    default: throw typerr(t);   // All else should not happen
    }
    TypeStruct thsi = this;
    TypeStruct that = (TypeStruct)t;
    // INVARIANT: Both this and that are prior existing & interned.
    assert RECURSIVE_MEET > 0 || (thsi.interned() && that.interned());
    // INVARIANT: Both MEETS are empty at the start.  Nothing involved in a
    // potential cycle is interned until the Meet completes.
    assert RECURSIVE_MEET > 0 || (MEETS0.isEmpty());

    // If both are cyclic, we have to do the complicated cyclic-aware meet
    if( _cyclic && that._cyclic )
      return cyclic_meet(that);
    // Recursive but not cyclic; since at least one of these types is
    // non-cyclic normal recursion will bottom-out.

    // If unequal length; then if short is low it "wins" (result is short) else
    // short is high and it "loses" (result is long).
    return thsi._ts.length <= that._ts.length ? thsi.xmeet1(that) : that.xmeet1(thsi);
  }

  // Meet 2 structs, shorter is 'this'.
  private TypeStruct xmeet1( TypeStruct tmax ) {
    int len = _any ? tmax._ts.length : _ts.length;
    // Meet of common elements
    String[] as = new String[len];
    Type  [] ts = TypeAry.get(len);
    byte  [] bs = new byte  [len];
    for( int i=0; i<_ts.length; i++ ) {
      as[i] = smeet(_flds  [i],     tmax._flds  [i]);
      ts[i] =       _ts    [i].meet(tmax._ts    [i]); // Recursive not cyclic
      bs[i] = fmeet(_flags[i],      tmax._flags[i]);
    }
    // Elements only in the longer tuple; the short struct must be high and so
    // is effectively infinitely extended with high fields.
    for( int i=_ts.length; i<len; i++ ) {
      as[i] = tmax._flds [i];
      ts[i] = tmax._ts   [i];
      bs[i] = tmax._flags[i];
    }
    // Ignore name in the non-recursive meet, it will be computed by the outer
    // 'meet' call anyways.
    return malloc("",_any&tmax._any,as,ts,bs).hashcons_free();
  }

  // Both structures are cyclic.  The meet will be "as if" both structures are
  // infinitely unrolled, Meeted, and then re-rolled.  If cycles are of uneven
  // length, the end result will be the cyclic GCD length.
  private TypeStruct cyclic_meet( TypeStruct that ) {
    // Walk 'this' and 'that' and map them both (via MEETS0) to a shared common
    // Meet result.  Only walk the cyclic parts... cyclically.  When visiting a
    // finite-sized part we use the normal recursive Meet.  When doing the
    // cyclic part, we use the normal Meet except we need to use the mapped
    // Meet types.  As part of these Meet operations we can end up Meeting Meet
    // types with each other more than once, or more than once from each side -
    // which means already visited Types might need to Meet again, even as they
    // are embedded in other Types - which leads to the need to use Tarjan U-F
    // to union Types on the fly.

    // See if we have worked on this unique pair before.  If so, the cycle has
    // been closed and just return that prior (unfinished) result.
    TypeStruct mt = MEETS0.get(TPair.set(this,that));
    if( mt != null ) return mt; // Cycle has been closed
    mt = this.shallow_clone();
    TypeStruct mx = that;
    MEETS0.put(new TPair(this,that),mt);

    // Do a shallow MEET: meet of field names and _any and _ts sizes - all
    // things that can be computed without the cycle.  _ts not filled in yet.
    int len = mt.len(mx); // Length depends on all the Structs Meet'ing here
    if( len != mt._ts.length ) {
      mt._flds = Arrays.copyOf(mt._flds , len);
      mt._ts   = Arrays.copyOf(mt._ts   , len);// escaped a _ts
      mt._flags= Arrays.copyOf(mt._flags, len);
    }
    if( mt._any && !mx._any ) mt._any=false;
    for( int i=0; i<len; i++ ) {
      String s0 = mt._flds[i];
      String s1 = i<mx._flds.length ? mx._flds[i] : null;
      mt._flds  [i] = smeet(s0,s1); // Set the Meet of field names
      byte b0 = mt._flags[i];
      byte b1 = i<mx._flags.length ? mx._flags[i] : flag_top();
      mt._flags[i] = fmeet(b0,b1); // Set the Meet of field access
    }
    mt._name = mt.mtname(mx,mt);
    mt._hash = mt.compute_hash(); // Compute hash now that fields and flags are set

    // Since the result is cyclic, we cannot test the cyclic parts for
    // pre-existence until the entire cycle is built.  We can't intern the
    // partially built parts, but we want to use the normal xmeet call - which
    // normally recursively interns.  Turn off interning with the global
    // RECURSIVE_MEET flag.
    RECURSIVE_MEET++;

    // For-all _ts edges do the Meet.  Some are not-recursive and mapped, some
    // are part of the cycle and mapped, some
    for( int i=0; i<len; i++ ) {
      Type lfi = i<this._ts.length ? this._ts[i] : null;
      Type rti = i<that._ts.length ? that._ts[i] : null;
      Type mti = (lfi==null) ? rti : (rti==null ? lfi : lfi.meet(rti));
      Type mtx = mt._ts[i];     // Prior value, perhaps updated recursively
      Type mts = mtx==null ? mti : mtx.meet(mti); // Meet again
      assert mt._uf==null;      // writing results but value is ignored
      mt._ts[i] = mts;          // Finally update
    }
    // Check for repeats right now
    for( TypeStruct ts : MEETS0.values() )
      if( ts!=mt && ts.equals(mt) )
        { mt.union(ts); mt = ts; break; } // Union together

    // Lower recursive-meet flag.  At this point the Meet 'mt' is still
    // speculative and not interned.
    if( --RECURSIVE_MEET > 0 )
      return mt;                // And, if not yet done, just exit with it

    // Remove any final UF before installation.
    // Do not install until the cycle is complete.
    RECURSIVE_MEET++;
    Ary<Type> reaches = mt.reachable();
    mt = shrink(mt.reachable(),mt);
    assert check_uf(reaches = mt.reachable());
    UF.clear();
    RECURSIVE_MEET--;
    // This completes 'mt' as the Meet structure.
    return mt.install_cyclic(reaches);
  }

  // Install, cleanup and return
  TypeStruct install_cyclic(Ary<Type> reachs) {
    // Check for dups.  If found, delete entire cycle, and return original.
    TypeStruct old = (TypeStruct)intern_lookup();
    // If the cycle already exists, just drop the new Type on the floor and let
    // GC get it and return the old Type.
    if( old == null ) {         // Not a dup
      mark_cyclic(get_cyclic(),reachs);
      assert !_cyclic || repeats_in_cycles()==null;
      rdual();               // Complete cyclic dual
      // Insert all members of the cycle into the hashcons.  If self-symmetric,
      // also replace entire cycle with self at each point.
      if( equals(_dual) ) throw AA.unimpl();
      walk( t -> {
          assert t._hash==0 || t._hash==t.compute_hash();
          if( t.interned() ) return false;
          t.retern()._dual.retern(); return true;
        });

      assert _ts[0].interned();
      old = this;
    }
    MEETS0.clear();
    return old;
  }

  // Make a deep clone of this TypeStruct that is not interned.
  private TypeStruct shallow_clone() {
    assert _cyclic;
    Type[] ts = TypeAry.get(_ts.length);
    Arrays.fill(ts,Type.ANY);
    TypeStruct tstr = malloc(_name,_any,_flds.clone(),ts,_flags.clone());
    tstr._cyclic = true;
    return tstr;
  }

  // Tarjan Union-Find to help build cyclic structures
  private void union( TypeStruct tt) {
    assert !interned() ;
    assert _uf==null && tt._uf==null;
    if( this!=tt )
      _uf = tt;
  }
  private TypeStruct ufind() {
    TypeStruct u = _uf;
    if( u==null ) return this;
    while( u._uf != null ) u = u._uf;
    TypeStruct t = this;
    while( t != u ) { TypeStruct tmp = t._uf; t._uf = u; t=tmp; }
    return u;
  }

  // This is for a struct that has grown 'too deep', and needs to be
  // approximated to avoid infinite growth.
  private static NonBlockingHashMapLong<Type> UF = new NonBlockingHashMapLong<>();
  private static IHashMap OLD2APX = new IHashMap();
  public TypeStruct approx( int cutoff, int alias ) {
    boolean shallow=true;
    for( Type t : _ts )
      if( t._type == TMEMPTR ) { shallow=false; break; }
    if( shallow ) return this;  // Fast cutout for boring structs

    // Scan the old copy for elements that are too deep.
    // 'Meet' those into the clone at one layer up.
    RECURSIVE_MEET++;
    assert UF.isEmpty();
    assert OLD2APX.isEmpty();
    TypeStruct apx = ax_impl_struct( alias, true, cutoff, null, 0, this, this );
    // Remove any leftover internal duplication
    apx = shrink(apx.reachable(),apx);
    RECURSIVE_MEET--;
    TypeStruct rez = this;
    if( apx != this ) {
      Ary<Type> reaches = apx.reachable();
      assert check_uf(reaches);
      assert !check_interned(reaches);
      rez = apx.install_cyclic(reaches);
      assert this.isa(rez);
    }
    UF.clear();
    OLD2APX.clear();
    return rez;
  }

  // Make a new TypeStruct which is the merge of the original TypeStruct with
  // the too-deep parts merged into shallower parts.
  private static TypeStruct ax_impl_struct( int alias, boolean isnews, int cutoff, Ary<TypeStruct> cutoffs, int d, TypeStruct dold, TypeStruct old ) {
    assert old.interned();
    // TODO: If past depth, never use OLD, forces maximal cloning for the
    // last step, as the last step will be MEET with an arbitrary structure.
    // Use alternative OLD past depth, to keep looping unrelated types
    // folding up.  Otherwise unrelated types might expand endlessly.
    TypeStruct nt = OLD2APX.get(old);
    if( nt != null ) return ufind(nt);

    if( isnews ) {            // Depth-increasing struct?
      if( d==cutoff ) {       // Cannot increase depth any more
        cutoffs.push(old);    // Save cutoff point for later MEET
        return OLD2APX.get(dold); // Return last valid depth - forces cycle
      } else {
        assert cutoffs == null; // Approaching max depth, make a place to record cutoffs
        if( d+1==cutoff ) cutoffs = new Ary<>(TypeStruct.class);
      }
      d++;              // Increase depth
      dold = old;       // And this is the last TypeStruct seen at this depth
    }
    // Clone the old, to make the approximation into
    TypeStruct nts = (TypeStruct)old.clone();
    nts._flds  = old._flds .clone();
    nts._flags = old._flags.clone();
    nts._ts    = TypeAry.clone(old._ts);
    OLD2APX.put(old,nts);
    for( int i=0; i<old._ts.length; i++ ) // Fill clone with approximation
      if( old._ts[i]._type == TMEMPTR )
        nts._ts[i] = ax_impl_ptr (alias,cutoff,cutoffs,d,dold,(TypeMemPtr)old._ts[i]);
      else if( old._ts[i]._type == TFUNPTR )
        nts._ts[i] = ax_impl_fptr(alias,cutoff,cutoffs,d,dold,(TypeFunPtr)old._ts[i]);
    if( isnews && d==cutoff ) {
      while( !cutoffs.isEmpty() ) { // At depth limit, meet with cutoff to make the approximation
        Type mt = ax_meet(new BitSetSparse(), nts,cutoffs.pop());
        assert mt==nts;
      }
    }
    OLD2APX.put(old,null); // Do not keep sharing the "tails"
    return nts;
  }

  private static Type ax_impl_ptr( int alias, int cutoff, Ary<TypeStruct> cutoffs, int d, TypeStruct dold, TypeMemPtr old ) {
    assert old.interned();
    // TODO: If past depth, never use OLD, forces maximal cloning for the
    // last step, as the last step will be MEET with an arbitrary structure.
    // Use alternative OLD past depth, to keep looping unrelated types
    // folding up.  Otherwise unrelated types might expand endlessly.
    TypeMemPtr nt = OLD2APX.get(old);
    if( nt != null ) return ufind(nt);

    // Walk internal structure, meeting into the approximation
    TypeMemPtr nmp = (TypeMemPtr)old.clone();
    OLD2APX.put(old,nmp);
    if( old._obj instanceof TypeStruct )
      nmp._obj = ax_impl_struct(alias,nmp._aliases.test(alias),cutoff,cutoffs,d,dold,(TypeStruct)old._obj);
    else if( old._obj == TypeObj.XOBJ || old._obj==nmp._obj )
      ; // No change to nmp._obj
    else if( old._obj == TypeObj.OBJ )
      nmp._obj = TypeObj.OBJ;   // Falls hard
    else
      throw com.cliffc.aa.AA.unimpl();
    OLD2APX.put(old,null);      // Do not keep sharing the "tails"
    return nmp;
  }
  private static Type ax_impl_fptr( int alias, int cutoff, Ary<TypeStruct> cutoffs, int d, TypeStruct dold, TypeFunPtr old ) {
    assert old.interned();
    // TODO: If past depth, never use OLD, forces maximal cloning for the
    // last step, as the last step will be MEET with an arbitrary structure.
    // Use alternative OLD past depth, to keep looping unrelated types
    // folding up.  Otherwise unrelated types might expand endlessly.
    TypeFunPtr nt = OLD2APX.get(old);
    if( nt != null ) return ufind(nt);

    // Walk internal structure, meeting into the approximation
    TypeFunPtr nmp = (TypeFunPtr)old.clone();
    OLD2APX.put(old,nmp);
    nmp._args = ax_impl_struct(alias,false,cutoff,cutoffs,d,dold,old._args);
    OLD2APX.put(old,null);      // Do not keep sharing the "tails"
    return nmp;
  }

  // Update-in-place 'meet' of pre-allocated new types.  Walk all the old type
  // and meet into the corresponding new type.  Changes the internal edges of
  // the new types, so their hash remains undefined.
  private static Type ax_meet( BitSetSparse bs, Type nt, Type old ) {
    assert old.interned();
    if( nt._hash != 0 && nt.interned() ) return nt.meet(old);
    assert nt._hash==0;         // Not definable yet
    nt = ufind(nt);
    if( nt == old ) return old;
    if( bs.tset(nt._uid,old._uid) ) return nt; // Been there, done that

    // TODO: Make a non-recursive "meet into".
    // Meet old into nt
    switch( nt._type ) {
    case TSCALAR: break; // Nothing to meet
    case TFUNPTR: {
      TypeFunPtr nptr = (TypeFunPtr)nt;
      if( old == Type.NIL || old == Type.XNIL ) return nptr.ax_meet_nil(old);
      if( old == Type.SCALAR )
        return union(nt,old); // Result is a scalar, which changes the structure of the new types.
      if( old == Type.XSCALAR ) break; // Result is the nt unchanged
      if( !(old instanceof TypeFunPtr) ) throw AA.unimpl(); // Not a xscalar, not a funptr, probably falls to scalar
      TypeFunPtr optr = (TypeFunPtr)old;
      nptr._fidxs = nptr._fidxs.meet(optr._fidxs);
      // While structs normally meet, function args *join*, although the return still meets.
      nptr._args = (TypeStruct)ax_meet(bs,nptr._args,optr._args);
      //Type ret = ax_meet(bs,nptr._args._ts[0],optr._args._ts[0]);
      //TypeStruct nxargs = nptr._args.rdual();
      //TypeStruct oxargs = optr._args.rdual();
      //nptr._args = (TypeStruct)ax_meet(bs,nxargs,oxargs).rdual();
      //nptr._args._ts[0] = ret;
      break;
    }
    case TMEMPTR: {
      TypeMemPtr nptr = (TypeMemPtr)nt;
      if( old == Type.NIL || old == Type.XNIL ) return nptr.ax_meet_nil(old);
      if( old == Type.SCALAR )
        return union(nt,old); // Result is a scalar, which changes the structure of the new types.
      if( old == Type.XSCALAR ) break; // Result is the nt unchanged
      if( !(old instanceof TypeMemPtr) ) throw AA.unimpl(); // Not a xscalar, not a memptr, probably falls to scalar
      TypeMemPtr optr = (TypeMemPtr)old;
      nptr._aliases = nptr._aliases.meet(optr._aliases);
      nptr._obj = (TypeObj)ax_meet(bs,nptr._obj,optr._obj);
      break;
    }
    case TSTRUCT:
      if( old == TypeObj.OBJ ) { nt = TypeObj.OBJ; break; }
      if( old == TypeObj.XOBJ ) break; // No changes, take nt as it is
      if( !(old instanceof TypeStruct) ) throw AA.unimpl();
      TypeStruct ots = (TypeStruct)old, nts = (TypeStruct)nt;
      assert nts._uf==null;     // Already handled by the caller
      // Compute a new target length.  Generally size is unchanged, but will
      // change if mixing structs.
      int len = ots.len(nts);     // New length
      if( len != nts._ts.length ) { // Grow/shrink as needed
        nts._flds = Arrays.copyOf(nts._flds , len);
        nts._ts   = Arrays.copyOf(nts._ts   , len);
        nts._flags= Arrays.copyOf(nts._flags, len);
      }
      int clen = Math.min(len,ots._ts.length);
      // Meet all the non-recursive parts
      nts._any &= ots._any;
      for( int i=0; i<clen; i++ ) {
        nts._flds [i] = smeet(nts._flds  [i],ots._flds  [i]); // Set the Meet of field names
        nts._flags[i] = fmeet(nts._flags[i],ots._flags[i]);
      }
      // Now recursively do all common fields
      for( int i=0; i<clen; i++ )
        nts._ts[i] = ax_meet(bs,nts._ts[i],ots._ts[i]);
      break;
    default: throw AA.unimpl();
    }
    return nt;
  }

  // Walk an existing, not-interned, structure.  Stop at any interned leaves.
  // Check for duplicating an interned Type or a UF hit, and use that instead.
  // Computes the final hash code.
  private static IHashMap DUPS = new IHashMap();
  private static TypeStruct shrink( Ary<Type> reaches, TypeStruct tstart ) {
    assert DUPS.isEmpty();
    // Structs never change their hash based on field types.  Set their hash first.
    for( int i=0; i<reaches._len; i++ ) {
      Type t = reaches.at(i);
      if( t instanceof TypeStruct )
        t._hash = t.compute_hash();
    }
    for( int i=0; i<reaches._len; i++ ) {
      Type t = reaches.at(i);// TypeMemPtr hash changes based on field contents.
      if( !(t instanceof TypeStruct) ) {
        assert t instanceof TypeMemPtr || t instanceof TypeFunPtr;
        if( t._hash == 0 )
          t._hash = t.compute_hash();
      }
    }

    // Need back-edges to do this iteratively in 1 pass.  This algo just sweeps
    // until no more progress, but with generic looping instead of recursion.
    boolean progress = true;
    while( progress ) {
      progress = false;
      DUPS.clear();
      for( int j=0; j<reaches._len; j++ ) {
        Type t = reaches.at(j);
        Type t0 = ufind(t);
        Type t1 = t0.intern_lookup();
        if( t1==null ) t1 = DUPS.get(t0);
        if( t1 != null ) t1 = ufind(t1);
        if( t1 == t0 ) continue; // This one is already interned
        if( t1 != null ) { union(t0,t1); progress = true; continue; }

        switch( t._type ) {
        case TMEMPTR:           // Update TypeMemPtr internal field
          TypeMemPtr tm = (TypeMemPtr)t0;
          TypeObj t4 = tm._obj;
          TypeObj t5 = ufind(t4);
          if( t4 != t5 ) {
            tm._obj = t5;
            progress |= post_mod(tm);
            if( !t5.interned() ) reaches.push(t5);
          }
          break;
        case TFUNPTR:           // Update TypeFunPtr internal field
          TypeFunPtr tfptr = (TypeFunPtr)t0;
          TypeStruct t6 = tfptr._args;
          TypeStruct t7 = ufind(t6);
          if( t6 != t7 ) {
            tfptr._args = t7;
            progress |= post_mod(tfptr);
            if( !t7.interned() ) reaches.push(t7);
          }
          break;
        case TSTRUCT:           // Update all TypeStruct fields
          TypeStruct ts = (TypeStruct)t0;
          for( int i=0; i<ts._ts.length; i++ ) {
            Type tfld = ts._ts[i];
            progress |= (tfld != (ts._ts[i] = ufind(tfld)));
          }
          break;
        default: break;
        }
        DUPS.put(t0);
      }
    }
    DUPS.clear();
    return ufind(tstart);
  }

  private static <T extends Type> T pre_mod(Type t, T tf) {
    T tu = ufind(tf);
    if( tu == tf ) return tf;   // No change
    DUPS.remove(t);   // Remove before field update changes equals(),hashCode()
    return tu;
  }
  // Set hash after field mod, and re-install in dups
  private static boolean post_mod(Type t) {
    t._hash = t.compute_hash();
    DUPS.put(t);
    return true;
  }


  @SuppressWarnings("unchecked")
  private static <T extends Type> T ufind(T t) {
    T t0 = (T)UF.get(t._uid), tu;
    if( t0 == null ) return t;  // One step, hit end of line
    // Find end of U-F line
    while( (tu = (T)UF.get(t0._uid)) != null ) t0=tu;
    // Set whole line to 1-step end of line
    while( (tu = (T)UF.get(t ._uid)) != null ) { assert t._uid != t0._uid; UF.put(t._uid,t0); t=tu; }
    return t0;
  }
  private static <T extends Type> T union( T lost, T kept) {
    if( lost == kept ) return kept;
    assert lost._hash==0 || !lost.interned();
    assert UF.get(lost._uid)==null && UF.get(kept._uid)==null;
    assert lost._uid != kept._uid;
    UF.put(lost._uid,kept);
    return kept;
  }

  // Walk, looking for prior interned
  private static boolean check_interned(Ary<Type> reachs) {
    for( Type t : reachs )
      if( t.intern_lookup() != null )
        return true;
    return false;
  }

  // Reachable collection of TypeMemPtr and TypeStruct.
  // Optionally keep interned Types.  List is pre-order.
  Ary<Type> reachable() { return reachable(false); }
  private Ary<Type> reachable( boolean keep ) {
    Ary<Type> work = new Ary<>(new Type[1],0);
    push(work, keep, this);
    int idx=0;
    while( idx < work._len ) {
      Type t = work.at(idx++);
      switch( t._type ) {
      case TMEMPTR:  push(work, keep, ((TypeMemPtr)t)._obj); break;
      case TFUNPTR:  push(work, keep, ((TypeFunPtr)t)._args); break;
      case TSTRUCT:  for( Type tf : ((TypeStruct)t)._ts ) push(work, keep, tf); break;
      default: break;
      }
    }
    return work;
  }
  private void push( Ary<Type> work, boolean keep, Type t ) {
    int y = t._type;
    if( (y==TMEMPTR || y==TFUNPTR || y==TSTRUCT) &&
        (keep || t._hash==0 || !t.interned()) && work.find(t)==-1 )
      work.push(t);
  }

  // Walk, looking for not-minimal.  Happens during 'approx' which might
  // require running several rounds of 'replace' to fold everything up.
  private static boolean check_uf(Ary<Type> reaches) {
    int err=0;
    HashMap<Type,Type> ss = new HashMap<>();
    for( Type t : reaches ) {
      Type tt;
      if( ss.get(t) != null || // Found unresolved dup; ts0.equals(ts1) but ts0!=ts1
          ((tt = t.intern_lookup()) != null && tt != t) ||
          (t instanceof TypeStruct && ((TypeStruct)t)._uf != null) || // Found unresolved UF
          ufind(t) != t )
        err++;
      ss.put(t,t);
    }
    return err == 0;
  }

  // Get BitSet of not-interned cyclic bits.  Almost classic cycle-finding
  // algorithm; since Structs have labeled out-edges (with field names), we can
  // have multiple output edges from the same node (struct) to the same
  // TypeMemPtr.  The classic cycle-finders do not work with multi-edges.
  private BitSet get_cyclic( ) {
    return get_cyclic(new BitSet(),new VBitSet(),new Ary<>(Type.class),this);
  }
  private static BitSet get_cyclic(BitSet bcs, VBitSet bs, Ary<Type> stack, Type t ) {
    if( t.interned() ) return bcs;
    if( bs.tset(t._uid) ) {     // If visiting again... have found a cycle t->....->t
      // All on the stack are flagged as being part of a cycle
      int i;
      i=stack._len-1;
      while( i >= 0 && stack.at(i)!=t ) i--;
      if( i== -1 ) return bcs;  // Due to multi-edges, we might not find if dupped, so just ignore
      for( ; i < stack._len; i++ )
        bcs.set(stack.at(i)._uid);
      bcs.set(t._uid);
      return bcs;
    }
    stack.push(t);              // Push on stack, in case a cycle is found
    switch( t._type ) {
    case TMEMPTR: get_cyclic(bcs,bs,stack,((TypeMemPtr)t)._obj ); break;
    case TFUNPTR: get_cyclic(bcs,bs,stack,((TypeFunPtr)t)._args); break;
    case TSTRUCT: for( Type tf : ((TypeStruct)t)._ts ) get_cyclic(bcs,bs,stack,tf); break;
    }
    stack.pop();                // Pop, not part of anothers cycle
    return bcs;
  }
  @SuppressWarnings("unchecked")
  private void mark_cyclic( BitSet bcs, Ary<Type> reaches ) {
    for( Type t : reaches ) {
      if( t instanceof TypeStruct ) {
        ((TypeStruct)t)._cyclic = bcs.get(t._uid);
        TypeStruct ts = (TypeStruct)t;
        ts._ts = TypeAry.hash_cons(ts._ts); // hashcons cyclic arrays
      } else if( t instanceof TypeMemPtr ) {
        ((TypeMemPtr)t)._cyclic = bcs.get(t._uid);
      } else {
        ((TypeFunPtr)t)._cyclic = bcs.get(t._uid);
      }
      t._dual=null;             // Remove any duals, so re-inserted clean
    }
  }

  // If unequal length; then if short is low it "wins" (result is short) else
  // short is high and it "loses" (result is long).
  private int len( TypeStruct tt ) { return _ts.length <= tt._ts.length ? len0(tt) : tt.len0(this); }
  private int len0( TypeStruct tmax ) { return _any ? tmax._ts.length : _ts.length; }


  // ------ String field name lattice ------
  static private boolean fldTop( String s ) { return s.charAt(0)=='*'; }
  static public  boolean fldBot( String s ) { return s.charAt(0)=='.'; }
  static public  String fldTop( ) { return "*"; }
  static public  String fldBot( ) { return "."; }
  // String meet
  private static String smeet( String s0, String s1 ) {
    if( s0==null || fldTop(s0) ) return s1;
    if( s1==null || fldTop(s1) ) return s0;
    if( fldBot(s0) ) return s0;
    if( fldBot(s1) ) return s1;
    if( Util.eq(s0,s1) ) return s0;
    return fldBot(); // fldBot
  }
  private static String sdual( String s ) {
    if( fldTop(s) ) return fldBot();
    if( fldBot(s) ) return fldTop();
    return s;
  }

  // ------ Flags lattice: 2 bits field mod, 1 bit dirty ------
  // Accessors
  public static byte    fmod ( byte f ) { return (byte)(f&3); }
  //public static boolean dirty( byte f ) { return 0 !=  (f&4); } // Set bit is dirty
  public static boolean dirty( byte f ) { return false; } // Turned off for now
  public byte fmod( int idx ) { return fmod(_flags[idx]); }

  // Setters
  public static byte set_fmod ( byte flags, byte mod     ) { assert 0<=mod && mod <=3; return (byte)((flags&~3)|mod); }
  //public static byte set_dirty( byte flags, boolean dirty) { assert !dirty || (flags&3)==FRW; return (byte)(dirty? (flags|4) : (flags&~4)); }
  public static byte make_flag( byte mod , boolean dirty ) {
    assert 0<=mod && mod <=3;
    if( mod != FRW ) dirty=false;
    //return (byte)(mod|(dirty?4:0));
    return mod;
  }

  // OR bits: If either is dirty, then dirty.
  // Similarly for field mods.
  public static byte fmeet( byte f0, byte f1 ) { return (byte)(f0|f1); }
  public static byte fdual( byte f ) {
    int flag = (~f)&3;                  // Dual all the bits
    if( flag==1 || flag==2 ) flag ^= 3; // Recover final & r/w dual
    return (byte)flag;
  }
  private static byte flag_top() { return 0; }
  //// Return flags cleaned
  //private byte[] clean_flags() {
  //  if( !is_dirty() ) return _flags; // Already clean
  //  byte[] flags = _flags.clone();   // Clone flags
  //  for( int i=0; i<_flags.length; i++ ) // And mark clone all clean
  //    flags[i] = set_dirty(_flags[i],false);
  //  return flags;
  //}
  //// Return true if any flag is dirty
  //private boolean is_dirty() {
  //  for( int i=0; i<_flags.length; i++ )
  //    if( dirty(_flags[i]) )
  //      return false;
  //  return true;
  //}
  // Get whole flags, only suitable for copying to a constructor as-is.
  public byte flags(int idx) { return _flags[idx]; }
  public byte[] flags_clone() { return _flags.clone(); }

  // ------ Utilities -------
  // Return the index of the matching field (or nth tuple), or -1 if not found
  // or field-num out-of-bounds.
  public int find( String fld ) {
    for( int i=0; i<_flds.length; i++ )
      if( fld.equals(_flds[i]) )
        return i;
    return -1;
  }

  public Type at( int idx ) { return _ts[idx]; }
  public Type last() { return _ts[_ts.length-1]; }

  // Update (approximately) the current TypeObj.  Updates the named field.
  @Override public TypeObj update(byte fin, String fld, Type val) { return update(fin,fld,val,false); }
  @Override public TypeObj st    (byte fin, String fld, Type val) { return update(fin,fld,val,true ); }
  private TypeObj update(byte fin, String fld, Type val, boolean precise) {
    assert val.isa_scalar();
    // Pointers & Memory to a Store can fall during GCP, and go from r/w to r/o
    // and the StoreNode output must remain monotonic.  This means store
    // updates are allowed to proceed even if in-error.
    byte[] flags = _flags.clone();
    Type[] ts    = TypeAry.clone(_ts);
    int idx = find(fld);
    if( idx == -1 )             // Unknown field, might change all fields
      for( int i=0; i<_flags.length; i++ )
        _update(flags,ts,fin,i,val,precise);
    else                        // Update the one field
      _update(flags,ts,fin,idx,val,precise);
    return malloc(_name,_any,_flds,ts,flags).hashcons_free();
  }
  private static void _update( byte[] flags, Type[] ts, byte fin, int idx, Type val, boolean precise ) {
    byte fmod = fmod(flags[idx]);
    if( fmod==FFNL || fmod==FRO )
      precise=false;      // Illegal store into final/r-o field
    ts[idx] =  precise ? val : ts[idx].meet(val);
    flags[idx] = set_fmod(flags[idx],precise ? fin : fmeet(fmod,fin));
  }

  // Allowed to update this field?
  //@Override public boolean can_update(String fld) {
  //  int idx = find(fld);
  //  return idx != -1 && can_update(idx);
  //}
  public boolean can_update(int idx) { return fmod(_flags[idx]) == FRW || fmod(_flags[idx]) == FUNK; }

  //// Identical struct but clean.  Complicated because has to do a recursive update.
  //@Override public TypeStruct clean() {
  //  if( this==ALLSTRUCT )       // Infinitely extended extra fields are bottom & dirty.
  //    return ALLSTRUCT;         // TODO: Think this is wrong
  //    //return ALLSTRUCT; // Shortcut
  //  if( this==GENERIC   ) return GENERIC;
  //  if( !_cyclic ) {            // Not cyclic, normal recursive walk
  //    Type[] ts = TypeAry.clone(_ts);
  //    for( int i=0; i<ts.length; i++ )
  //      if( ts[i] != null )
  //        ts[i] = ts[i].clean();
  //    return malloc(_name,_any,_flds,ts,clean_flags()).hashcons_free();
  //  }
  //  // Cyclic, but perhaps already clean
  //  Ary<Type> reaches = reachable(true);
  //  boolean dirty = false;
  //  for( Type t : reaches )
  //    if( t instanceof TypeStruct && ((TypeStruct)t).is_dirty() )
  //      { dirty=true; break; }
  //  if( !dirty ) return this;   // Already clean.
  //
  //  //// Need to clone the existing structure, then make it clean
  //  //RECURSIVE_MEET++;
  //  //assert OLD2APX.isEmpty();
  //  //TypeStruct cln = clone_clean_str(this);
  //  //RECURSIVE_MEET--;
  //  //reaches = cln.reachable();  // Recompute on the new types
  //  //TypeStruct cln2 = cln.install_cyclic(reaches);
  //  //assert cln2.isa(this);
  //  //OLD2APX.clear();
  //  //return cln2;
  //  throw com.cliffc.aa.AA.unimpl();
  //}

  //private static TypeStruct clone_clean_str(TypeStruct dirty) {
  //  TypeStruct ts = OLD2APX.get(dirty);
  //  if( ts != null ) return ts;
  //  if( dirty._cln ) throw com.cliffc.aa.AA.unimpl(); // Return the clean copy
  //  ts = dirty.shallow_clone();
  //  ts._cln = true;
  //  ts._hash = ts.compute_hash(); // Hash does not depend on _ts, which are not set yet
  //  OLD2APX.put(dirty,ts);
  //  for( int i=0; i<ts._ts.length; i++ ) {
  //    Type td = dirty._ts[i];
  //    ts._ts[i] = td instanceof TypeMemPtr ? clone_clean_ptr((TypeMemPtr)td) : td;
  //  }
  //  return ts;
  //}
  //private static TypeMemPtr clone_clean_ptr(TypeMemPtr dirty) {
  //  TypeMemPtr nmp = OLD2APX.get(dirty);
  //  if( nmp != null ) return nmp;
  //  nmp = (TypeMemPtr)dirty.clone();
  //  OLD2APX.put(dirty,nmp);
  //  if( dirty._obj instanceof TypeStruct )
  //    nmp._obj = clone_clean_str((TypeStruct)dirty._obj);
  //  nmp._hash = nmp.compute_hash();
  //  TypeMemPtr x = (TypeMemPtr)nmp.intern_lookup(); // Check for prior hit
  //  if( x==null ) return nmp;
  //  OLD2APX.put(dirty,x);
  //  return nmp.free(x);
  //}

  // True if isBitShape on all bits
  @Override public byte isBitShape(Type t) {
    if( isa(t) ) return 0; // Can choose compatible format
    if( t.isa(this) ) return 0; // TODO: really: test same flds, each fld isBitShape
    return 99;
  }

  @Override public Type meet_nil(Type nil) { return this; }

  @Override boolean contains( Type t, VBitSet bs ) {
    if( bs==null ) bs=new VBitSet();
    if( bs.tset(_uid) ) return false;
    for( Type t2 : _ts) if( t2==t || t2.contains(t,bs) ) return true;
    return false;
  }

  @SuppressWarnings("unchecked")
  @Override void walk( Predicate<Type> p ) {
    if( p.test(this) )
      for( Type _t : _ts ) _t.walk(p);
  }
}
