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
  private byte[] _flags; // Field mod types; see fmeet, fdual, fstr.
  boolean _open; // Fields after _ts.length are treated as ALL (or ANY)

  boolean _cyclic; // Type is cyclic.  This is a summary property, not a description of value sets, hence is not in the equals or hash
  private TypeStruct     ( String name, boolean any, String[] flds, Type[] ts, byte[] flags, boolean open) { super(TSTRUCT, name, any); init(name, any, flds,ts,flags,open); }
  private TypeStruct init( String name, boolean any, String[] flds, Type[] ts, byte[] flags, boolean open) {
    super.init(TSTRUCT, name, any);
    _flds  = flds;
    _ts    = ts;
    _flags = flags;
    _open  = open;
    return this;
  }
  // Precomputed hash code.  Note that it can NOT depend on the field types -
  // because during recursive construction the types are not available.
  @Override int compute_hash() {
    int hash = super.compute_hash()+(_open?1023:0), hash1=hash;
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
    if( _ts.length != t._ts.length || _open != t._open ) return 0;
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
    return repeats_in_cycles(this,new VBitSet());
  }
  @Override TypeStruct repeats_in_cycles(TypeStruct head, VBitSet bs) {
    if( bs.tset(_uid) ) return null;
    if( this!=head && equals(head) ) return this;
    for( Type t : _ts ) {
      TypeStruct ts = t.repeats_in_cycles(head,bs);
      if( ts!=null ) return ts;
    }
    return null;
  }

  private static boolean isDigit(char c) { return '0' <= c && c <= '9'; }
  private boolean is_tup() { return _flds.length<=1 || fldTop(_flds[0]) || fldBot(_flds[0]) || isDigit(_flds[1].charAt(0)); }
  public String str( VBitSet dups) {
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return "$"; // Break recursive printing cycle
    // Special shortcut for the all-prims display type
    if( find("!") != -1 && find("math_pi") != -1 )
      return (_any?"~":"") + (_ts[1] instanceof TypeFunPtr
        ? (((TypeFunPtr)_ts[1])._fidxs.above_center() ? "{PRIMS}" : "{LOW_PRIMS}")
                              : "{PRIMS_"+_ts[1]+"}");

    SB sb = new SB();
    if( _any ) sb.p('~');
    sb.p(_name);
    boolean is_tup = is_tup();
    sb.p(is_tup ? "(" : "@{");
    for( int i=0; i<_flds.length; i++ ) {
      if( !is_tup )
        sb.p(_flds[i]).p(fstr(_fmod(i))).p('='); // Field name, access mod
      Type t = at(i);
      if( t==null ) sb.p("!");  // Graceful with broken types
      else if( t==SCALAR ) ;    // Default answer, do not print
      else sb.p(t.str(dups));   // Recursively print field type
      sb.p(';');
    }
    if( _open ) sb.p("...");    // More fields allowed
    else if( _flds.length>0 ) sb.unchar();
    sb.p(!is_tup ? "}" : ")");
    return sb.toString();
  }
  @Override SB dstr( SB sb, VBitSet dups ) {
    sb.p('_').p(_uid);
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return sb.p('$'); // Break recursive printing cycle
    // Special shortcut for the all-prims display type
    if( find("!") != -1 && find("math_pi") != -1 && _ts[1] instanceof TypeFunPtr )
      return sb.p(_any?"~":"").p(((TypeFunPtr)_ts[1])._fidxs.above_center()
                                 ? "{PRIMS}" : "{LOW_PRIMS}");

    if( _any ) sb.p('~');
    sb.p(_name);
    boolean is_tup = is_tup();
    if( !is_tup ) sb.p('@');    // Not a tuple
    sb.p(is_tup ? '(' : '{').nl().ii(1); // open struct, newline, increase_indent
    for( int i=0; i<_flds.length; i++ ) {
      sb.i();                   // indent, 1 field per line
      Type t = at(i);
      if( !is_tup )
        sb.p(_flds[i]).p(fstr(_fmod(i))).p('='); // Field name, access mod
      if( t==null ) sb.p("!");  // Graceful with broken types
      else if( t==SCALAR ) ;    // Default answer, do not print
      else t.dstr(sb,dups);     // Recursively print field type
      sb.p(';').nl();           // One field per line
    }
    if( _open ) sb.i().p("...").nl(); // More fields allowed
    return sb.di(1).i().p(!is_tup ? '}' : ')');
  }
  // Print with memory instead of recursion
  @Override public SB str(SB sb, VBitSet dups, TypeMem mem) {
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return sb.p('$'); // Break recursive printing cycle
    // Special shortcut for the all-prims display type
    if( find("!") != -1 && find("math_pi") != -1 && _ts[1] instanceof TypeFunPtr )
      return sb.p(_any?"~":"").p(((TypeFunPtr)_ts[1])._disp.above_center()
                  ? "{PRIMS}" : "{LOW_PRIMS}");
    if( _any ) sb.p('~');
    sb.p(_name);
    boolean is_tup = is_tup();
    if( !is_tup ) sb.p('@');    // Not a tuple
    sb.p(is_tup ? '(' : '{');
    for( int i=0; i<_flds.length; i++ ) {
      if( Util.eq(_flds[i],"^") ) continue; // Do not print the ever-present display
      Type t = at(i);
      if( !is_tup )
        sb.p(_flds[i]).p(fstr(_fmod(i))).p('='); // Field name, access mod
      if( t==null ) sb.p("!");  // Graceful with broken types
      else if( t==SCALAR ) ;    // Default answer, do not print
      else t.str(sb,dups,mem);  // Recursively print field type
      sb.p(';');
    }
    if( _open ) sb.p("...");     // More fields allowed
    else if( _flds.length>0 ) sb.unchar();
    return sb.p(!is_tup ? '}' : ')');
  }

  // Unlike other types, TypeStruct never makes dups - instead it might make
  // cyclic types for which a DAG-like bottom-up-remove-dups approach cannot work.
  private static TypeStruct FREE=null;
  @Override protected TypeStruct free( TypeStruct ret ) { FREE=this; return ret; }
  static TypeStruct malloc( String name, boolean any, String[] flds, Type[] ts, byte[] flags, boolean open ) {
    assert check_name(name);
    if( FREE == null ) return new TypeStruct(name, any,flds,ts,flags,open);
    TypeStruct t1 = FREE;  FREE = null;
    return t1.init(name, any,flds,ts,flags,open);
  }
  private TypeStruct hashcons_free() {
    _ts = TypeAry.hash_cons(_ts);
    TypeStruct t2 = (TypeStruct)hashcons();
    return this==t2 ? this : free(t2);
  }

  // ------ Flags lattice: 1 bit field mod ------
  // In other times, I've had other flags, and probably will again.
  // Flags are a 'short' stored as bytes, and the flag parts are 'bytes'.
  // Unfortunate lack of Java-int-typing to help here, otherwise all are just bytes.

  // Field modifiers.
  public static final byte FRW  = 1; // Read/Write
  public static final byte FFNL = 0; // Final field (no load will witness other value)
  public static final byte FHI  = 2; // Field mod is inverted
  public static final byte FTOP = 1; // Flags top; must be 1 if MEET is AND
  public static final byte FBOT = 0; // Flags bot; must be 0 if MEET is AND
  // Printers
  private static String fstr   ( short f ) { return new String[]{"=",":","~:","~="}[f]; }
  public  static String fstring( short f ) { return new String[]{"final","read-write","~read-write","~final"}[f]; }
  // Array of flags
  public static byte[] new_flags(int n, short flag) { byte[] bs = new byte[n]; Arrays.fill(bs,(byte)flag); return bs; }
  public static byte[] fbots(int n) { return new_flags(n,bot_flag); }
  public static byte[] frws (int n) { return new_flags(n,frw_flag); }
  public static byte[] ffnls(int n) { return new_flags(n,fnl_flag); }
  // Get whole flags, only suitable for copying to a constructor as-is.
  public static short  flags(byte[] flags, int idx) { return flags[idx]; }
  public static byte[] flags(byte[] flags, int idx, short flag ) { flags[idx] = (byte)flag; return flags; }
  // Accessors for field mods from flags
  public static byte fmod( short flag ) {
    //assert (flag&FHI)==0;       // Do not ask for inverted field mod
    return _fmod(flag);
  }
  // Used by printers
  private static byte _fmod( short flag ) { return (byte)(flag&3); }
  // Make a flags from all parts
  public static short make_flag( byte mod ) { assert mod==FRW || mod== FFNL; return mod; }
  // Modify just the field mods of a flags
  public static short set_fmod ( short flags, byte mod ) { assert mod==FRW || mod== FFNL; return mod; }

  // Shortcuts for the current flags[] as opposed to independent flags[]
  public byte fmod(int idx) { return fmod(flags(idx)); }
  private byte _fmod(int idx) { return _fmod(flags(idx)); }
  public short flags(int idx) { return flags(_flags,idx); }
  public byte[] flags(int idx, short flag) { return flags(_flags,idx,flag); }


  // MEET is MIN
  public static short fmeet( short f0, short f1 ) { return (short)Math.min(f0,f1); }
  public static short fdual( short f ) { return (short)(f^3); }
  // Some precooked flags: combination of field mods and anything else (not current used)
  static final short fnl_flag = make_flag(FFNL); // Field final
  static final short frw_flag = make_flag(FRW ); // Field R/W
  static final short top_flag = make_flag(FTOP); // Flags top; must be 1 if MEET is AND
  static final short bot_flag = make_flag(FBOT); // Flags bot; must be 0 if MEET is AND
  static {
    assert fmeet(fdual(fnl_flag),fdual(frw_flag))==fdual(frw_flag); // ~final .isa( ~rw ) 3 isa 2
    assert fmeet(fdual(fnl_flag),     (frw_flag))==     (frw_flag); // ~final .isa(  rw ) 3 isa 1
    assert fmeet(fdual(fnl_flag),     (fnl_flag))==     (fnl_flag); // ~final .isa(final) 3 isa 0
    assert fmeet(fdual(frw_flag),     (frw_flag))==     (frw_flag); // ~rw    .isa(  rw ) 2 isa 1
    assert fmeet(fdual(frw_flag),     (fnl_flag))==     (fnl_flag); // ~rw    .isa(final) 2 isa 0
    assert fmeet(     (frw_flag),     (fnl_flag))==     (fnl_flag); //  rw    .isa(final) 1 isa 0
  }

  // Default tuple field names - all bottom-field names
  static String[] flds(String... fs) { return fs; }
  public  static final String[] ARGS_X  = flds("^","x");     // Used for functions of 1 arg
  public  static final String[] ARGS_XY = flds("^","x","y"); // Used for functions of 2 args
  public  static Type[] ts() { return TypeAry.get(0); }
  public  static Type[] ts(Type t0) { Type[] ts = TypeAry.get(1); ts[0]=t0; return ts;}
  public  static Type[] ts(Type t0, Type t1) { Type[] ts = TypeAry.get(2); ts[0]=t0; ts[1]=t1; return ts;}
  public  static Type[] ts(Type t0, Type t1, Type t2) { Type[] ts = TypeAry.get(3); ts[0]=t0; ts[1]=t1; ts[2]=t2; return ts;}
  public  static Type[] ts(Type t0, Type t1, Type t2, Type t3) { Type[] ts = TypeAry.get(4); ts[0]=t0; ts[1]=t1; ts[2]=t2; ts[3]=t3; return ts;}
  public  static Type[] ts(int n) { Type[] ts = TypeAry.get(n); Arrays.fill(ts,SCALAR); return ts; } // All Scalar fields

  public  static TypeStruct make(Type[] ts) { return malloc(ts).hashcons_free(); }
  public  static TypeStruct malloc(Type[] ts) {
    String[] flds = new String[ts.length];
    Arrays.fill(flds,fldBot());
    return malloc("",false,flds,ts,fbots(ts.length),false);
  }

  // Function formals, used by FunNode.
  // Generic function arguments.  Slot 0 is the display.
  public static TypeStruct make_args(Type[] ts) { return make_x_args(false,ts); }
  public static TypeStruct make_x_args(boolean any, Type[] ts) {
    String[] args = new String[ts.length];
    Arrays.fill(args,any ? fldTop() : fldBot());
    args[0] = "^";
    return make_args(any,args,ts);
  }
  public static TypeStruct make_args(String[] flds, Type[] ts) { return make_args(false,flds,ts); }
  // First field is the display
  public static TypeStruct make_args(boolean any, String[] flds, Type[] ts) {
    assert Util.eq(flds[0],"^");
    assert ts[0].is_display_ptr() && ts[0]==ts[0].simple_ptr(); // Simple display ptrs only
    byte[] fs = fbots(ts.length);
    return malloc("",any,flds,ts,fs,false).hashcons_free();
  }
  public  static TypeStruct make(String[] flds, Type[] ts) { return malloc("",false,flds,ts,fbots(ts.length),false).hashcons_free(); }
  public  static TypeStruct make(String[] flds, Type[] ts, byte[] flags) { return malloc("",false,flds,ts,flags,false).hashcons_free(); }
  public  static TypeStruct make(String name, String[] flds, Type[] ts, byte[] flags) { return malloc(name,false,flds,ts,flags,false).hashcons_free(); }
  public  static TypeStruct make(String name, String[] flds, Type[] ts, byte[] flags, boolean open) { return malloc(name,false,flds,ts,flags,open).hashcons_free(); }
  public  static TypeStruct make(boolean any, String[] flds, Type[] ts, byte[] flags, boolean open) { return malloc("",any,flds,ts,flags,open).hashcons_free(); }

  // Generic parser struct object, slot 0 is the display and is NO_DISP post-parse.
  private static final String[][] TFLDS={{},
                                         {"^"},
                                         {"^","0"},
                                         {"^","0","1"},
                                         {"^","0","1","2"}};
  public static TypeStruct make_tuple( Type... ts ) { return make(TFLDS[ts.length],ts,ffnls(ts.length)); }
  public static TypeStruct make_tuple_open( Type... ts ) { return make(false,TFLDS[ts.length],ts,ffnls(ts.length),true); }
  public static TypeStruct make_tuple(Type t1) { return make_tuple(ts(NO_DISP,t1)); }
  public static TypeStruct open(Type tdisp) { return make(false,TFLDS[1],ts(tdisp),ffnls(1),true); }
  public TypeStruct close() { assert _open; return malloc(_name,_any,_flds,_ts,_flags,false).hashcons_free(); } // Mark as no-more-fields

  public  static TypeStruct make(String[] flds, byte[] flags) { return make(flds,ts(flds.length),flags); }
  // Make from prior, just updating field types
  public TypeStruct make_from( Type[] ts ) { return make_from(_any,ts,_flags); }
  public TypeStruct make_from( boolean any, Type[] ts ) { return make_from(any,ts,_flags); }
  public TypeStruct make_from( boolean any, Type[] ts, byte[] bs ) { return malloc(_name,any,_flds,ts,bs,_open).hashcons_free(); }
  // Make a TS with a name
  public TypeStruct make_from( String name ) { return malloc(name,_any,_flds,_ts,_flags,_open).hashcons_free();  }

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

  public  static final TypeStruct ANYSTRUCT = malloc("",true ,new String[0],TypeAry.get(0),fbots(0),false).hashcons_free();
  public  static final TypeStruct ALLSTRUCT = malloc("",false,new String[0],TypeAry.get(0),fbots(0),true ).hashcons_free();
  // The display is a self-recursive structure: slot 0 is a ptr to a Display.
  // To break class-init cycle, this is partially made here, now.
  // Then we touch TypeMemPtr, which uses this field.
  // Then we finish making DISPLAY.
  public static final TypeStruct DISPLAY = malloc("",false,new String[]{"^"},ts(NIL),ffnls(1),true);
  static {
    DISPLAY._hash = DISPLAY.compute_hash();
    Type dummy = TypeMemPtr.STRPTR; // Force TypeMemPtr
    assert DISPLAY._ts[0] == Type.NIL;
    DISPLAY._ts = ts(TypeMemPtr.DISPLAY_PTR);
    DISPLAY.install_cyclic(new Ary<>(ts(DISPLAY ,TypeMemPtr.DISPLAY_PTR)));
    assert DISPLAY.is_display();
  }
  public static TypeMemPtr NO_DISP = TypeMemPtr.NO_DISP;
  @Override boolean is_display() {
    return
      this==DISPLAY || this==DISPLAY._dual ||
      (_ts.length >= 1 && _ts[0].is_display_ptr() && Util.eq(_flds[0],"^"));
  }

  public  static final TypeStruct NO_ARGS    = make_args(TFLDS[1],ts(NO_DISP));
  public  static final TypeStruct INT64      = make_args(ARGS_X ,ts(NO_DISP,TypeInt.INT64)); // {int->flt}
  public  static final TypeStruct FLT64      = make_args(ARGS_X ,ts(NO_DISP,TypeFlt.FLT64)); // {flt->flt}
  public  static final TypeStruct STRPTR     = make_args(ARGS_X ,ts(NO_DISP,TypeMemPtr.STRPTR));
  public  static final TypeStruct INT64_INT64= make_args(ARGS_XY,ts(NO_DISP,TypeInt.INT64,TypeInt.INT64)); // {int int->int }
  public  static final TypeStruct FLT64_FLT64= make_args(ARGS_XY,ts(NO_DISP,TypeFlt.FLT64,TypeFlt.FLT64)); // {flt flt->flt }
  public  static final TypeStruct OOP_OOP    = make_args(ARGS_XY,ts(NO_DISP,TypeMemPtr.USE0,TypeMemPtr.USE0));
  public  static final TypeStruct SCALAR1    = make_args(ARGS_X ,ts(NO_DISP,SCALAR));

  // A bunch of types for tests
  public  static final TypeStruct NAMEPT= make("Point:",flds("^","x","y"),ts(NO_DISP,TypeFlt.FLT64,TypeFlt.FLT64),ffnls(3));
  public  static final TypeStruct POINT = make(flds("^","x","y"),ts(NO_DISP,TypeFlt.FLT64,TypeFlt.FLT64));
          static final TypeStruct TFLT64= make(flds("^","."),ts(NO_DISP,TypeFlt.FLT64 )); //  (  flt)
  public  static final TypeStruct A     = make(flds("^","a"),ts(NO_DISP,TypeFlt.FLT64 ));
  private static final TypeStruct C0    = make(flds("^","c"),ts(NO_DISP,TypeInt.FALSE )); // @{c:0}
  private static final TypeStruct D1    = make(flds("^","d"),ts(NO_DISP,TypeInt.TRUE  )); // @{d:1}
          static final TypeStruct ARW   = make(flds("^","a"),ts(NO_DISP,TypeFlt.FLT64),new byte[]{FRW,FRW});

  static final TypeStruct[] TYPES = new TypeStruct[]{ALLSTRUCT,STRPTR,FLT64,POINT,NAMEPT,A,C0,D1,ARW,DISPLAY,INT64_INT64,ANYSTRUCT};

  // Extend the current struct with a new named field
  public TypeStruct add_fld( String name, byte mutable ) { return add_fld(name,mutable,Type.SCALAR); }
  public TypeStruct add_fld( String name, byte mutable, Type tfld ) {
    assert name==null || fldBot(name) || find(name)==-1;
    assert !_any && _open;

    Type  []   ts = TypeAry.copyOf(_ts   ,_ts   .length+1);
    String[] flds = Arrays .copyOf(_flds ,_flds .length+1);
    byte[]  flags = Arrays .copyOf(_flags,_flags.length+1);
    ts   [_ts.length] = tfld;
    flds [_ts.length] = name==null ? fldBot() : name;
    flags(flags,_ts.length, make_flag(mutable));
    return make(_any,flds,ts,flags,true);
  }
  public TypeStruct set_fld( int idx, Type t, byte ff ) {
    Type[] ts  = _ts;
    byte[] ffs = _flags;
    if( ts  [idx] != t  ) ( ts = TypeAry.clone(_ts))[idx] = t;
    if( fmod(idx) != ff ) flags(ffs= _flags .clone(),idx,set_fmod(_flags[idx],ff));
    return make_from(_any,ts,ffs);
  }

  // Make a type-variable with no definition - it is assumed to be a
  // forward-reference, to be resolved before the end of parsing.
  public static Type make_forward_def_type(String tok) {
    return make((tok+":").intern(),flds("$fref"),ts(SCALAR),fbots(1),true);
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
        if( st instanceof TypeStruct )
          ((TypeStruct)st)._cyclic = ((TypeStruct)st)._dual._cyclic = true;
        st._hash = st._dual._hash = 0; // Clear.  Cannot compute until all children found/cycles walked.
      }
    } else {
      if( t instanceof TypeMemPtr || t instanceof TypeFunPtr || t instanceof TypeStruct ) {
        stack.push(t);              // Push on stack, in case a cycle is found
        if( t instanceof TypeMemPtr ) {
          rehash_cyclic(stack,((TypeMemPtr)t)._obj);
        } else if( t instanceof TypeFunPtr ) {
          rehash_cyclic(stack,((TypeFunPtr)t)._disp);
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
    for( int i=0; i<bs.length; i++ ) flags(bs,i,fdual(_flags[i]));
    ts = TypeAry.hash_cons(ts);
    return new TypeStruct(_name,!_any,as,ts,bs,!_open);
  }

  // Recursive dual
  @Override TypeStruct rdual() {
    if( _dual != null ) return _dual;
    String[] as = new String[_flds.length];
    Type  [] ts = TypeAry.get(_ts.length);
    byte  [] bs = new byte  [_ts  .length];
    for( int i=0; i<as.length; i++ ) as[i]=sdual(_flds[i]);
    for( int i=0; i<bs.length; i++ ) flags(bs,i,fdual(_flags[i]));
    TypeStruct dual = _dual = new TypeStruct(_name,!_any,as,ts,bs,!_open);
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
    case TLIVE:
    case TSTR:   return OBJ;
    case TOBJ:   return t.above_center() ? this : t;
    case TFUNSIG:
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
      as[i] = smeet(_flds   [i],     tmax._flds  [i]);
      ts[i] =       _ts     [i].meet(tmax._ts    [i]); // Recursive not cyclic
      flags(bs,i,fmeet(flags(i),     tmax.flags  (i)));
    }
    // Elements only in the longer tuple; the short struct must be high and so
    // is effectively infinitely extended with high fields.
    for( int i=_ts.length; i<len; i++ ) {
      as[i] = tmax._flds   [i];
      ts[i] = tmax._ts     [i];
      flags(bs,i,tmax.flags(i));
    }
    // Ignore name in the non-recursive meet, it will be computed by the outer
    // 'meet' call anyways.
    return malloc("",_any&tmax._any,as,ts,bs,_open|tmax._open).hashcons_free();
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
    if( mt._any  && !mx._any ) mt._any =false;
    if(!mt._open &&  mx._open) mt._open=true ;
    for( int i=0; i<len; i++ ) {
      String s0 = mt._flds[i];
      String s1 = i<mx._flds.length ? mx._flds[i] : null;
      mt._flds  [i] = smeet(s0,s1); // Set the Meet of field names
      short b0 = mt.flags(i);
      short b1 = i<mx._flags.length ? mx.flags(i) : top_flag;
      mt.flags(i,fmeet(b0,b1)); // Set the Meet of field access
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
      mt._ts[i] = mts;          // Finally update
    }
    // Check for repeats right now
    for( TypeStruct ts : MEETS0.values() )
      if( ts!=mt && ts.equals(mt) )
        { mt = ts; break; } // Union together

    // Lower recursive-meet flag.  At this point the Meet 'mt' is still
    // speculative and not interned.
    if( --RECURSIVE_MEET > 0 )
      return mt;                // And, if not yet done, just exit with it

    // Remove any final UF before installation.
    // Do not install until the cycle is complete.
    RECURSIVE_MEET++;
    mt = shrink(mt.reachable(),mt);
    Ary<Type> reaches = mt.reachable(); // Recompute reaches after shrink
    assert check_uf(reaches);
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
    TypeStruct tstr = malloc(_name,_any,_flds.clone(),ts,_flags.clone(),_open);
    tstr._cyclic = true;
    return tstr;
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

  private static TypeMemPtr ax_impl_ptr( int alias, int cutoff, Ary<TypeStruct> cutoffs, int d, TypeStruct dold, TypeMemPtr old ) {
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
    nmp._disp = ax_impl_ptr(alias,cutoff,cutoffs,d,dold,old._disp);
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
      nptr._disp = (TypeMemPtr)ax_meet(bs,nptr._disp,optr._disp);
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
      nts._any &= ots._any ; 
      nts._open|= ots._open;
      for( int i=0; i<clen; i++ ) {
        nts._flds [i] = smeet(nts._flds[i],ots._flds[i]); // Set the Meet of field names
        nts.flags(i,    fmeet(nts.flags(i),ots.flags(i)));
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
  static TypeStruct shrink( Ary<Type> reaches, TypeStruct tstart ) {
    assert DUPS.isEmpty();
    // Structs never change their hash based on field types.  Set their hash first.
    for( int i=0; i<reaches._len; i++ ) {
      Type t = reaches.at(i);
      if( t instanceof TypeStruct )
        t._hash = t.compute_hash();
    }
    // TMPs depend on Structs
    for( int i=0; i<reaches._len; i++ ) {
      Type t = reaches.at(i);
      if( t instanceof TypeMemPtr )
        t._hash = t.compute_hash();
    }
    // TFPs depend on TMPS for display
    for( int i=0; i<reaches._len; i++ ) {
      Type t = reaches.at(i);
      if( t instanceof TypeFunPtr )
        t._hash = t.compute_hash();
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
          TypeMemPtr t6 = tfptr._disp;
          TypeMemPtr t7 = ufind(t6);
          if( t6 != t7 ) {
            tfptr._disp = t7;
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
      case TFUNPTR:  push(work, keep, ((TypeFunPtr)t)._disp); break;
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
    case TFUNPTR: get_cyclic(bcs,bs,stack,((TypeFunPtr)t)._disp); break;
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
      }
      t._dual=null;             // Remove any duals, so re-inserted clean
    }
  }

  // If unequal length; then if short is low it "wins" (result is short) else
  // short is high and it "loses" (result is long).
  private int len( TypeStruct tt ) { return _ts.length <= tt._ts.length ? len0(tt) : tt.len0(this); }
  private int len0( TypeStruct tmax ) { return _any ? tmax._ts.length : _ts.length; }


  // ------ String field name lattice ------
  static private boolean fldTop( String s ) { return s.charAt(0)=='\\'; }
  static public  boolean fldBot( String s ) { return s.charAt(0)=='.'; }
  static public  String fldTop( ) { return "\\"; }
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

  // ------ Utilities -------
  // Return the index of the matching field (or nth tuple), or -1 if not found
  // or field-num out-of-bounds.
  public int find( String fld ) {
    for( int i=0; i<_flds.length; i++ )
      if( Util.eq(_flds[i],fld) )
        return i;
    return -1;
  }

  public Type at( int idx ) { return _ts[idx]; }
  public Type last() { return _ts[_ts.length-1]; }

  // Update (approximately) the current TypeObj.  Updates the named field.
  @Override public TypeObj update(byte fin, String fld, Type val) { return update(fin,fld,val,false); }
  @Override public TypeObj st    (byte fin, String fld, Type val) { return update(fin,fld,val,true ); }
  private TypeObj update(byte fin, String fld, Type val, boolean precise) {
    int idx = find(fld);
    if( idx == -1 )             // Unknown field, assume changes no fields
      return this;
    // Pointers & Memory to a Store can fall during GCP, and go from r/w to r/o
    // and the StoreNode output must remain monotonic.  This means store
    // updates are allowed to proceed even if in-error.
    byte[] flags = _flags.clone();
    Type[] ts    = TypeAry.clone(_ts);
    _update(flags,ts,fin,idx,val,precise);
    return malloc(_name,_any,_flds,ts,flags,_open).hashcons_free();
  }
  private static void _update( byte[] flags, Type[] ts, byte fin, int idx, Type val, boolean precise ) {
    short flag = flags(flags,idx);
    if( fmod(flag)==FFNL ) {val=val.widen(); precise=false; }// Illegal store into final field
    ts[idx] =  precise ? val : ts[idx].meet(val);
    byte mod = precise ? fin : fmod(fmeet(flag,make_flag(fin)));
    flags(flags,idx,set_fmod(flags(flags,idx),mod));
  }

  // Allowed to update this field?
  public boolean can_update(int idx) { return fmod(idx) == FRW; }

  // Widen (lose info), to make it suitable as the default function memory.
  // Final fields can remain as-is; non-finals are all widened to ALL (assuming
  // a future error Store); field flags set to bottom; the field names are kept.
  @Override public TypeStruct crush() {
    if( _any ) return this;     // No crush on high structs
    Type[] ts = TypeAry.clone(_ts);
    byte[] flags = _flags.clone();
    for( int i=0; i<ts.length; i++ )
      if( fmod(i)!=FFNL && fmod(i)!=fdual(FFNL) ) { ts[i]=ALL; flags[i]=FFNL; }// Widen non-finals to ALL, as-if crushed by errors
      else { ts[i]=ts[i].simple_ptr(); flags[i]=_flags[i]; }
    // Keep the name and field names.
    // Low input so low output.
    // Currently must keep _open==true to pass monotonicity
    return malloc(_name,false,_flds,ts,flags,true).hashcons_free();
  }

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

  // Shallow clone
  TypeStruct sharpen_clone() {
    assert interned();
    Type[] ts = TypeAry.clone(_ts);
    TypeStruct t = malloc(_name,_any,_flds,ts,_flags,_open);
    t._hash = t.compute_hash();
    return t;
  }

}
