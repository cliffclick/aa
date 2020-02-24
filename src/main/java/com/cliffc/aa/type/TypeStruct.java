package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.*;
import org.jetbrains.annotations.NotNull;

import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.function.Predicate;

/** A memory-based Tuple with optionally named fields.  This is a recursive
 *  type, only produced by NewNode and structure or tuple constants.  Fields
 *  can be indexed by field name or numeric constant (i.e. tuples), but NOT by
 *  a general number - thats an Array.  Field access mods make a small lattice
 *  of: {choice,r/w,final,r-o}.  Note that mixing r/w and final moves to r-o and
 *  loses the final property.
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
  public Type[] _ts;            // Matching field types
  public byte[] _finals;        // Fields that are final; see fmeet, fdual, fstr
  public boolean _cln;          // Clean: not modified since last function
  private TypeStruct _uf;       // Tarjan Union-Find, used during cyclic meet
  private TypeStruct     ( String name, boolean any, boolean cln, String[] flds, Type[] ts, byte[] finals) { super(TSTRUCT, name, any); init(name, any,cln, flds,ts,finals); }
  private TypeStruct init( String name, boolean any, boolean cln, String[] flds, Type[] ts, byte[] finals) {
    super.init(TSTRUCT, name, any);
    _cln   = cln;
    _flds  = flds;
    _ts    = ts;
    _finals= finals;
    _uf    = null;
    return this;
  }
  // Precomputed hash code.  Note that it can NOT depend on the field types -
  // because during recursive construction the types are not available.
  @Override int compute_hash() {
    int hash = super.compute_hash() + (_cln?1001:0), hash1=hash;
    for( int i=0; i<_flds.length; i++ ) hash = ((hash<<_finals[i])*_flds[i].hashCode())|(hash>>17);
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
    if( !super.equals(t) || _cln != t._cln ) return 0;
    if( _ts.length != t._ts.length ) return 0;
    if( _ts == t._ts && _flds == t._flds && _finals == t._finals ) return 1;
    for( int i=0; i<_ts.length; i++ )
      if( !Util.eq(_flds[i],t._flds[i]) || _finals[i]!=t._finals[i] )
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
    CYCLES.remove(len);
    CYCLES.remove(len);
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
  String str( VBitSet dups) {
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return "$"; // Break recursive printing cycle
    if( find("!") != -1 && find("math_pi") != -1 )
      return "{PRIMS}";         // Special shortcut for the all-prims closure type

    SB sb = new SB();
    if( _uf!=null ) return "=>"+_uf; // Only used mid-recursion
    if( _any ) sb.p('~');
    sb.p(_name);
    boolean is_tup = _flds.length==0 || fldTop(_flds[0]) || fldBot(_flds[0]) || isDigit(_flds[0].charAt(0));
    sb.p(is_tup ? "(" : "@{");
    for( int i=0; i<_flds.length; i++ ) {
      if( !is_tup )
        sb.p(_flds[i]).p(fstr(_finals[i])).p('='); // Field name, access mod
      Type t = at(i);
      if( t==null ) sb.p("!");  // Graceful with broken types
      else if( t==SCALAR ) ;    // Default answer, do not print
      //else if( t instanceof TypeMemPtr ) sb.p("*"+((TypeMemPtr)t)._aliases); // Do not recurse here, gets too big too fast
      else sb.p(t.str(dups));   // Recursively print field type
      if( i<_flds.length-1 ) sb.p(';');
    }
    sb.p(!is_tup ? "}" : ")");
    return sb.p(_cln ?"":"!").toString();
  }
  @Override SB dstr( SB sb, VBitSet dups ) {
    sb.p('_').p(_uid);
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return sb.p('$'); // Break recursive printing cycle
    if( find("!") != -1 && find("math_pi") != -1 )
      return sb.p("{PRIMS}");

    if( _uf!=null ) return _uf.dstr(sb.p("=>"),dups);
    if( _any ) sb.p('~');
    sb.p(_name);
    boolean is_tup = _flds.length==0 || fldTop(_flds[0]) || fldBot(_flds[0]) || isDigit(_flds[0].charAt(0));
    if( !is_tup ) sb.p('@');    // Not a tuple
    sb.p(is_tup ? '(' : '{').nl().ii(1); // open struct, newline, increase_indent
    for( int i=0; i<_flds.length; i++ ) {
      sb.i();                   // indent, 1 field per line
      Type t = at(i);
      if( !is_tup )
        sb.p(_flds[i]).p(fstr(_finals[i])).p('='); // Field name, access mod
      if( t==null ) sb.p("!");  // Graceful with broken types
      else if( t==SCALAR ) ;    // Default answer, do not print
      else t.dstr(sb,dups);     // Recursively print field type
      if( i<_flds.length-1 ) sb.p(';');
      sb.nl();                  // one field per line
    }
    return sb.di(1).i().p(!is_tup ? '}' : ')').p(_cln ?"":"!");
  }
  // Print with memory instead of recursion
  @Override public SB str(SB sb, VBitSet dups, TypeMem mem) {
    if( dups == null ) dups = new VBitSet();
    if( dups.tset(_uid) ) return sb.p('$'); // Break recursive printing cycle
    if( find("!") != -1 && find("math_pi") != -1 )
      return sb.p("{PRIMS}");
    if( _uf!=null ) return _uf.str(sb.p("=>"),dups,mem);
    if( _any ) sb.p('~');
    sb.p(_name);
    boolean is_tup = _flds.length==0 || fldTop(_flds[0]) || fldBot(_flds[0]) || isDigit(_flds[0].charAt(0));
    if( !is_tup ) sb.p('@');    // Not a tuple
    sb.p(is_tup ? '(' : '{');
    for( int i=0; i<_flds.length; i++ ) {
      Type t = at(i);
      if( !is_tup )
        sb.p(_flds[i]).p(fstr(_finals[i])).p('='); // Field name, access mod
      if( t==null ) sb.p("!");  // Graceful with broken types
      else if( t==SCALAR ) ;    // Default answer, do not print
      else t.str(sb,dups,mem);  // Recursively print field type
      if( i<_flds.length-1 ) sb.p(';');
    }
    return sb.p(!is_tup ? '}' : ')').p(_cln ?"":"!");
  }

  // Unlike other types, TypeStruct never makes dups - instead it might make
  // cyclic types for which a DAG-like bottom-up-remove-dups approach cannot work.
  private static TypeStruct FREE=null;
  @Override protected TypeStruct free( TypeStruct ret ) { FREE=this; return ret; }
  static TypeStruct malloc( String name, boolean any, boolean cln, String[] flds, Type[] ts, byte[] finals ) {
    assert check_name(name);
    if( FREE == null ) return new TypeStruct(name, any,cln,flds,ts,finals);
    TypeStruct t1 = FREE;  FREE = null;
    return t1.init(name, any,cln,flds,ts,finals);
  }
  private TypeStruct hashcons_free() {
    _ts = TypeAry.hash_cons(_ts);
    TypeStruct t2 = (TypeStruct)hashcons();
    return this==t2 ? this : free(t2);
  }

  // Default tuple field names - all bottom-field names
  private static final String[] FLD0={};
  private static final String[] FLD1={"."};
  private static final String[] FLD2={".","."};
  private static final String[] FLD3={".",".","."};
  private static final String[][] FLDS={FLD0,FLD1,FLD2,FLD3};
  public  static String[] FLDS( int len ) { return FLDS[len]; }
  private static String[] flds(String... fs) { return fs; }
  public  static final String[] ARGS_X  = flds("^","x");
  public  static final String[] ARGS_XY = flds("^","x","y");
  public  static Type[] ts() { return TypeAry.get(0); }
  public  static Type[] ts(Type t0) { Type[] ts = TypeAry.get(1); ts[0]=t0; return ts;}
  public  static Type[] ts(Type t0, Type t1) { Type[] ts = TypeAry.get(2); ts[0]=t0; ts[1]=t1; return ts;}
  public  static Type[] ts(Type t0, Type t1, Type t2) { Type[] ts = TypeAry.get(3); ts[0]=t0; ts[1]=t1; ts[2]=t2; return ts;}
  public  static Type[] ts(int n) { Type[] ts = TypeAry.get(n); Arrays.fill(ts,SCALAR); return ts; } // All Scalar fields
  public  static byte[] fbots (int n) { byte[] bs = new byte[n]; Arrays.fill(bs,fbot  ()); return bs; }
  public  static byte[] finals(int n) { byte[] bs = new byte[n]; Arrays.fill(bs,ffinal()); return bs; } // All read-only
  public  static byte[] frws  (int n) { byte[] bs = new byte[n]; Arrays.fill(bs,frw   ()); return bs; } // All read-write

  public  static TypeStruct make(Type[] ts) {
    return malloc("",false,false,FLDS[ts.length],ts,fbots(ts.length)).hashcons_free();
  }
  // Generic function arguments.  Slot 0 is the closure and has a fixed name.
  public  static TypeStruct make_args(Type[] ts) {
    assert ts[0]==TypeMemPtr.CLOSURE_PTR || ts[0]==Type.NIL;
    String[] args = new String[ts.length];
    Arrays.fill(args,".");
    args[0] = "^";
    return malloc("",false,false,args,ts,fbots(ts.length)).hashcons_free();
  }
  public  static TypeStruct make(Type t0         ) { return make(ts(t0   )); }
  public  static TypeStruct make(Type t0, Type t1) { return make(ts(t0,t1)); }
  public  static TypeStruct make(String[] flds, Type[] ts) { return malloc("",false,false,flds,ts,fbots(ts.length)).hashcons_free(); }
  public  static TypeStruct make(String[] flds, Type[] ts, byte[] finals) { return malloc("",false,false,flds,ts,finals).hashcons_free(); }
  public  static TypeStruct make(String name, String[] flds, Type[] ts, byte[] finals) { return malloc(name,false,false,flds,ts,finals).hashcons_free(); }

  private static final String[][] TFLDS={{},
                                         {"^"},
                                         {"^","0"},
                                         {"^","0","1"},
                                         {"^","0","1","2"}};
  public  static String[] TFLDS( int len ) { return TFLDS[len]; }
  public  static TypeStruct make_tuple( Type... ts ) { return make(TFLDS[ts.length],ts,finals(ts.length)); }
  public  static TypeStruct make(String[] flds, byte[] finals) { return make(flds,ts(flds.length),finals); }

  // If has lattice-bottom field-mods (i.e. read-only), make a highest-possible
  // struct except for the field mods.  This struct is suitable for doing a
  // meet and only dropping the fields to field-bot.
  public TypeStruct make_fmod_bot() { return has_fmod_bot()? make(_dual._flds, _dual._ts, _finals) : null; }
  private boolean has_fmod_bot() {
    for( byte b : _finals ) if( b==fbot() ) return true;
    return false;
  }

  // The display is a self-recursive structure: slot 0 is a ptr to a Display.
  public  static final TypeStruct CLOSURE = malloc("",false,false,new String[]{"^"},ts(Type.NIL),finals(1));
  static { CLOSURE._hash = CLOSURE.compute_hash(); }
  // Most primitive function call argument type lists are 0-based
  public  static final TypeStruct GENERIC = malloc("",true,true,FLD0,TypeAry.get(0),new byte[0]).hashcons_free();
  public  static final TypeStruct ALLSTRUCT = make(ts());
  public  static final TypeStruct ALLSTRUCT_CLN = malloc("",false,true,FLDS[0],TypeAry.get(0),fbots(0)).hashcons_free();
  public  static final TypeStruct SCALAR0     = make_args   (ts(Type.NIL));
  public  static final TypeStruct SCALAR1     = make(ARGS_X ,ts(Type.NIL,SCALAR));
  public  static final TypeStruct SCALAR2     = make(ARGS_XY,ts(Type.NIL,SCALAR,SCALAR));
  public  static final TypeStruct STRPTR      = make(ARGS_X ,ts(Type.NIL,TypeMemPtr.STRPTR));
  public  static final TypeStruct OOP_OOP     = make(ARGS_XY,ts(Type.NIL,TypeMemPtr.OOP0,TypeMemPtr.OOP0));
  public  static final TypeStruct INT64_INT64 = make(ARGS_XY,ts(Type.NIL,TypeInt.INT64,TypeInt.INT64));
  public  static final TypeStruct FLT64_FLT64 = make(ARGS_XY,ts(Type.NIL,TypeFlt.FLT64,TypeFlt.FLT64));
  public  static final TypeStruct STR_STR     = make(ARGS_XY,ts(Type.NIL,TypeMemPtr.STRPTR,TypeMemPtr.STRPTR));
  public  static final TypeStruct FLT64       = make(ARGS_X ,ts(Type.NIL,TypeFlt.FLT64)); // @{x:flt}
  public  static final TypeStruct INT64       = make(ARGS_X ,ts(Type.NIL,TypeInt.INT64)); // @{x:int}

  // A bunch of types for tests
  public  static final TypeStruct NAMEPT= make("Point:",ARGS_XY,ts(Type.NIL,TypeFlt.FLT64,TypeFlt.FLT64),finals(3));
  public  static final TypeStruct POINT = make(ARGS_XY,ts(Type.NIL,TypeFlt.FLT64,TypeFlt.FLT64));
          static final TypeStruct TFLT64= make(          ts(TypeFlt.FLT64 )); //  (  flt)
  public  static final TypeStruct A     = make(flds("^","a"),ts(Type.NIL,TypeFlt.FLT64 ));
  private static final TypeStruct C0    = make(flds("^","c"),ts(Type.NIL,TypeInt.FALSE )); // @{c:0}
  private static final TypeStruct D1    = make(flds("^","d"),ts(Type.NIL,TypeInt.TRUE  )); // @{d:1}
  private static final TypeStruct ARW   = make(flds("^","a"),ts(Type.NIL,TypeFlt.FLT64),new byte[]{frw(),frw()});

  // Called during init to break the cycle making CLOSURE
  public static void init1() {
    if( CLOSURE._ts[0] == Type.NIL ) {
      CLOSURE._ts = ts(TypeMemPtr.CLOSURE_PTR);
      CLOSURE.install_cyclic(new Ary<>(ts(CLOSURE,TypeMemPtr.CLOSURE_PTR)));
    }
    assert CLOSURE.is_closure();
  }
  boolean is_closure() {
    if( this==CLOSURE || this==CLOSURE._dual ) return true;
    return _ts.length >= 1 && _ts[0] instanceof TypeMemPtr && ((TypeMemPtr)_ts[0]).is_closure();
  }

  static final TypeStruct[] TYPES = new TypeStruct[]{ALLSTRUCT,STR_STR,FLT64,POINT,NAMEPT,A,C0,D1,ARW,CLOSURE};

  // Extend the current struct with a new named field
  public TypeStruct add_fld( String name, Type t, byte mutable ) {
    assert t.isa(SCALAR) && (name==null || fldBot(name) || find(name)==-1);

    Type  []   ts = Arrays.copyOfRange(_ts    ,0,_ts    .length+1);
    String[] flds = Arrays.copyOfRange(_flds  ,0,_flds  .length+1);
    byte[] finals = Arrays.copyOfRange(_finals,0,_finals.length+1);
    ts    [_ts.length] = t;
    flds  [_ts.length] = name==null ? "." : name;
    finals[_ts.length] = mutable;
    return make(flds,ts,finals);
  }
  public TypeStruct set_fld( int idx, Type t, byte ff ) {
    Type[] ts = TypeAry.clone(_ts);
    ts[idx] = t;
    byte[] ffs = _finals;
    if( _finals[idx] != ff )
      (ffs = _finals.clone())[idx]=ff;
    return make(_flds,ts,ffs);
  }
  public TypeStruct del_fld( int idx ) {
    Type[] ts = TypeAry.get(_ts.length-1);
    for( int i=0; i<idx; i++ ) ts[i] = _ts[i];
    for( int i=idx; i<ts.length; i++ ) ts[i] = _ts[i+1];
    String[] flds = new String[_flds.length-1];
    for( int i=0; i<idx; i++ ) flds[i] = _flds[i];
    for( int i=idx; i<flds.length; i++ ) flds[i] = _flds[i+1];
    byte[] finals = new byte[_finals.length-1];
    for( int i=0; i<idx; i++ ) finals[i] = _finals[i];
    for( int i=idx; i<finals.length; i++ ) finals[i] = _finals[i+1];
    return make(flds,ts,finals);
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
    assert has_name() && _flds[0]=="$fref";
    // Remove from INTERN table, since hacking type will not match hash
    untern()._dual.untern();
    ts.untern().dual().untern();
    // Hack type and it's dual.  Type is now recursive.
    _flds  = ts._flds  ; _dual._flds  = ts._dual._flds  ;
    _ts    = ts._ts    ; _dual._ts    = ts._dual._ts    ;
    _finals= ts._finals; _dual._finals= ts._dual._finals;
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
        assert st._type==TMEMPTR || st._type == TSTRUCT;
        st.untern()._dual.untern(); // Wrong hash
        st._cyclic = st._dual._cyclic = true;
        st._hash = st._dual._hash = 0; // Clear.  Cannot compute until all children found/cycles walked.
      }
    } else {
      if( t instanceof TypeMemPtr || t instanceof TypeStruct ) {
        stack.push(t);              // Push on stack, in case a cycle is found
        if( t instanceof TypeMemPtr )             rehash_cyclic(stack,((TypeMemPtr)t)._obj);
        else for( Type tf : ((TypeStruct)t)._ts ) rehash_cyclic(stack, tf                 );
        if( t._hash==0 ) {    // If part of a cycle, hash was cleared.  Rehash.
          assert t._cyclic && t._dual._cyclic;
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
    for( int i=0; i<bs.length; i++ ) bs[i] = fdual(_finals[i]);
    ts = TypeAry.hash_cons(ts);
    return new TypeStruct(_name,!_any,!_cln,as,ts,bs);
  }

  // Recursive dual
  @Override TypeStruct rdual() {
    if( _dual != null ) return _dual;
    String[] as = new String[_flds.length];
    Type  [] ts = TypeAry.get(_ts.length);
    byte  [] bs = new byte  [_ts  .length];
    for( int i=0; i<as.length; i++ ) as[i]=sdual(_flds[i]);
    for( int i=0; i<bs.length; i++ ) bs[i]=fdual(_finals[i]);
    TypeStruct dual = _dual = new TypeStruct(_name,!_any,!_cln,as,ts,bs);
    assert _hash == compute_hash();
    dual._hash = dual.compute_hash(); // Compute hash before recursion
    for( int i=0; i<ts.length; i++ ) ts[i] = _ts[i].rdual();
    dual._ts = TypeAry.hash_cons(ts); // hashcons cyclic arrays
    dual._dual = this;
    dual._cyclic = _cyclic;
    return dual;
  }

  // Recursive meet in progress
  private static final HashMap<TypeStruct,TypeStruct> MEETS1 = new HashMap<>(), MEETS2 = new HashMap<>();

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
    case TNIL:
    case TTUPLE :
    case TFUNPTR:
    case TMEMPTR:
    case TRPC:
    case TFUN:
    case TMEM:   return ALL;
    default: throw typerr(t);   // All else should not happen
    }
    TypeStruct thsi = this;
    TypeStruct that = (TypeStruct)t;
    // INVARIANT: Both this and that are prior existing & interned.
    assert RECURSIVE_MEET > 0 || (thsi.interned() && that.interned());
    // INVARIANT: Both MEETS are empty at the start.  Nothing involved in a
    // potential cycle is interned until the Meet completes.
    assert RECURSIVE_MEET > 0 || (MEETS1.isEmpty() && MEETS2.isEmpty());

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
      bs[i] = fmeet(_finals[i],     tmax._finals[i]);
    }
    // Elements only in the longer tuple
    for( int i=_ts.length; i<len; i++ ) {
      as[i] = tmax._flds  [i];
      ts[i] = tmax._ts    [i];
      bs[i] = tmax._finals[i];
    }
    // Ignore name in the non-recursive meet, it will be computed by the outer
    // 'meet' call anyways.
    return malloc("",_any&tmax._any, _cln &tmax._cln,as,ts,bs).hashcons_free();
  }

  // Both structures are cyclic.  The meet will be "as if" both structures are
  // infinitely unrolled, Meeted, and then re-rolled.  If cycles are of uneven
  // length, the end result will be the cyclic GCD length.
  private TypeStruct cyclic_meet( TypeStruct that ) {
    // Walk 'this' and 'that' and map them both (via MEETS1 and MEETS2) to a
    // shared common Meet result.  Only walk the cyclic parts... cyclically.
    // When visiting a finite-sized part we use the normal recursive Meet.
    // When doing the cyclic part, we use the normal Meet except we need to use
    // the mapped Meet types.  As part of these Meet operations we can end up
    // Meeting Meet types with each other more than once, or more than once
    // from each side - which means already visited Types might need to Meet
    // again, even as they are embedded in other Types - which leads to the
    // need to use Tarjan U-F to union Types on the fly.

    // There are 4 choices here: this, that the existing MEETs from either
    // side.  U-F all choices together.  Some or all may be missing and can
    // be assumed equal to the final MEET.
    TypeStruct lf = MEETS1.get(this);
    TypeStruct rt = MEETS2.get(that);
    if( lf != null ) { lf = lf.ufind(); assert lf._cyclic && !lf.interned(); }
    if( rt != null ) { rt = rt.ufind(); assert rt._cyclic && !rt.interned(); }
    if( lf == rt && lf != null ) return lf; // Cycle has been closed

    // Take for the starting point MEET either already-mapped type.  If neither
    // is mapped, clone one (to make a new space to put new types into) and
    // simply point at the other - it will only be used for the len() and _any
    // fields.  If both are mapped, union together and pick one arbitrarily
    // (here always picked left).
    TypeStruct mt, mx;
    if( lf == null ) {
      if( rt == null ) { mt = this.shallow_clone(); mx = that; }
      else             { mt = rt;                   mx = this; }
    } else {
      if( rt == null ) { mt = lf;                   mx = that; }
      else             { mt = lf;  rt.union(lf);    mx = rt  ; }
    }
    MEETS1.put(this,mt);
    MEETS2.put(that,mt);

    // Do a shallow MEET: meet of field names and _any and _ts sizes - all
    // things that can be computed without the cycle.  _ts not filled in yet.
    int len = mt.len(mx); // Length depends on all the Structs Meet'ing here
    if( len != mt._ts.length ) {
      mt._flds  = Arrays.copyOf(mt._flds  , len);
      mt._ts    = Arrays.copyOf(mt._ts    , len);
      mt._finals= Arrays.copyOf(mt._finals, len);
    }
    if( mt._any && !mx._any ) mt._any=false;
    if( mt._cln && !mx._cln ) mt._cln=false;
    len = Math.min(len,mx._ts.length);
    for( int i=0; i<len; i++ ) {
      mt._flds  [i] = smeet(mt._flds  [i],mx._flds  [i]); // Set the Meet of field names
      mt._finals[i] = fmeet(mt._finals[i],mx._finals[i]); // Set the Meet of field access
    }
    mt._name = mt.mtname(mx,mt);
    mt._hash = mt.compute_hash(); // Compute hash now that fields and finals are set

    // Since the result is cyclic, we cannot test the cyclic parts for
    // pre-existence until the entire cycle is built.  We can't intern the
    // partially built parts, but we want to use the normal xmeet call - which
    // normally recursively interns.  Turn off interning with the global
    // RECURSIVE_MEET flag.
    RECURSIVE_MEET++;

    // For-all _ts edges do the Meet.  Some are not-recursive and mapped, some
    // are part of the cycle and mapped, some
    for( int i=0; i<len; i++ ) {
      Type lfi = this._ts[i];
      Type rti = that._ts[i];
      Type mti = lfi.meet(rti); // Recursively meet, can update 'mt'
      Type mtx = mt._ts[i];     // Prior value, perhaps updated recursively
      Type mts = mtx.meet(mti); // Meet again
      assert mt._uf==null;      // writing results but value is ignored
      mt._ts[i] = mts;          // Finally update
    }

    // Check for repeats right now
    for( TypeStruct ts : MEETS1.values() )
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
    UF.isEmpty();
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
    MEETS1.clear();
    MEETS2.clear();
    return old;
  }

  // Make a clone of this TypeStruct that is not interned.
  private TypeStruct shallow_clone() {
    assert _cyclic;
    Type[] ts = TypeAry.get(_ts.length);
    Arrays.fill(ts,Type.ANY);
    TypeStruct tstr = malloc(_name,_any, _cln,_flds.clone(),ts,_finals.clone());
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
    nts._flds   = old._flds  .clone();
    nts._finals = old._finals.clone();
    nts._ts     = TypeAry.clone(old._ts);
    OLD2APX.put(old,nts);
    for( int i=0; i<old._ts.length; i++ ) // Fill clone with approximation
      if( old._ts[i]._type == TMEMPTR )
        nts._ts[i] = ax_impl_ptr(alias,cutoff,cutoffs,d,dold,(TypeMemPtr)old._ts[i]);
    if( isnews && d==cutoff ) {
      while( !cutoffs.isEmpty() ) { // At depth limit, meet with cutoff to make the approximation
        Type mt = ax_meet(new BitSetSparse(), nts,cutoffs.pop());
        assert mt==nts;
      }
    }
    if( d==cutoff ) OLD2APX.put(old,null); // Do not keep sharing the "tails"
    return nts;
  }

  private static Type ax_impl_ptr( int alias, int cutoff, Ary<TypeStruct> cutoffs, int d, TypeStruct dold, TypeMemPtr old ) {
    assert old.interned();
    TypeMemPtr nt = OLD2APX.get(old);
    if( nt != null ) return ufind(nt);

    // Walk internal structure, meeting into the approximation
    TypeMemPtr nmp = (TypeMemPtr)old.clone();
    OLD2APX.put(old,nmp);
    if( old._obj instanceof TypeStruct )
      nmp._obj = ax_impl_struct(alias,nmp._aliases.test(alias),cutoff,cutoffs,d,dold,(TypeStruct)old._obj);
    if( d+1==cutoff ) OLD2APX.put(old,null); // Do not keep sharing the "tails"
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
    case TMEMPTR: {
      TypeMemPtr nptr = (TypeMemPtr)nt;
      if( old == Type.NIL ) { nptr._aliases = nptr._aliases.meet_nil();  break; }
      if( old == Type.SCALAR )
        return union(nt,old); // Result is a scalar, which changes the structure of the new types.
      if( old == Type.XSCALAR ) break; // Result is the nt unchanged
      if( !(old instanceof TypeMemPtr) ) throw AA.unimpl();
      TypeMemPtr optr = (TypeMemPtr)old;
      nptr._aliases = nptr._aliases.meet(optr._aliases);
      nptr._obj = (TypeObj)ax_meet(bs,nptr._obj,optr._obj);
      break;
    }
    case TSTRUCT:
      if( !(old instanceof TypeStruct) ) throw AA.unimpl();
      TypeStruct ots = (TypeStruct)old, nts = (TypeStruct)nt;
      assert nts._uf==null;     // Already handled by the caller
      // Compute a new target length.  Generally size is unchanged, but will
      // change if mixing structs.
      int len = ots.len(nts);     // New length
      if( len != nts._ts.length ) { // Grow/shrink as needed
        nts._flds  = Arrays.copyOf(nts._flds  , len);
        nts._ts    = Arrays.copyOf(nts._ts    , len);
        nts._finals= Arrays.copyOf(nts._finals, len);
      }
      int clen = Math.min(len,ots._ts.length);
      // Meet all the non-recursive parts
      nts._any &= ots._any;
      nts._cln &= ots._cln;
      for( int i=0; i<clen; i++ ) {
        nts._flds  [i] = smeet(nts._flds  [i],ots._flds  [i]); // Set the Meet of field names
        nts._finals[i] = fmeet(nts._finals[i],ots._finals[i]);
      }
      if( clen != len ) throw AA.unimpl();
      // Now recursively do all fields
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
        assert t instanceof TypeMemPtr;
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
          TypeObj t6 = t5;
          if( t4 != t5 ) {
            tm._obj = t5;
            progress |= post_mod(tm);
            if( !t5.interned() ) reaches.push(t5);
          }
          break;
        case TSTRUCT:           // Update all TypeStruct fields
          TypeStruct ts = (TypeStruct)t0;
          for( int i=0; i<ts._ts.length; i++ ) {
            Type tf = ts._ts[i];
            progress |= (tf != (ts._ts[i] = ufind(tf)));
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
      case TSTRUCT:  for( Type tf : ((TypeStruct)t)._ts ) push(work, keep, tf); break;
      default: break;
      }
    }
    return work;
  }
  private void push( Ary<Type> work, boolean keep, Type t ) {
    int y = t._type;
    if( (y==TMEMPTR || y==TSTRUCT) &&
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
      assert !(t instanceof TypeFunPtr); // Never part of a cycle
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
    case TSTRUCT: for( Type tf : ((TypeStruct)t)._ts ) get_cyclic(bcs,bs,stack,tf); break;
    }
    stack.pop();                // Pop, not part of anothers cycle
    return bcs;
  }
  private void mark_cyclic( BitSet bcs, Ary<Type> reaches ) {
    for( Type t : reaches ) {
      t._cyclic = bcs.get(t._uid);
      if( t instanceof TypeStruct ) {
        TypeStruct ts = (TypeStruct)t;
        ts._ts = TypeAry.hash_cons(ts._ts); // hashcons cyclic arrays
      }
    }
  }

  // If unequal length; then if short is low it "wins" (result is short) else
  // short is high and it "loses" (result is long).
  private int len( TypeStruct tt ) { return _ts.length <= tt._ts.length ? len0(tt) : tt.len0(this); }
  private int len0( TypeStruct tmax ) { return _any ? tmax._ts.length : _ts.length; }

  static private boolean fldTop( String s ) { return s.charAt(0)=='*'; }
  static public  boolean fldBot( String s ) { return s.charAt(0)=='.'; }
  // String meet
  private static String smeet( @NotNull String s0, @NotNull String s1 ) {
    if( fldTop(s0) ) return s1;
    if( fldTop(s1) ) return s0;
    if( fldBot(s0) ) return s0;
    if( fldBot(s1) ) return s1;
    if( s0.equals(s1) ) return s0;
    return "."; // fldBot
  }
  private static String sdual( String s ) {
    if( fldTop(s) ) return ".";
    if( fldBot(s) ) return "*";
    return s;
  }

  // Field modifiers make a tiny non-obvious lattice:
  //           0unknown
  //      1final     2read/write
  //          3read-only
  public  static byte fmeet( byte f0, byte f1 ) { return (byte)(f0|f1); }
  private static byte fdual( byte f ) { return f==funk() || f==fro() ? (byte)(3-f) : f; }
  // Shows as:  fld?=val, fld==val, fld:=val, fld=val
  private static String fstr( byte f ) { return new String[]{"?","=",":",""}[f]; }
  public  static String fstring( byte f ) { return new String[]{"unknown","final","read-write","read-only"}[f]; }

  public static byte ftop()  { return funk(); }
  public static byte fbot()  { return fdual(ftop()); }
  public static byte funk()  { return 0; }
  public static byte ffinal(){ return 1; }
  public static byte frw()   { return 2; }
  public static byte fro()   { return 3; }

  // Return the index of the matching field (or nth tuple), or -1 if not found
  // or field-num out-of-bounds.
  public int find( String fld ) {
    for( int i=0; i<_flds.length; i++ )
      if( fld.equals(_flds[i]) )
        return i;
    return -1;
  }

  public Type at( int idx ) { return _ts[idx]; }

  // Update (approximately) the current TypeObj.  Updates the named field.
  @Override public TypeObj update(byte fin, String fld, Type val) { return update(fin,fld,val,false); }
  @Override public TypeObj st    (byte fin, String fld, Type val) { return update(fin,fld,val,true ); }
  private TypeObj update(byte fin, String fld, Type val, boolean precise) {
    assert val.isa_scalar();
    // Pointers & Memory to a Store can fall during GCP, and go from r/w to r/o
    // and the StoreNode output must remain monotonic.  This means store
    // updates are allowed to proceed even if in-error.
    byte[] finals = _finals.clone();
    Type[] ts     = TypeAry.clone(_ts);
    int idx = find(fld);
    if( idx == -1 )             // Unknown field, might change all fields
      for( int i=0; i<_finals.length; i++ )
        _update(finals,ts,fin,i,val,precise);
    else                        // Update the one field
      _update(finals,ts,fin,idx,val,precise);
    return malloc(_name,_any,false,_flds,ts,finals).hashcons_free();
  }
  private static void _update( byte[] finals, Type[] ts, byte fin, int idx, Type val, boolean precise ) {
    if( finals[idx]==ffinal() || finals[idx]==fro() )
      precise=false;      // Illegal store into final/r-o field
    ts[idx] =  precise ? val : ts[idx].meet(val);
    finals[idx] = precise ? fin : fmeet(fin,finals[idx]);
  }

  // Allowed to update this field?
  //@Override public boolean can_update(String fld) {
  //  int idx = find(fld);
  //  return idx != -1 && can_update(idx);
  //}
  public boolean can_update(int idx) { return _finals[idx] == frw() || _finals[idx] == funk(); }

  // Identical struct but clean.  Complicated because has to do a recursive update.
  @Override public TypeStruct clean() {
    if( this==ALLSTRUCT || this==ALLSTRUCT_CLN )
      return ALLSTRUCT_CLN;     // Shortcut
    if( this==GENERIC ) return GENERIC;
    if( !_cyclic ) {            // Not cyclic, normal recursive walk
      Type[] ts = TypeAry.clone(_ts);
      for( int i=0; i<ts.length; i++ )
        if( ts[i] != null )
          ts[i] = ts[i].clean();
      return malloc(_name,_any,true,_flds,ts,_finals).hashcons_free();
    }
    // Cyclic, but perhaps already clean
    Ary<Type> reaches = reachable(true);
    boolean clean = true;
    for( Type t : reaches )
      if( t instanceof TypeStruct && !((TypeStruct)t)._cln )
        { clean=false; break; }
    if( clean ) return this;    // Already clean.

    // Need to clone the existing structure, then make it clean
    RECURSIVE_MEET++;
    assert OLD2APX.isEmpty();
    TypeStruct cln = clone_clean_str(this);
    RECURSIVE_MEET--;
    reaches = cln.reachable();  // Recompute on the new types
    TypeStruct cln2 = cln.install_cyclic(reaches);
    assert cln2.isa(this);
    OLD2APX.clear();
    return cln2;
  }

  private static TypeStruct clone_clean_str(TypeStruct dirty) {
    TypeStruct ts = OLD2APX.get(dirty);
    if( ts != null ) return ts;
    if( dirty._cln ) throw com.cliffc.aa.AA.unimpl(); // Return the clean copy
    ts = dirty.shallow_clone();
    ts._cln = true;
    ts._hash = ts.compute_hash();
    OLD2APX.put(dirty,ts);
    for( int i=0; i<ts._ts.length; i++ ) {
      Type td = dirty._ts[i];
      ts._ts[i] = td instanceof TypeMemPtr ? clone_clean_ptr((TypeMemPtr)td) : td;
    }
    return ts;
  }
  private static TypeMemPtr clone_clean_ptr(TypeMemPtr dirty) {
    TypeMemPtr nmp = OLD2APX.get(dirty);
    if( nmp != null ) return nmp;
    nmp = (TypeMemPtr)dirty.clone();
    if( dirty._obj instanceof TypeStruct )
      nmp._obj = clone_clean_str((TypeStruct)dirty._obj);
    nmp._hash = nmp.compute_hash();
    OLD2APX.put(dirty,nmp);
    return nmp;
  }

  // True if this field is not modified.  Allows a Load to bypass.
  boolean is_clean(String fld) { return _cln; }

  @Override public BitsAlias recursive_aliases(BitsAlias abs, TypeMem mem) {
    for( Type t : _ts ) abs = t.recursive_aliases(abs, mem);
    return abs;
  }

  // True if isBitShape on all bits
  @Override public byte isBitShape(Type t) {
    if( isa(t) ) return 0; // Can choose compatible format
    if( t.isa(this) ) return 0; // TODO: really: test same flds, each fld isBitShape
    return 99;
  }

  @Override public Type meet_nil() { return this; }

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

  // Keep the high parts
  @Override public TypeStruct startype() {
    String[] as = new String[_flds.length];
    Type  [] ts = TypeAry.get(_ts  .length);
    byte  [] bs = new byte  [_ts  .length];
    for( int i=0; i<as.length; i++ ) as[i] = fldBot(_flds[i]) ? "*" : _flds[i];
    for( int i=0; i<ts.length; i++ ) ts[i] = _ts[i].above_center() ? _ts[i] : _ts[i].dual();
    for( int i=0; i<bs.length; i++ ) bs[i] = ftop(); // top of lattice
    return malloc(_name,true,true,as,ts,bs).hashcons_free();
  }
}
