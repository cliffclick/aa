package com.cliffc.aa.HM;

import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;
import org.jetbrains.annotations.NotNull;

import java.util.*;
import java.util.function.Function;

import static com.cliffc.aa.AA.unimpl;

// Hindley-Milner typing.  Complete stand-alone, for research.  MEETs base
// types, instead of declaring type error.  Requires SSA renumbering; looks
// 'up' the Syntax tree for variables instead of building a 'nongen' set.
//
// T2 types form a Lattice, with 'unify' same as 'meet'.  T2's form a DAG
// (cycles if i allow recursive unification) with sharing.  Each Syntax has a
// T2, and the forest of T2s can share.  Leaves of a T2 can be either a simple
// concrete base type, or a sharable leaf.  Unify is structural, and where not
// unifyable the union is replaced with an Error.

// Extend to records with nil.
// Extend to aliases.

public class HM {
  // Mapping from primitive name to Type Variable
  static final HashMap<String,T2> PRIMS = new HashMap<>();
  // Mapping from primitive name to a data flow Type
  static final HashMap<String,Type> VALS = new HashMap<>();
  // Mapping from a function index (fidx) to an abstract transfer function,
  // which maps argument types to a return type.
  static final NonBlockingHashMapLong<Function<Syntax[],Type>> XFERS = new NonBlockingHashMapLong<>();
  // Mapping from a Type to a function (fidx in the TFP) which returns a pair
  // with this type as the first element.
  static final HashMap<Type,TypeFunPtr> PAIR1_ARGS = new HashMap<>();

  static final boolean DEBUG_LEAKS=false;
  static { BitsAlias.init0(); BitsFun.init0(); }

  static final boolean DO_HM  = true;
  static final boolean DO_GCP = false;

  public static Root hm( String sprog ) {
    Object dummy = TypeStruct.DISPLAY;

    Worklist work = new Worklist();

    // Simple types
    T2 bool  = T2.make_leaf(TypeInt.BOOL);
    T2 int64 = T2.make_leaf(TypeInt.INT64);
    T2 flt64 = T2.make_leaf(TypeFlt.FLT64);
    T2 strp  = T2.make_leaf(TypeMemPtr.STRPTR);

    // Primitives
    T2 var1 = T2.make_leaf();
    T2 var2 = T2.make_leaf();
    T2 var3 = T2.make_leaf();
    TypeFunPtr tfp;

    // Pair1 - a curried 'pair' operator
    TypeMemPtr tptr_pair = TypeMemPtr.make(BitsAlias.new_alias(BitsAlias.REC),TypeStruct.ANYSTRUCT);
    PRIMS.put("pair1",T2.make_fun(var1, T2.make_fun(var2, T2.make_struct(tptr_pair,new String[]{"0","1"},new T2[]{var1,var2}) ))); // curried
    VALS .put("pair1",tfp=TypeFunPtr.make_new_fidx(BitsFun.ALL,1,TypeMemPtr.NO_DISP));
    XFERS.put(tfp.fidx(), args -> {
        // Return a function which takes an arg (to be named later) and puts
        // args[0] as the first part of a tuple.  The function is lazily made
        // and cached.  This is more precision that most flow operators will have.
        final Type fld0 = args[0]._type;
        TypeFunPtr tfp0 = PAIR1_ARGS.get(fld0);
        if( tfp0!=null ) return tfp0;
        tfp0 = TypeFunPtr.make_new_fidx(BitsFun.ALL,1,TypeMemPtr.NO_DISP);
        PAIR1_ARGS.put(fld0,tfp0);
        XFERS.put(tfp0.fidx(), args0 -> tptr_pair.make_from(TypeStruct.make_tuple(fld0,args0==null?Type.ANY:args0[0]._type)));
        return tfp0;
      });

    // Pair - all arguments provided 'pair' operator
    PRIMS.put("pair",T2.make_fun(var1, var2, T2.make_struct(tptr_pair,new String[]{"0","1"},new T2[]{var1,var2}) )); // not-curried
    VALS .put("pair",tfp=TypeFunPtr.make_new_fidx(BitsFun.ALL,1,TypeMemPtr.NO_DISP));
    XFERS.put(tfp.fidx(), args -> {
        Type[] ts = TypeStruct.ts(args.length+1);
        ts[0] = Type.ANY;       // Display
        for( int i=0; i<args.length; i++ ) ts[i+1] = args[i]._type;
        return tptr_pair.make_from(TypeStruct.make_tuple(ts));
      });

    TypeMemPtr tptr_triple = TypeMemPtr.make(BitsAlias.new_alias(BitsAlias.REC),TypeStruct.ANYSTRUCT);
    PRIMS.put("triple",T2.make_fun(var1, var2, var3, T2.make_struct(tptr_triple,new String[]{"0","1","2"},new T2[]{var1,var2,var3}) ));
    VALS .put("triple",tfp=TypeFunPtr.make_new_fidx(BitsFun.ALL,1,TypeMemPtr.NO_DISP));
    XFERS.put(tfp.fidx(), args -> {
        Type[] ts = TypeStruct.ts(args.length+1);
        ts[0] = Type.ANY;       // Display
        for( int i=0; i<args.length; i++ ) ts[i+1] = args[i]._type;
        return tptr_triple.make_from(TypeStruct.make_tuple(ts));
      });

    PRIMS.put("if",T2.make_fun(var2,var1,var1,var1));
    VALS .put("if",tfp=TypeFunPtr.make_new_fidx(BitsFun.ALL,1,TypeMemPtr.NO_DISP));
    XFERS.put(tfp.fidx(), args -> {
        Type pred= args[0]._type;
        Type t1  = args[1]._type;
        Type t2  = args[2]._type;
        if( pred.above_center() )
          return Type.XSCALAR; // t1.join(t2);
        if( pred==TypeInt.TRUE )
          return t1;
        if( pred==TypeInt.FALSE )
          return t2;
        return t1.meet(t2);
      });

    PRIMS.put("dec",T2.make_fun(int64,int64));
    VALS .put("dec",tfp=TypeFunPtr.make_new_fidx(BitsFun.ALL,1,TypeMemPtr.NO_DISP));
    XFERS.put(tfp.fidx(), args -> {
        Type t0 = args[0]._type;
        if( t0.above_center() ) return TypeInt.INT64.dual();
        if( t0 instanceof TypeInt && t0.is_con() )
          return TypeInt.con(t0.getl()-1);
        return TypeInt.INT64;
      });

    PRIMS.put("*"  ,T2.make_fun(int64,int64,int64));
    VALS .put("*"  ,tfp=TypeFunPtr.make_new_fidx(BitsFun.ALL,1,TypeMemPtr.NO_DISP));
    XFERS.put(tfp.fidx(), args -> {
        Type t0 = args[0]._type;
        Type t1 = args[1]._type;
        if( t0.above_center() || t1.above_center() )
          return TypeInt.INT64.dual();
        if( t0 instanceof TypeInt && t1 instanceof TypeInt ) {
          if( t0.is_con() && t0.getl()==0 ) return TypeInt.ZERO;
          if( t1.is_con() && t1.getl()==0 ) return TypeInt.ZERO;
          if( t0.is_con() && t1.is_con() )
            return TypeInt.con(t0.getl()*t1.getl());
        }
        return TypeInt.INT64;
      });

    PRIMS.put("?0" ,T2.make_fun(T2.make_leaf(),bool));
    VALS .put("?0" ,tfp=TypeFunPtr.make_new_fidx(BitsFun.ALL,1,TypeMemPtr.NO_DISP));
    XFERS.put(tfp.fidx(), args -> {
        Type pred = args[0]._type;
        if( pred.above_center() ) return TypeInt.BOOL.dual();
        if( pred==Type.ALL ) return TypeInt.BOOL;
        if( pred == TypeInt.FALSE || pred == Type.NIL || pred==Type.XNIL )
          return TypeInt.TRUE;
        if( pred.meet_nil(Type.NIL)!=pred )
          return TypeInt.FALSE;
        return TypeInt.BOOL;
      });

    PRIMS.put("eq",T2.make_fun(var1,var1,bool));
    VALS .put("eq" ,tfp=TypeFunPtr.make_new_fidx(BitsFun.ALL,1,TypeMemPtr.NO_DISP));
    XFERS.put(tfp.fidx(), args -> {
        Type x0 = args[0]._type;
        Type x1 = args[1]._type;
        if( x0.above_center() || x1.above_center() ) return TypeInt.BOOL.dual();
        if( x0.is_con() && x1.is_con() && x0==x1 )
          return TypeInt.TRUE;
        // TODO: Can also know about nil/not-nil
        return TypeInt.BOOL;
      });

    PRIMS.put("isempty",T2.make_fun(strp,bool));
    VALS .put("isempty" ,tfp=TypeFunPtr.make_new_fidx(BitsFun.ALL,1,TypeMemPtr.NO_DISP));
    XFERS.put(tfp.fidx(), args -> {
        Type pred = args[0]._type;
        if( pred.above_center() ) return TypeInt.BOOL.dual();
        if( pred instanceof TypeStr && pred.is_con() )
          return TypeInt.con(pred.getstr().isEmpty() ? 1 : 0);
        return TypeInt.BOOL;
      });

    // Print a string; int->str
    PRIMS.put("str",T2.make_fun(int64,strp));
    VALS .put("str" ,tfp=TypeFunPtr.make_new_fidx(BitsFun.ALL,1,TypeMemPtr.NO_DISP));
    XFERS.put(tfp.fidx(), args -> {
        Type i = args[0]._type;
        if( i.above_center() ) return TypeMemPtr.STRPTR.dual();
        if( i instanceof TypeInt && i.is_con() )
          return TypeMemPtr.make(BitsAlias.STRBITS,TypeStr.con(String.valueOf(i.getl()).intern()));
        return TypeMemPtr.STRPTR;
      });
    // Factor; FP div/mod-like operation
    PRIMS.put("factor",T2.make_fun(flt64,T2.prim("divmod",flt64,flt64)));
    VALS .put("factor" ,tfp=TypeFunPtr.make_new_fidx(BitsFun.ALL,1,TypeMemPtr.NO_DISP));
    XFERS.put(tfp.fidx(), args -> {
        Type flt = args[0]._type;
        if( flt.above_center() ) return TypeFlt.FLT64.dual();
        return TypeFlt.FLT64;
      });

    // Parse
    Root prog = parse( sprog );

    // Prep for SSA: pre-gather all the (unique) ids
    int cnt_syns = prog.prep_tree(null,null,work);
    int init_T2s = T2.CNT;

    while( work.len()>0 ) {     // While work
      int oldcnt = T2.CNT;      // Used for cost-check when no-progress
      Syntax syn = work.pop();  // Get work
      if( DO_HM && !DO_GCP ) {
        T2 old = syn._t;        // Old value for progress assert
        if( syn.hm(work) ) {
          assert !syn.debug_find().unify(old.find(),null);// monotonic: unifying with the result is no-progress
          syn.add_hm_work(work);     // Push affected neighbors on worklist
        } else {
          assert !DEBUG_LEAKS || oldcnt==T2.CNT;  // No-progress consumes no-new-T2s
        }
      }
      if( DO_GCP && !DO_HM ) {
        Type t = syn.val();
        if( t!=syn._type ) {       // Progress
          assert syn._type.isa(t); // Monotonic falling
          syn._type = t;           // Update type
          if( syn._par!=null ) {   // Generally, parent needs revisit
            work.push(syn._par);   // Assume parent needs revisit
            syn._par.add_val_work(syn,work); // Push affected neighbors on worklist
          }
        }
      }

      // VERY EXPENSIVE ASSERT: O(n^2).  Every Syntax that makes progress is on the worklist
      assert prog.more_work(work);
    }
    assert prog.more_work(work);

    System.out.println("Initial T2s: "+init_T2s+", Prog size: "+cnt_syns+", worklist iters: "+work._cnt+", T2s: "+T2.CNT);
    return prog;
  }

  static void reset() {
    PRIMS.clear();
    VALS.clear();
    XFERS.clear();
    PAIR1_ARGS.clear();
    Lambda.FUNS.clear();
    T2.reset();
    BitsAlias.reset_to_init0();
    BitsFun.reset_to_init0();
  }

  // ---------------------------------------------------------------------
  // Program text for parsing
  private static int X;
  private static byte[] BUF;
  @Override public String toString() { return new String(BUF,X,BUF.length-X); }
  static Root parse( String s ) {
    X = 0;
    BUF = s.getBytes();
    Syntax prog = term();
    if( skipWS() != -1 ) throw unimpl("Junk at end of program: "+new String(BUF,X,BUF.length-X));
    return new Root(prog);
  }
  static Syntax term() {
    if( skipWS()==-1 ) return null;
    if( isDigit(BUF[X]) ) return number();
    if( BUF[X]=='"' ) return string();
    if( BUF[X]=='(' ) {         // Parse an Apply
      X++;                      // Skip paren
      Syntax fun = term();
      Ary<Syntax> ARGS = new Ary<>(new Syntax[1],0);
      while( skipWS()!= ')' && X<BUF.length ) ARGS.push(term());
      require(')');
      return new Apply(fun,ARGS.asAry());
    }
    if( BUF[X]=='{' ) {         // Lambda of 1 or 2 args
      X++;                      // Skip paren
      Ary<String> args = new Ary<>(new String[1],0);
      while( skipWS()!='-' ) args.push(id());
      require("->");
      Syntax body = term();
      require('}');
      return new Lambda(body,args.asAry());
    }
    // Let or Id
    if( isAlpha0(BUF[X]) ) {
      String id = id();
      if( skipWS()!='=' )  return new Ident(id);
      // Let expression; "id = term(); term..."
      X++;                      // Skip '='
      Syntax def = term();
      require(';');
      return new Let(id,def,term());
    }

    // Structure
    if( BUF[X]=='@' ) {
      X++;
      require('{');
      Ary<String>  ids = new Ary<>(String.class);
      Ary<Syntax> flds = new Ary<>(Syntax.class);
      while( skipWS()!='}' && X < BUF.length ) {
        String id = require('=',id());
        Syntax fld = term();
        if( fld==null ) throw unimpl("Missing term for field "+id);
        ids .push( id);
        flds.push(fld);
        if( skipWS()==',' ) X++;
      }
      require('}');
      return new Struct(ids.asAry(),flds.asAry());
    }

    // Field lookup is prefix or backwards: ".x term"
    if( BUF[X]=='.' ) {
      X++;
      return new Field(id(),term());
    }

    throw unimpl("Unknown syntax");
  }
  private static final SB ID = new SB();
  private static String id() {
    ID.clear();
    while( X<BUF.length && isAlpha1(BUF[X]) )
      ID.p((char)BUF[X++]);
    String s = ID.toString().intern();
    if( s.length()==0 ) throw unimpl("Missing id");
    return s;
  }
  private static Syntax number() {
    if( BUF[X]=='0' ) { X++; return new Con(Type.XNIL); }
    int sum=0;
    while( X<BUF.length && isDigit(BUF[X]) )
      sum = sum*10+BUF[X++]-'0';
    if( X>= BUF.length || BUF[X]!='.' )
      return new Con(TypeInt.con(sum));
    X++;
    float f = (float)sum;
    f = f + (BUF[X++]-'0')/10.0f;
    return new Con(TypeFlt.con(f));
  }
  private static Syntax string() {
    int start = ++X;
    while( X<BUF.length && BUF[X]!='"' ) X++;
    return require('"', new Con(TypeMemPtr.make(BitsAlias.STRBITS,TypeStr.con(new String(BUF,start,X-start).intern()))));
  }
  private static byte skipWS() {
    while( X<BUF.length && isWS(BUF[X]) ) X++;
    return X==BUF.length ? -1 : BUF[X];
  }
  private static boolean isWS    (byte c) { return c == ' ' || c == '\t' || c == '\n' || c == '\r'; }
  private static boolean isDigit (byte c) { return '0' <= c && c <= '9'; }
  private static boolean isAlpha0(byte c) { return ('a'<=c && c <= 'z') || ('A'<=c && c <= 'Z') || (c=='_') || (c=='*') || (c=='?'); }
  private static boolean isAlpha1(byte c) { return isAlpha0(c) || ('0'<=c && c <= '9') || (c=='/'); }
  private static void require(char c) { if( skipWS()!=c ) throw unimpl("Missing '"+c+"'"); X++; }
  private static <T> T require(char c, T t) { require(c); return t; }
  private static void require(String s) {
    skipWS();
    for( int i=0; i<s.length(); i++ )
      if( X+i >= BUF.length || BUF[X+i]!=s.charAt(i) )
        throw unimpl("Missing '"+s+"'");
    X+=s.length();
  }

  // ---------------------------------------------------------------------
  // Worklist of Syntax nodes
  private static class Worklist {
    public int _cnt;
    private final Ary<Syntax> _ary = new Ary<>(Syntax.class); // For picking random element
    private final HashSet<Syntax> _work = new HashSet<>();    // For preventing dups
    public int len() { return _ary.len(); }
    public void push(Syntax s) { if( s!=null && !_work.contains(s) ) _work.add(_ary.push(s)); }
    public Syntax pop() { Syntax s = _ary.pop();_cnt++;            _work.remove(s); return s; }
    //public Syntax pop() { Syntax s = _ary.del(  _cnt++%_ary._len); _work.remove(s); return s; }
    public boolean has(Syntax s) { return _work.contains(s); }
    public void addAll(Ary<? extends Syntax> ss) { if( ss != null ) for( Syntax s : ss ) push(s); }
    @Override public String toString() { return _ary.toString(); }
  }

  // ---------------------------------------------------------------------
  // Small classic tree of T2s, immutable, with sharing at the root parts.
  static class VStack implements Iterable<T2> {
    final VStack _par;
    final T2 _nongen;
    VStack( VStack par, T2 nongen ) { _par=par; _nongen=nongen; }
    @Override public String toString() {
      // Collect dups across the forest of types
      VBitSet dups = new VBitSet();
      for( VStack vs = this; vs!=null; vs = vs._par )
        vs._nongen.get_dups(dups);
      // Now recursively print
      return str(new SB(),dups).toString();
    }
    SB str(SB sb, VBitSet dups) {
      _nongen.str(sb,new VBitSet(),dups);
      if( _par!=null ) _par.str(sb.p(" , "),dups);
      return sb;
    }
    @NotNull @Override public Iterator<T2> iterator() { return new Iter(); }
    private class Iter implements Iterator<T2> {
      private VStack _vstk;
      Iter() { _vstk=VStack.this; }
      @Override public boolean hasNext() { return _vstk!=null; }
      @Override public T2 next() { T2 v = _vstk._nongen; _vstk = _vstk._par;  return v; }
    }
  }

  // ---------------------------------------------------------------------
  static abstract class Syntax {
    Syntax _par;                // Parent in the AST
    VStack _nongen;             // Non-generative type variables
    T2 _t;                      // Current HM type
    T2 find() {                 // U-F find
      T2 t = _t.find();
      return t==_t ? t : (_t=t);
    }
    T2 debug_find() { return _t.debug_find(); } // Find, without the roll-up

    // Dataflow type.  Varies during a run of CCP.
    Type _type;


    // Compute and set a new HM type.
    // If no change, return false.
    // If a change, return always true, however:
    // - If 'work' is null do not change/set anything.
    // - If 'work' is available, set a new HM in '_t' and update the worklist.
    abstract boolean hm(Worklist work);

    T2 lookup_tvar(String name) { return null; } // Lookup name in scope & return type

    abstract void add_hm_work(Worklist work); // Add affected neighbors to worklist

    // Compute and return (and do not set) a new dataflow type
    abstract Type val();

    Type lookup_val(String name) { throw unimpl(); } // Lookup name in scope & return type

    void add_val_work(Syntax child, Worklist work) {} // Add affected neighbors to worklist

    abstract int prep_tree(Syntax par, VStack nongen, Worklist work);
    final void prep_tree_impl( Syntax par, VStack nongen, Worklist work, T2 t ) {
      _par=par;
      _t=t;
      _nongen = nongen;
      work.push(this);
      _type = Type.ANY;         // Prepare for GCP
    }
    void prep_lookup_deps(Ident id) {}

    // Giant Assert: True if OK; all Syntaxs off worklist do not make progress
    abstract boolean more_work(Worklist work);
    final boolean more_work_impl(Worklist work) {
      if( work.has(this) ) return true;
      if( DO_HM && hm(null) )   // Any more HM work?
        return false;            // Found HM work not on worklist
      if( DO_GCP && val()!=_type )
        return false;            // Found GCP work not on worklist
      return true;
    }
    // Print for debugger
    @Override final public String toString() { return str(new SB()).toString(); }
    abstract SB str(SB sb);
    // Line-by-line print with more detail
    public String p() { return p0(new SB(), new VBitSet()).toString(); }
    final SB p0(SB sb, VBitSet dups) {
      p1(sb.i()).p(" ");
      _t.get_dups(dups);
      if( DO_HM  ) _t.str(sb, new VBitSet(),dups).p(" ");
      if( DO_GCP ) _type.str(sb,new VBitSet(),null,false);
      sb.nl();
      return p2(sb.ii(1),dups).di(1);
    }
    abstract SB p1(SB sb);      // Self short print
    abstract SB p2(SB sb, VBitSet dups); // Recursion print
  }

  static class Con extends Syntax {
    final Type _con;
    Con(Type con) { super(); _con=con; }
    @Override SB str(SB sb) { return p1(sb); }
    @Override SB p1(SB sb) { return sb.p(_con instanceof TypeMemPtr ? "str" : _con.toString()); }
    @Override SB p2(SB sb, VBitSet dups) { return sb; }
    @Override boolean hm(Worklist work) { return false; }
    @Override Type val() { return _con; }
    @Override void add_hm_work(Worklist work) { work.push(_par); }
    @Override int prep_tree( Syntax par, VStack nongen, Worklist work ) {
      prep_tree_impl(par, nongen, work, T2.make_leaf(_con));
      return 1;
    }
    @Override boolean more_work(Worklist work) { return more_work_impl(work); }
  }


  static class Ident extends Syntax {
    final String _name;
    T2 _idt;                    // Type var for the name in scope
    Ident(String name) { _name=name; }
    @Override SB str(SB sb) { return p1(sb); }
    @Override SB p1(SB sb) { return sb.p(_name); }
    @Override SB p2(SB sb, VBitSet dups) { return sb; }
    @Override boolean hm(Worklist work) {
      return _idt.find().fresh_unify(find(),_nongen,work);
    }
    @Override void add_hm_work(Worklist work) {
      work.push(_par);
      T2 t = _idt.find();
      if( t.occurs_in(_par) )                        // Got captured in some parent?
        t.add_deps_work(work);                       // Need to revisit dependent ids
    }
    @Override Type val() {
      Type t = null;
      for( Syntax syn = _par; syn!=null; syn = syn._par )
        if( (t=syn.lookup_val(_name)) != null )
          break;                         // Found in scope
      if( t==null ) t = VALS.get(_name); // Lookup in prims
      assert t!=null;                    // Missing a primitive?
      return t;
    }
    @Override int prep_tree( Syntax par, VStack nongen, Worklist work ) {
      prep_tree_impl(par,nongen,work,T2.make_leaf());
      for( Syntax syn = _par; syn!=null; syn = syn._par )
        syn.prep_lookup_deps(this);

      // Lookup, and get the T2 type var
      T2 t = null;
      for( Syntax syn = _par; syn!=null; syn = syn._par )
        if( (t=syn.lookup_tvar(_name)) != null )
          break;                          // Found in scope
      if( t==null ) t = PRIMS.get(_name); // Lookup in prims
      if( t==null )                       // Still not found
        throw new RuntimeException("Parse error, "+_name+" is undefined");
      _idt = t;

      return 1;
    }
    @Override boolean more_work(Worklist work) { return more_work_impl(work); }
  }


  static class Lambda extends Syntax {
    // Map from FIDXs to Lambdas
    static final NonBlockingHashMapLong<Lambda> FUNS = new NonBlockingHashMapLong<>();
    final String[] _args;
    final Syntax _body;
    final T2[] _targs;
    final Type[] _types;
    final TypeFunPtr _tfp;

    Lambda(Syntax body, String... args) {
      _args=args;
      _body=body;
      // Type variables for all arguments
      _targs = new T2[args.length];
      for( int i=0; i<args.length; i++ ) _targs[i] = T2.make_leaf();
      // Flow types for all arguments
      _types = new Type[args.length];
      for( int i=0; i<args.length; i++ ) _types[i] = Type.XSCALAR;
      // A unique FIDX for this Lambda
      _tfp = TypeFunPtr.make_new_fidx(BitsFun.ALL,_args.length,Type.ANY);
      FUNS.put(_tfp.fidx(),this);
      XFERS.put(_tfp.fidx(), args0 -> {
          // Ignore arguments, and return body type.  Very conservative.
          return _body._type;
        });
    }
    @Override SB str(SB sb) {
      sb.p("{ ");
      for( String arg : _args ) sb.p(arg).p(' ');
      return _body.str(sb.p("-> ")).p(" }");
    }
    @Override SB p1(SB sb) {
      sb.p("{ ");
      for( int i=0; i<_args.length; i++ )
        sb.p(_args[i]).p(':').p(_types[i]).p(' ');
      return sb.p(" -> ... } ");
    }
    @Override SB p2(SB sb, VBitSet dups) { return _body.p0(sb,dups); }
    T2 targ(int i) { T2 targ = _targs[i].find(); return targ==_targs[i] ? targ : (_targs[i]=targ); }
    @Override boolean hm(Worklist work) {
      boolean progress = false;
      // The normal lambda work
      T2 old = find();
      if( old.is_err() ) return false;
      if( old.is_fun() ) {      // Already a function?  Compare-by-parts
        for( int i=0; i<_targs.length; i++ )
          if( old.args(i).unify(targ(i),work) )
            { progress=true; break; }
        if( !progress && !old.args(_targs.length).unify(_body.find(),work) )
          return false;           // Shortcut: no progress, no allocation
      }
      // Make a new T2 for progress
      T2[] targs = Arrays.copyOf(_targs,_targs.length+1);
      targs[_targs.length] = _body.find();
      T2 fun = T2.make_fun(targs);
      return old.unify(fun,work);
    }
    @Override T2 lookup_tvar(String name) {
      for( int i=0; i<_args.length; i++ )
        if( Util.eq(_args[i],name) ) return targ(i);
      return null;
    }
    @Override void add_hm_work(Worklist work) {
      work.push(_par );
      work.push(_body);
      for( int i=0; i<_targs.length; i++ )
        if( targ(i).occurs_in_type(find()) ) work.addAll(_targs[i]._deps);
    }
    @Override Type val() {
      return _tfp;
    }
    @Override void add_val_work(Syntax child, Worklist work) {
      // Body changed, all Apply sites need to recompute
      work.addAll(_t._deps);
    }
    @Override Type lookup_val(String name) {
      for( int i=0; i<_args.length; i++ )
        if( Util.eq(_args[i],name) )
          return _types[i];
      return null;
    }
    @Override int prep_tree( Syntax par, VStack nongen, Worklist work ) {
      prep_tree_impl(par,nongen,work,T2.make_leaf());
      VStack vs = nongen;
      for( T2 targ : _targs ) vs = new VStack(vs, targ);
      return _body.prep_tree(this,vs,work) + 1;
    }
    @Override void prep_lookup_deps(Ident id) {
      for( int i=0; i<_args.length; i++ )
        if( Util.eq(_args[i],id._name) ) _targs[i].push_update(id);
    }
    @Override boolean more_work(Worklist work) {
      if( !more_work_impl(work) ) return false;
      return _body.more_work(work);
    }
  }

  static class Let extends Syntax {
    final String _arg0;
    final Syntax _def, _body;
    T2 _targ;
    Let(String arg0, Syntax def, Syntax body) { _arg0=arg0; _body=body; _def=def; _targ=T2.make_leaf(); }
    @Override SB str(SB sb) { return _body.str(_def.str(sb.p(_arg0).p(" = ")).p("; ")); }
    @Override SB p1(SB sb) { return sb.p(_arg0).p(" = ... ; ..."); }
    @Override SB p2(SB sb, VBitSet dups) { _def.p0(sb,dups); return _body.p0(sb,dups); }
    T2 targ() { T2 targ = _targ.find(); return targ==_targ ? targ : (_targ=targ); }
    @Override boolean hm(Worklist work) {
      return targ().unify(_def.find(),work);
    }
    @Override T2 lookup_tvar(String name) { return Util.eq(_arg0,name) ? targ() : null; }
    @Override void add_hm_work(Worklist work) {
      work.push(_par);
      work.push(_body);
      work.push(_def);
      if( targ().occurs_in_type(_def.find()) ) work.addAll(_targ._deps);
    }
    @Override Type val() { return _body._type; }
    @Override Type lookup_val(String name) { return Util.eq(_arg0,name) ? _def._type : null; }
    @Override void add_val_work(Syntax child, Worklist work) {
      if( child==_def )
        work.addAll(_targ._deps);
    }

    @Override int prep_tree( Syntax par, VStack nongen, Worklist work ) {
      prep_tree_impl(par,nongen,work,_body._t);
      int cnt = _body.prep_tree(this,           nongen       ,work) +
                _def .prep_tree(this,new VStack(nongen,_targ),work);
      _t = _body._t;            // Unify 'Let._t' with the '_body'
      return cnt+1;
    }
    @Override void prep_lookup_deps(Ident id) {
      if( Util.eq(id._name,_arg0) ) _targ.push_update(id);
    }
    @Override boolean more_work(Worklist work) {
      if( !more_work_impl(work) ) return false;
      return _body.more_work(work) && _def.more_work(work);
    }
  }

  static class Apply extends Syntax {
    final Syntax _fun;
    final Syntax[] _args;
    Apply(Syntax fun, Syntax... args) { _fun = fun; _args = args; }
    @Override SB str(SB sb) {
      _fun.str(sb.p("(")).p(" ");
      for( Syntax arg : _args )
        arg.str(sb).p(" ");
      return sb.unchar().p(")");
    }
    @Override SB p1(SB sb) { return sb.p("(...)"); }
    @Override SB p2(SB sb, VBitSet dups) {
      _fun.p0(sb,dups);
      for( Syntax arg : _args ) arg.p0(sb,dups);
      return sb;
    }

    // Unifiying these: make_fun(this.arg0 this.arg1 -> new     )
    //                      _fun{_fun.arg0 _fun.arg1 -> _fun.rez}
    @Override boolean hm(Worklist work) {
      boolean progress = false;

      // Discover not-nil in the trivial case of directly using the 'if'
      // primitive against a T2.is_struct().  Will not work if 'if' is some
      // more hidden or complex function (e.q. '&&' or '||') or the predicate
      // implies not-null on some other struct.
      T2 str = is_if_nil();
      if( str!=null && str.is_struct() ) {
        TypeMemPtr tmp = (TypeMemPtr)str._t;
        if( !tmp._aliases.test(0) ) {
          str._t = str._t.meet(Type.XNIL); // Nil is allowed on the tested value
          progress = true;
          if( work==null ) return true;
          work.addAll(str._deps);
        }
      }

      // Progress if:
      //   _fun is not a function
      //   any arg-pair-unifies make progress
      //   this-unify-_fun.return makes progress
      T2 tfun = _fun.find();
      if( !tfun.is_fun() ) {    // Not a function, so progress
        if( tfun.is_err() ) return find().unify(tfun,work);
        if( work==null ) return true; // Will-progress & just-testing
        T2[] targs = new T2[_args.length+1];
        for( int i=0; i<_args.length; i++ )
          targs[i] = _args[i].find();
        targs[_args.length] = find(); // Return
        T2 nfun = T2.make_fun(targs);
        progress = tfun.unify(nfun,work);
        return tfun.find().is_err() ? find().unify(tfun.find(),work) : progress;
      }

      if( tfun._args.length != _args.length+1 )
        progress |= T2.make_err("Mismatched argument lengths").unify(find(),work);
      // Check for progress amongst arg pairs
      for( int i=0; i<_args.length; i++ ) {
        progress |= tfun.args(i).unify(_args[i].find(),work);
        if( progress && work==null )
          return true;          // Will-progress & just-testing early exit
      }
      // Check for progress on the return
      progress |= tfun.args(_args.length).unify(find(),work);
      if( tfun.find().is_err() ) return find().unify(tfun.find(),work);

      return progress;
    }
    @Override void add_hm_work(Worklist work) {
      work.push(_par);
      for( Syntax arg : _args ) work.push(arg);
    }
    @Override Type val() {
      if( _fun._type.above_center() ) return Type.XSCALAR;
      if( !(_fun._type instanceof TypeFunPtr) ) return Type.SCALAR;
      TypeFunPtr tfp = (TypeFunPtr)_fun._type;
      // Have some functions, meet over their returns.
      Type rez = Type.ANY;
      for( int fidx : tfp._fidxs )
        rez = rez.meet(XFERS.get(fidx).apply(_args));
      return rez;
    }
    @Override void add_val_work(Syntax child, Worklist work) {
      // If function changes type, recompute self
      if( child==_fun ) work.push(this);
      // If an argument changes type, adjust the lambda arg types
      if( _fun._type.above_center() ) return;
      if( !(_fun._type instanceof TypeFunPtr) ) return;
      // Meet the actuals over the formals.
      for( int fidx : ((TypeFunPtr)_fun._type)._fidxs ) {
        Lambda fun = Lambda.FUNS.get(fidx);
        if( fun!=null ) {
          fun._t.push_update(this); // Discovered as call-site; if the Lambda changes the Apply needs to be revisited.
          for( int i=0; i<fun._types.length; i++ ) {
            Type formal = fun._types[i];
            Type actual = this instanceof Root ? Type.SCALAR : _args[i]._type;
            if( formal != actual ) {
              fun._types[i] = formal.meet(actual);
              work.addAll(fun._targs[i]._deps);
            }
          }
        }
      }
    }

    @Override Type lookup_val(String name) { return null; } // Lookup name in scope & return type
    @Override int prep_tree(Syntax par, VStack nongen, Worklist work) {
      prep_tree_impl(par,nongen,work,T2.make_leaf());
      int cnt = 1+_fun.prep_tree(this,nongen,work);
      for( Syntax arg : _args ) cnt += arg.prep_tree(this,nongen,work);
      T2 str = is_if_nil();
      if( str!=null ) str.push_update(this);
      return cnt;
    }
    @Override boolean more_work(Worklist work) {
      if( !more_work_impl(work) ) return false;
      if( !_fun.more_work(work) ) return false;
      for( Syntax arg : _args ) if( !arg.more_work(work) ) return false;
      return true;
    }
    // True if we can refine an if-not-nil
    private T2 is_if_nil() {
      return _fun instanceof Ident && Util.eq(((Ident)_fun)._name,"if") && _args[0] instanceof Ident ? _args[0].find() : null;
    }
  }


  static class Root extends Apply {
    Root(Syntax body) { super(body); }
    @Override SB str(SB sb) { return _fun.str(sb); }
    @Override boolean hm(Worklist work) { return find().unify(_fun.find(),work); }
    @Override void add_hm_work(Worklist work) { }

    private static Type xval(TypeFunPtr fun) {
      Type rez = Type.ANY;
      for( int fidx : fun._fidxs )
        rez = rez.meet(XFERS.get(fidx).apply(null));
      return rez;
    }
    @Override Type val() {
      Type rez = _fun._type;
      while( rez instanceof TypeFunPtr )
        rez = xval((TypeFunPtr)rez); // Propagate arg types
      return _fun._type;
    }
    // Expand functions to full signatures, recursively
    Type flow_type() { return add_sig(_fun._type); }

    private static Type add_sig(Type t) {
      if( t instanceof TypeFunPtr ) {
        Type rez = add_sig(xval((TypeFunPtr)t));
        return TypeFunSig.make(TypeTuple.make_ret(rez),TypeTuple.make_args());
      } else {
        return t;
      }
    }
  }


  // Structure or Records.
  static class Struct extends Syntax {
    final TypeMemPtr _tmp;
    final String[]  _ids;
    final Syntax[] _flds;
    Struct( String[] ids, Syntax[] flds ) {
      _ids=ids;
      _flds=flds;
      // Make a TMP
      int alias = BitsAlias.new_alias(BitsAlias.REC);
      _tmp = TypeMemPtr.make(alias,TypeStruct.ANYSTRUCT);
    }
    @Override SB str(SB sb) {
      sb.p("@{");
      for( int i=0; i<_ids.length; i++ ) {
        sb.p(' ').p(_ids[i]).p(" = ");
        _flds[i].str(sb);
        if( i < _ids.length-1 ) sb.p(',');
      }
      return sb.p("}:").p(_tmp._aliases.toString());
    }
    @Override SB p1(SB sb) { return _tmp.str(sb,new VBitSet(),null,true).p("@{ ... } "); }
    @Override SB p2(SB sb, VBitSet dups) {
      for( int i=0; i<_ids.length; i++ )
        _flds[i].p0(sb.i().p(_ids[i]).p(" = ").nl(),dups);
      return sb;
    }
    @Override boolean hm(Worklist work) {
      boolean progress = false, must_alloc=false;

      // Force result to be a struct with at least these fields.
      // Do not allocate a T2 unless we need to pick up fields.
      T2 rec = find();
      if( rec.is_err() ) return false;
      for( String id : _ids )
        if( Util.find(rec._ids, id) == -1 )
          { must_alloc = true; break; }
      if( must_alloc ) {              // Must allocate.
        if( work==null ) return true; // Will progress
        T2[] t2s = new T2[_ids.length];
        for( int i=0; i<_ids.length; i++ )
          t2s[i] = _flds[i].find();
        T2.make_struct(_tmp,_ids,t2s).unify(rec,work);
        rec=find();
        progress = true;
      }

      // Extra fields are unified with ERR since they are not created here:
      // error to load from a non-existing field
      for( int i=0; i<rec._ids.length; i++ ) {
        if( Util.find(_ids,rec._ids[i])== -1 && !rec.args(i).is_err() ) {
          if( work==null ) return true;
          progress |= T2.make_err("Missing field "+rec._ids[i]+" in "+this).unify(rec.args(i),work);
        }
      }

      // Unify existing fields.  Ignore extras on either side.
      for( int i=0; i<_ids.length; i++ ) {
        int idx = Util.find(rec._ids,_ids[i]);
        if( idx!= -1 ) progress |= rec.args(idx).unify(_flds[i].find(),work);
        if( work==null && progress ) return true;
      }

      return progress;
    }
    @Override void add_hm_work(Worklist work) {
      work.push(_par);
      for( Syntax fld : _flds ) work.push(fld);
    }
    @Override Type val() {
      Type[] ts = Types.get(_flds.length);
      for( int i=0; i<_flds.length; i++ )
        ts[i] = _flds[i]._type;
      TypeStruct tstr = TypeStruct.make(_ids,ts);
      TypeStruct t2 = tstr.approx(1,_tmp.getbit());
      return _tmp.make_from(t2);
    }

    @Override Type lookup_val(String name) { return null; } // Lookup name in scope & return type

    @Override int prep_tree(Syntax par, VStack nongen, Worklist work) {
      T2[] t2s = new T2[_ids.length];
      prep_tree_impl(par, nongen, work, T2.make_struct(_tmp,_ids,t2s));
      //prep_tree_impl(par, nongen, work, T2.make_struct(_tmp,new String[0],new T2[0]));
      int cnt = 1;              // One for self
      for( int i=0; i<_flds.length; i++ ) { // Prep all sub-fields
        cnt += _flds[i].prep_tree(this,nongen,work);
        t2s[i] = _flds[i].find();
      }
      return cnt;
    }
    @Override boolean more_work(Worklist work) {
      if( !more_work_impl(work) ) return false;
      for( Syntax fld : _flds )
        if( !fld.more_work(work) )
          return false;
      return true;
    }
  }

  // Field lookup in a Struct
  static class Field extends Syntax {
    final String _id;
    final Syntax _rec;
    Field( String id, Syntax str ) { _id=id; _rec =str; }
    @Override SB str(SB sb) { return _rec.str(sb.p(".").p(_id).p(' ')); }
    @Override SB p1 (SB sb) { return sb.p(".").p(_id); }
    @Override SB p2(SB sb, VBitSet dups) { return _rec.p0(sb,dups); }
    @Override boolean hm(Worklist work) {
      boolean progress;
      T2 rec = _rec.find();
      int idx = rec._ids==null ? -1 : Util.find(rec._ids,_id);
      if( idx==-1 ) {           // Not a struct or no field, force it to be one
        if( find().is_err() ) return false;
        if( work==null ) return true;
        if( rec.is_err() ) return find().unify(rec,work);
        // We need to make a TypeMemPtr to a Struct, but do not have the alias (yet).
        TypeMemPtr tmp = TypeMemPtr.make(BitsAlias.EMPTY,TypeStruct.ANYSTRUCT);
        // The actual Struct is just a 1-field struct, and since structs ignore
        // field order it does not matter in which order fields get unified.
        progress = T2.make_struct(tmp,new String[]{_id}, new T2[]{find().push_update(rec._deps)}).unify(rec, work);
      } else {
        // Unify the field
        progress = rec.args(idx).unify(find(), work);
        Type t = find()._t;
        if( t == Type.ALL || t == Type.SCALAR || t == Type.NSCALR )
          throw unimpl(); // TODO: unify with error
        //  progress |= T2.make_err("Missing field "+_id+" in "+rec.find()).unify(find(),work);
      }
      return progress;
    }
    @Override void add_hm_work(Worklist work) {
      work.push(_par);
      work.push(_rec);
      _rec.add_hm_work(work);
    }
    @Override Type val() {
      Type trec = _rec._type;
      if( trec.above_center() ) return Type.XSCALAR;
      if( trec instanceof TypeMemPtr ) {
        TypeMemPtr tmp = (TypeMemPtr)trec;
        if( tmp._obj instanceof TypeStruct ) {
          TypeStruct tstr = (TypeStruct)tmp._obj;
          int idx = tstr.find(_id);
          if( idx!=-1 )
            return tstr._ts[idx]; // Field type
        }
        return TypeMemPtr.make(BitsAlias.STRBITS,TypeStr.con(("Missing field "+_id+" in "+tmp._obj).intern())); // Any or All?      }
      }
      return TypeMemPtr.make(BitsAlias.STRBITS,TypeStr.con(("No field "+_id+" in "+trec).intern()));
    }
    @Override Type lookup_val(String name) { return null; } // Lookup name in scope & return type
    @Override int prep_tree(Syntax par, VStack nongen, Worklist work) {
      prep_tree_impl(par, nongen, work, T2.make_leaf());
      return _rec.prep_tree(this,nongen,work)+1;
    }
    @Override boolean more_work(Worklist work) {
      if( !more_work_impl(work) ) return false;
      return _rec.more_work(work);
    }
  }

  // ---------------------------------------------------------------------
  // T2 types form a Lattice, with 'unify' same as 'meet'.  T2's form a DAG
  // (cycles if i allow recursive unification) with sharing.  Each Syntax has a
  // T2, and the forest of T2s can share.  Leaves of a T2 can be either a
  // simple concrete base type, or a sharable leaf.  Unify is structural, and
  // where not unifyable the union is replaced with an Error.
  static class T2 {
    private static int CNT=0;
    final int _uid;

    // A plain type variable starts with a 'V', and can unify directly.
    // Everything else is structural - during unification they must match names
    // and arguments and Type constants.
    @NotNull String _name; // name, e.g. "->" or "pair" or "V123" or "base"

    // Structural parts to unify with, or slot 0 is used during normal U-F
    T2 @NotNull [] _args;

    // A dataflow type.  Either ANY for a bare leaf, or a TypeMemPtr with
    // aliases (including nil or not), to a bare structure, some scalar (for
    // H-M base types).
    @NotNull Type _t;

    // Structs have field names
    @NotNull String[] _ids;

    // Dependent (non-local) tvars to revisit
    Ary<Syntax> _deps;

    // Constructor factories.
    static T2 make_fun(T2... args) { return new T2("->"   ,Type.ANY ,null,args); }
    static T2 make_leaf()          { return new T2("V"+CNT,Type.ANY ,null,new T2[1]); }
    static T2 make_leaf(Type t)    { return new T2("V"+CNT,t        ,null,new T2[1]); }
    static T2 make_struct( TypeMemPtr tmp, String[] ids, T2[] flds ) { return new T2("@{}", tmp,ids,flds); }
    static T2 make_err(String s)   { return new T2("Err"  ,TypeStr.con(s.intern()),null); }
    static T2 prim(String name, T2... args) { return new T2(name,Type.ANY,null,args); }
    T2 copy() { return new T2(_name,_t,_ids,new T2[_args.length]); }

    private T2(@NotNull String name, @NotNull Type t, String[] ids, T2 @NotNull ... args) {
      _uid = CNT++;
      _name= name;
      _t = t;
      _ids = ids;
      _args= args;
      _deps = null;
    }

    // A type var, not a concrete leaf.  Might be U-Fd or not.
    boolean is_leaf() { return _name.charAt(0)=='V'; }
    boolean no_uf() { return !is_leaf() || _args[0]==null; }
    boolean isa(String name) { return Util.eq(_name,name); }
    boolean is_fun () { return isa("->"); }
    boolean is_struct() { return isa("@{}"); }
    boolean is_mem()  { return isa("[]"); }
    boolean is_err()  { return isa("Err"); }

    T2 debug_find() {// Find, without the roll-up
      if( !is_leaf() ) return this; // Shortcut
      T2 u = _args[0];
      if( u==null ) return this; // Shortcut
      if( u.no_uf() ) return u;  // Shortcut
      // U-F fixup
      while( u.is_leaf() && u._args[0]!=null ) u = u._args[0];
      return u;
    }

    // U-F find
    T2 find() {
      T2 u = debug_find();
      if( u==this || u==_args[0] ) return u;
      T2 v = this, v2;
      while( v.is_leaf() && (v2=v._args[0])!=u ) { v._args[0]=u; v = v2; }
      return u;
    }
    // U-F find on the args array
    T2 args(int i) {
      T2 u = _args[i];
      T2 uu = u.find();
      return u==uu ? uu : (_args[i]=uu);
    }

    // U-F union; this becomes that; returns 'that'.
    // No change if only testing, and reports progress.
    boolean union(T2 that, Worklist work) {
      assert no_uf(); // Cannot union twice
      if( this==that ) return false;
      if( work==null ) return true; // Report progress without changing
      // Worklist: put updates on the worklist for revisiting
      if( _deps != null ) {
        work.addAll(_deps); // Re-Apply
        // Merge update lists, for future unions
        if( that._deps==null && that.is_leaf() ) that._deps = _deps;
        else
          for( Syntax dep : _deps ) that.push_update(dep);
        _deps = null;
      }
      if( _args.length==0 ) _args = new T2[1];
      // Unify the two base types, preserving errors
      if( !that.is_err() )
        that._t = _t.meet(that._t);
      _args[0] = that;         // U-F update
      if( _name.charAt(0)!='V' ) _name = "V"+_uid; // Flag as a leaf & unified
      assert !no_uf();
      return true;
    }

    // -----------------
    // Structural unification.
    // Returns false if no-change, true for change.
    // If work is null, does not actually change anything, just reports progress.
    // If work and change, unifies 'this' into 'that' (changing both), and
    // updates the worklist.
    static private final HashMap<Long,T2> DUPS = new HashMap<>();
    boolean unify( T2 that, Worklist work ) {
      if( this==that ) return false;
      assert DUPS.isEmpty();
      boolean progress = _unify(that,work);
      DUPS.clear();
      return progress;
    }

    // Structural unification, 'this' into 'that'.  No change if just testing
    // (work is null) and returns 'that' if progress.  If updating, both 'this'
    // and 'that' are the same afterwards.
    private boolean _unify(T2 that, Worklist work) {
      assert no_uf() && that.no_uf();
      if( this==that ) return false;

      // two errs union in either order, so keep lower uid (actually should merge error strings)
      if( is_err() && that.is_err() && _uid<that._uid ) return that.union(this,work);
      if(      is_err() ) return that.union(this,work);
      if( that.is_err() ) return      union(that,work);

      // two leafs union in either order, so keep lower uid
      if( is_leaf() && that.is_leaf() && _uid<that._uid ) return that.union(this,work);
      if(      is_leaf() && (     _t==Type.ANY ||      _t==Type.XNIL)) return      union(that,work);
      if( that.is_leaf() && (that._t==Type.ANY || that._t==Type.XNIL)) return that.union(this,work);
      if( is_leaf() && that.is_leaf() ) return union(that,work);

      // Cycle check
      long luid = dbl_uid(that);    // long-unique-id formed from this and that
      T2 rez = DUPS.get(luid);
      assert rez==null || rez==that;
      if( rez!=null ) return false; // Been there, done that
      DUPS.put(luid,that);          // Close cycles

      if( work==null ) return true; // Here we definitely make progress; bail out early if just testing

      if( !Util.eq(_name,that._name) )
        return union_err(that,work,"Cannot unify "+this.p()+" and "+that.p());
      assert _args!=that._args; // Not expecting to share _args and not 'this'

      // Structural recursion unification.

      // Structs unify only on matching fields, and add missing fields.
      if( is_struct() ) {
        // Unification for structs is more complicated; args are aligned via
        // field names and not by position.
        for( int i=0; i<_ids.length; i++ ) { // For all fields in LHS
          int idx = Util.find(that._ids,_ids[i]);
          if( idx==-1 ) that.add_fld(_ids[i],args(i), work); // Extend 'that' with matching field from 'this'
          else args(i)._unify(that.args(idx),work);    // Unify matching field
          that = that.find();                          // Recursively, might have already rolled this up
        }
        // Fields in RHS and not the LHS do not need to be added to the RHS.

        // Memory add missing fields
      } else if( is_mem() ) {
      //  for( int i=0; i<_args.length; i++ ) // For all fields in LHS
      //    if( _args[i]!=null )
      //      that.unify_rec(i,args(i),work);
        throw unimpl();

        // Normal structural unification
      } else {
        for( int i=0; i<_args.length; i++ ) // For all fields in LHS
          args(i)._unify(that.args(i),work);
      }
      if( find().is_err() && !that.find().is_err() )
        return that.find().union(find(),work); // Preserve errors
        // TODO: Find a more elegant way to preserve errors
      return find().union(that,work);
    }

    private void add_fld(String id, T2 fld, Worklist work) {
      assert is_struct();
      int len = _ids.length;
      _ids  = Arrays.copyOf( _ids,len+1);
      _args = Arrays.copyOf(_args,len+1);
      _ids [len] = id ;
      _args[len] = fld;
      work.addAll(_deps); //
    }

    private long dbl_uid(T2 t) { return ((long)_uid<<32)|t._uid; }

    private boolean unify_base(T2 that, Worklist work) {
      Type t = _t.meet(that._t);
      if( t==that._t ) return false; // No progress
      if( work==null ) return true;
      that._t = t;              // Yes progress, but no update if null work
      _args = new T2[1];        // Room for a forwarding pointer
      _t=null;                  // Unified
      return union(that,work);
    }
    private boolean fresh_base(T2 that, Worklist work) {
      Type t = _t.meet(that._t);
      if( t==that._t ) return false; // No progress
      if( work==null ) return true;
      that._t = t;          // Yes progress, but no update if null work
      that.add_deps_work(work);
      return true;
    }
    private boolean union_err(T2 that, Worklist work, String msg) {
      union(that,work);
      return that.union(make_err(msg),work);
    }

    // -----------------
    // Make a (lazy) fresh copy of 'this' and unify it with 'that'.  This is
    // the same as calling 'fresh' then 'unify', without the clone of 'this'.
    // The Syntax is used when making the 'fresh' copy for the occurs_check;
    // it is another version of the 'nongen' set.
    // Returns progress.
    // If work is null, we are testing only and make no changes.
    static private final HashMap<T2,T2> VARS = new HashMap<>();
    boolean fresh_unify(T2 that, VStack nongen, Worklist work) {
      assert VARS.isEmpty() && DUPS.isEmpty();
      int old = CNT;
      boolean progress = _fresh_unify(that,nongen,work);
      VARS.clear();  DUPS.clear();
      if( work==null && old!=CNT && DEBUG_LEAKS )
        throw unimpl("busted, made T2s but just testing");
      return progress;
    }

    // Outer recursive version, wraps a VARS check around other work
    private boolean _fresh_unify(T2 that, VStack nongen, Worklist work) {
      assert no_uf() && that.no_uf();
      T2 prior = VARS.get(this);
      if( prior!=null )         // Been there, done that
        return prior.find()._unify(that,work);  // Also 'prior' needs unification with 'that'
      if( cycle_equals(that) ) return vput(that,false);

      if( that.is_err() ) return vput(that,false); // That is an error, ignore 'this' and no progress
      if( this.is_err() ) return vput(that,_unify(that,work));

      // Attempting to pre-compute occurs_in, by computing 'is_fresh' in the
      // Ident.hm() call does NOT work.  The 'is_fresh' is for the top-layer
      // only, not the internal layers.  As soon as we structural recurse down
      // a layer, 'is_fresh' does not correlate with an occurs_in check.
      if( nongen_in(nongen) ) return vput(that,_unify(that,work)); // Famous 'occurs-check', switch to normal unify
      if( this.is_leaf() ) return vput(that,fresh_base(that,work));
      if( that.is_leaf() && that._t==Type.ANY )  // RHS is a tvar; union with a deep copy of LHS
        return work==null || vput(that,that.union(_fresh(nongen),work));

      if( !Util.eq(_name,that._name) ||
          (!is_struct() && _args.length != that._args.length) )
        return work == null || vput(that,that._unify(make_err("Cannot unify "+this.p()+" and "+that.p()),work));

      // Structural recursion unification, lazy on LHS
      vput(that,false); // Early set, to stop cycles
      boolean progress = false;
      if( is_struct() )
        progress = _fresh_unify_struct(that,nongen,work);
      else {
        for( int i=0; i<_args.length; i++ ) {
          progress |= args(i)._fresh_unify(that.args(i),nongen,work);
          if( progress && work==null ) return true;
        }
      }
      return progress;
    }

    // Unification with structs must honor field names.
    private boolean _fresh_unify_struct(T2 that, VStack nongen, Worklist work) {
      assert is_struct() && that.is_struct();
      boolean progress = false;
      for( int i=0; i<_args.length; i++ ) {
        int idx = Util.find(that._ids,_ids[i]);
        if( idx == -1 ) {       // Missing field on RHS
          if( work==null ) return true; // Will definitely make progress
          progress = true;
          that.add_fld(_ids[i],args(i)._fresh(nongen), work);
        } else
          progress |= args(i)._fresh_unify(that.args(idx),nongen,work);
        if( progress && work==null ) return true;
      }
      // Fields in RHS and not the LHS do not need to be added to the RHS.
      Type t = _t.meet(that._t);
      if( that._t != t ) progress = true; // Base types differ
      that._t = t;
      return progress;
    }

    private boolean vput(T2 that, boolean progress) { VARS.put(this,that); return progress; }

    // Return a fresh copy of 'this'
    private T2 _fresh(VStack nongen) {
      assert no_uf();
      T2 rez = VARS.get(this);
      if( rez!=null ) return rez; // Been there, done that

      if( is_leaf() ) {
        // If occurs_in lexical scope, keep same variable, else make a new leaf
        T2 t = nongen_in(nongen) ? this : T2.make_leaf(_t);
        VARS.put(this,t);
        return t;
      } else {                  // Structure is deep-replicated
        T2 t = copy();
        VARS.put(this,t);       // Stop cyclic structure looping
        for( int i=0; i<_args.length; i++ )
          t._args[i] = args(i)._fresh(nongen);
        return t;
      }
    }

    // -----------------
    private static final VBitSet ODUPS = new VBitSet();
    boolean occurs_in(Syntax syn) {
      if( syn==null ) return false;
      assert ODUPS.isEmpty();
      boolean found = _occurs_in(syn);
      ODUPS.clear();
      return found;
    }
    boolean occurs_in_type(T2 x) {
      assert ODUPS.isEmpty();
      boolean found = _occurs_in_type(x);
      ODUPS.clear();
      return found;
    }
    boolean _occurs_in(Syntax syn) {
      for( ; syn!=null; syn=syn._par )
        if( _occurs_in_type(syn.find()) )
          return true;
      return false;
    }

    boolean _occurs_in_type(T2 x) {
      assert no_uf() && x.no_uf();
      if( x==this ) return true;
      if( ODUPS.tset(x._uid) ) return false; // Been there, done that
      if( !x.is_leaf() )
        for( int i=0; i<x._args.length; i++ )
          if( _occurs_in_type(x.args(i)) )
            return true;
      return false;
    }

    boolean nongen_in(VStack syn) {
      if( syn==null ) return false;
      assert ODUPS.isEmpty();
      boolean found = _nongen_in(syn);
      ODUPS.clear();
      return found;
    }
    boolean _nongen_in(VStack nongen) {
      for( T2 t2 : nongen )
        if( _occurs_in_type(t2.find()) )
          return true;
      return false;
    }

    // -----------------
    // Test for structural equivalence, including cycles
    static private final HashMap<T2,T2> CDUPS = new HashMap<>();
    boolean cycle_equals(T2 t) {
      assert CDUPS.isEmpty();
      boolean rez = _cycle_equals(t);
      CDUPS.clear();
      return rez;
    }
    boolean _cycle_equals(T2 t) {
      assert no_uf() && t.no_uf();
      if( this==t ) return true;
      if( is_leaf() && t.is_leaf() && _t!=Type.ANY )
        return _t==t._t;        // Base-cases have to be completely identical
      if( !Util.eq(_name,t._name) ||       // Wrong type-var names
          _args.length != t._args.length ) // Mismatched sizes
        return false;
      if( _args==t._args ) return true;
      // Cycles stall the equal/unequal decision until we see a difference.
      T2 tc = CDUPS.get(this);
      if( tc!=null )
        return tc==t; // Cycle check; true if both cycling the same
      CDUPS.put(this,t);
      if( is_struct() )         // Struct equality honors field names without regard to order
        return _cycle_equals_struct(t);
      for( int i=0; i<_args.length; i++ )
        if( !args(i)._cycle_equals(t.args(i)) )
          return false;
      return true;
    }

    private boolean _cycle_equals_struct(T2 t) {
      assert is_struct() && t.is_struct();
      if( _t!=t._t ) return false; // Aliases have to be equal
      for( int i=0; i<_args.length; i++ ) {
        int idx = Util.find(t._ids,_ids[i]);
        if( idx==-1 || !args(i)._cycle_equals(t.args(idx)) )
          return false;
      }
      assert _t==t._t;
      return true;
    }

    // Unify 'str' at alias 'alias' in 'this' memory.
    void unify_rec( int alias, T2 str, Worklist work) {
      assert is_mem() && str.is_struct();
      while( alias >= _args.length )
        _args = Arrays.copyOf(_args,_args.length<<1);
      if( _args[alias] != null ) {
        args(alias).unify(str, work);
        return;
      }
      if( work!=null ) _args[alias] = str;
    }

    // -----------------
    // This is a T2 function that is the target of 'fresh', i.e., this function
    // might be fresh-unified with some other function.  Push the application
    // down the function parts; if any changes the fresh-application may make
    // progress.
    static final VBitSet UPDATE_VISIT  = new VBitSet();
    T2 push_update( Ary<Syntax> as ) { if( as != null ) for( Syntax a : as ) push_update(a);  return this;   }
    void push_update( Syntax a) { assert UPDATE_VISIT.isEmpty(); push_update_impl(a); UPDATE_VISIT.clear(); }
    private void push_update_impl(Syntax a) {
      assert no_uf();
      if( UPDATE_VISIT.tset(_uid) ) return;
      if( _deps==null ) _deps = new Ary<>(Syntax.class);
      if( _deps.find(a)==-1 ) _deps.push(a);
      for( int i=0; i<_args.length; i++ )
        if( _args[i]!=null )
          args(i).push_update_impl(a);
    }

    void add_deps_work( Worklist work ) { assert UPDATE_VISIT.isEmpty(); add_deps_work_impl(work); UPDATE_VISIT.clear(); }
    private void add_deps_work_impl( Worklist work ) {
      if( is_leaf() || _args.length==0 ) {
        work.addAll(_deps);
      } else {
        if( UPDATE_VISIT.tset(_uid) ) return;
        for( int i=0; i<_args.length; i++ )
          args(i).add_deps_work_impl(work);
      }
    }

    // -----------------
    // Glorious Printing

    // Look for dups, in a tree or even a forest (which Syntax.p() does)
    VBitSet get_dups(VBitSet dups) { return _get_dups(new VBitSet(),dups); }
    VBitSet _get_dups(VBitSet visit, VBitSet dups) {
      if( visit.tset(_uid) ) {
        if( no_uf() ) dups.set(_uid);
      } else
        for( T2 t : _args )
          if( t!=null )
            t._get_dups(visit,dups);
      return dups;
    }

    // Fancy print for Debuggers - includes explicit U-F re-direction.
    // Does NOT roll-up U-F, has no side-effects.
    @Override public String toString() { return str(new SB(), new VBitSet(), get_dups(new VBitSet()) ).toString(); }
    SB str(SB sb, VBitSet visit, VBitSet dups) {
      if( is_err() ) return sb.p(_t.getstr());
      boolean dup = dups.get(_uid);
      if( is_leaf() ) {
        if( !dup ) sb.p(_name).p(':');
        sb.p(_t);
        return _args.length==0 || _args[0]==null ? sb : _args[0].str(sb.p(">>"), visit, dups);
      }
      if( dup ) sb.p("$V").p(_uid);
      if( visit.tset(_uid) && dup ) return sb;
      if( dup ) sb.p(':');

      // Special printing for functions
      if( is_fun() ) {
        sb.p("{ ");
        for( int i=0; i<_args.length-1; i++ )
          str(sb,visit,_args[i],dups).p(" ");
        return str(sb.p("-> "),visit,_args[_args.length-1],dups).p(" }");
      }

      // Special printing for structures
      if( is_struct() ) {
        sb.p("@{");
        for( int i=0; i<_ids.length; i++ )
          str(sb.p(' ').p(_ids[i]).p(" = "),visit,_args[i],dups).p(',');
        sb.unchar().p("}");
        sb.p(':').p(_t);
        return sb.p(((TypeMemPtr)_t)._aliases.toString());
      }

      // Special printing for memory
      if( is_mem() ) {
        sb.p("[  ");
        for( int i=0; i<_args.length; i++ )
          if( _args[i] != null )
            _args[i].str(sb.p(i).p(':'),visit,dups).p(", ");
        return sb.unchar(2).p("]");
      }

      // Generic structural T2
      sb.p("(").p(_name).p(" ");
      for( T2 t : _args ) str(sb,visit,t,dups).p(" ");
      return sb.unchar().p(")");
    }
    static private SB str(SB sb, VBitSet visit, T2 t, VBitSet dups) { return t==null ? sb.p("_") : t.str(sb,visit,dups); }

    // Same as toString but calls find().  Can thus side-effect & roll-up U-Fs, so not a toString
    public String p() { return p(get_dups(new VBitSet())); }
    private static int VCNT;
    private static final HashMap<T2,Integer> VNAMES = new HashMap<>();
    String p(VBitSet dups) { VCNT=0; VNAMES.clear(); return find()._p(new SB(), new VBitSet(), dups).toString(); }
    private SB _p(SB sb, VBitSet visit, VBitSet dups) {
      assert no_uf();
      if( is_leaf() || dups.get(_uid) ) { // Leafs or Duplicates?  Take some effort to pretty-print cycles
        if( is_leaf() && _t!=Type.ANY ) return sb.p(_t); // One-shot bases just do type
        Integer ii = VNAMES.get(this);
        if( ii==null )  VNAMES.put(this,ii=VCNT++); // Type-var name
        // 2nd and later visits use the short form
        boolean later = visit.tset(_uid);
        if( later ) sb.p('$');
        char c = (char)('A'+ii);
        if( c<'V' ) sb.p(c); else sb.p("V"+ii);
        if( later ) return sb;
        if( is_leaf() ) return sb;
        sb.p(':'); // Dups now print their structure
      }
      if( is_err () ) return sb.p(_t);

      // Special printing for functions: { arg -> body }
      if( is_fun() ) {
        sb.p("{ ");
        for( int i=0; i<_args.length-1; i++ )
          args(i)._p(sb,visit,dups).p(" ");
        return args(_args.length-1)._p(sb.p("-> "),visit,dups).p(" }");
      }

      // Special printing for structures: @{ fld0 = body, fld1 = body, ... }
      if( is_struct() ) {
        boolean is_tuple=true;
        for( String id : _ids )
          if( !isDigit((byte) id.charAt(0)) )
            { is_tuple = false; break; }
        if( is_tuple ) {
          sb.p('(');
          for( int i=0; i<_ids.length; i++ ) {
            int idx = Util.find(_ids,new String(new char[]{(char)('0'+i)}).intern());
            args(idx)._p(sb.p(' '),visit,dups).p(',');
          }
          sb.unchar().p(')');

        } else {
          sb.p("@{");
          for( int i=0; i<_ids.length; i++ )
            args(i)._p(sb.p(' ').p(_ids[i]).p(" = "),visit,dups).p(',');
          sb.unchar().p("}");
        }
        return sb.p(((TypeMemPtr)_t)._aliases.toString());
      }

      // Special printing for memory
      if( is_mem() ) {
        sb.p("[  ");
        for( int i=0; i<_args.length; i++ )
          if( _args[i] != null )
            args(i)._p(sb.p(i).p(':'),visit,dups).p(", ");
        return sb.unchar(2).p("]");
      }

      // Generic structural T2: (fun arg0 arg1...)
      sb.p("(").p(_name).p(" ");
      for( int i=0; i<_args.length; i++ ) args(i)._p(sb,visit,dups).p(" ");
      return sb.unchar().p(")");
    }

    static void reset() { CNT=0; DUPS.clear(); VARS.clear(); ODUPS.clear(); CDUPS.clear(); UPDATE_VISIT.clear(); }
  }

}
