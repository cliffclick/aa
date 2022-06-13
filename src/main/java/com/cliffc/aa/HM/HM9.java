package com.cliffc.aa.HM;

import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;
import org.jetbrains.annotations.NotNull;

import java.util.*;

import static com.cliffc.aa.AA.unimpl;

// Combined Hindley-Milner and Global Constant Propagation typing.

// Complete stand-alone, for research.

// Treats HM as a Monotone Analysis Framework; converted to a worklist style.
// The type-vars are monotonically unified, gradually growing over time - and
// this is treated as the MAF lattice.  Some of the normal Algo-W work gets
// done in a prepass; e.g. discovering identifier sources (SSA form), and
// building the non-generative set.  Because of the non-local unification
// behavior type-vars include a "dependent Syntax" set; a set of Syntax
// elements put back on the worklist if this type unifies, beyond the expected
// parent and AST children.
//
// The normal HM unification steps are treated as the MAF transfer "functions",
// taking type-vars as inputs and producing new, unified, type-vars.  Because
// unification happens in-place (normal Tarjan disjoint-set union), the xfer
// "functions" are executed for side-effects only, and return a progress flag.
// The transfer functions are virtual calls on each Syntax element.  Some of
// the steps are empty because of the pre-pass (Let,Con).

// HM Bases include anything from the GCP lattice, but 'widened' to form
// borders between e.g. ints and pointers.  Includes polymorphic structures and
// fields (structural typing not duck typing), polymorphic nil-checking and an
// error type-var.  Both HM and GCP types fully support recursive types.
//
// Unification typically makes many many temporary type-vars and immediately
// unifies them.  For efficiency, this algorithm checks to see if unification
// requires an allocation first, instead of just "allocate and unify".  The
// major place this happens is identifiers, which normally make a "fresh" copy
// of their type-var, then unify.  I use a combined "make-fresh-and-unify"
// unification algorithm there.  It is a structural clone of the normal unify,
// except that it lazily makes a fresh-copy of the left-hand-side on demand
// only; typically discovering that no fresh-copy is required.
//
// To engineer and debug the algorithm, the unification step includes a flag to
// mean "actually unify, and report a progress flag" vs "report if progress".
// The report-only mode is aggressively asserted for in the main loop; all
// Syntax elements that can make progress are asserted as on the worklist.
//
// GCP gets the normal MAF treatment, no surprises there.
//
// The combined algorithm includes transfer functions taking facts from both
// MAF lattices, producing results in the other lattice.

// For the GCP->HM direction, the HM 'if' has a custom transfer function
// instead of the usual one.  Unification looks at the GCP value, and unifies
// either the true arm, or the false arm, or both or neither.  In this way GCP
// allows HM to avoid picking up constraints from dead code.

// For the HM->GCP direction, the GCP 'apply' has a customer transfer function
// where the result from a call gets lifted (JOINed) based on the matching GCP
// inputs - and the match comes from using the same HM type-var on both inputs
// and outputs.  This allows e.g. "map" calls which typically merge many GCP
// values at many applies (call sites) and thus end up typed as a Scalar to
// Scalar, to improve the GCP type on a per-call-site basis.
//
// Test case 45 demonstrates this combined algorithm, with a program which can
// only be typed using the combination of GCP and HM.

public class HM9 {
  // Mapping from primitive name to PrimSyn
  static final HashMap<String,PrimSyn> PRIMSYNS = new HashMap<>();

  static final boolean DEBUG_LEAKS=false;
  static { BitsAlias.init0(); BitsFun.init0(); }

  static final boolean DO_HM  = true;
  static final boolean DO_GCP = true;

  public static Root hm( String sprog ) {
    Worklist work = new Worklist();
    PrimSyn.WORK=work;

    for( PrimSyn prim : new PrimSyn[]{new If(), new Pair1(), new Pair(), new EQ(), new EQ0(), new Mul(), new Dec(), new Str(), new Triple(), new Factor(), new IsEmpty(), new NotNil()} )
      PRIMSYNS.put(prim.name(),prim);

    // Parse
    Root prog = parse( sprog );

    // Prep for SSA: pre-gather all the (unique) ids
    int cnt_syns = prog.prep_tree(null,null,work);
    int init_T2s = T2.CNT;

    while( work.len()>0 ) {     // While work
      int oldcnt = T2.CNT;      // Used for cost-check when no-progress
      assert work._cnt<1000;
      Syntax syn = work.pop();  // Get work
      if( DO_HM ) {
        T2 old = syn._hmt;        // Old value for progress assert
        if( syn.hm(work) ) {
          assert !syn.debug_find().unify(old.find(),null);// monotonic: unifying with the result is no-progress
          syn.add_hm_work(work);     // Push affected neighbors on worklist
        } else {
          assert !DEBUG_LEAKS || oldcnt==T2.CNT;  // No-progress consumes no-new-T2s
        }
      }
      if( DO_GCP ) {
        Type old = syn._flow;
        Type t = syn.val(work);
        if( t!=old ) {           // Progress
          assert old.isa(t);     // Monotonic falling
          syn._flow = t;         // Update type
          if( syn._par!=null ) { // Generally, parent needs revisit
            work.push(syn._par); // Assume parent needs revisit
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
    BitsAlias.reset_to_init0();
    BitsFun.reset_to_init0();
    PRIMSYNS.clear();
    Pair1.PAIR1S.clear();
    Lambda.FUNS.clear();
    T2.reset();
    PrimSyn.reset();
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
    // Inject IF at root
    return new Root(prog);
  }
  static Syntax term() {
    if( skipWS()==-1 ) return null;
    if( isDigit(BUF[X]) ) return number();
    if( BUF[X]=='"' ) return string();

    if( BUF[X]=='(' ) {         // Parse an Apply
      X++;                      // Skip paren
      Syntax fun = term();
      Ary<Syntax> args = new Ary<>(new Syntax[1],0);
      while( skipWS()!= ')' && X<BUF.length ) args.push(term());
      require(')');
      // Guarding if-nil test inserts an upcast.  This is a syntatic transform only.
      if( fun instanceof If &&
          args.at(0) instanceof Ident ) {
        Ident id = (Ident)args.at(0);
        args.set(1,new Apply(new Lambda(args.at(1), id._name),
                             new Apply(new NotNil(),new Ident(id._name))));
      }
      return new Apply(fun,args.asAry());
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
      if( skipWS()!='=' ) {
        PrimSyn prim = PRIMSYNS.get(id); // No shadowing primitives or this lookup returns the prim instead of the shadow
        return prim==null ? new Ident(id) : prim.make(); // Make a prim copy with fresh HM variables
      }
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

    // Field lookup is prefix or backwards: ".x term" instead of "term.x"
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
    if( BUF[X]=='0' ) { X++; return new Con(TypeNil.NIL); }
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
    //return require('"', new Con(TypeMemPtr.make(BitsAlias.STRBITS,TypeStr.con(new String(BUF,start,X-start).intern()))));
    throw unimpl();
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
    public int _cnt;                                          // Count of items ever popped (not the current length)
    private final Ary<Syntax> _ary = new Ary<>(Syntax.class); // For picking random element
    private final HashSet<Syntax> _work = new HashSet<>();    // For preventing dups
    public int len() { return _ary.len(); }
    public void push(Syntax s) { if( s!=null && !_work.contains(s) ) _work.add(_ary.push(s)); }
    public Syntax pop() { Syntax s = _ary.pop();_cnt++;            _work.remove(s); return s; }
    //public Syntax pop() { Syntax s = _ary.del(  _cnt++%_ary._len); _work.remove(s); return s; }
    public boolean has(Syntax s) { return _work.contains(s); }
    public void addAll(Ary<? extends Syntax> ss) { if( ss != null ) for( Syntax s : ss ) push(s); }
    public void clear() {
      _cnt=0;
      _ary.clear();
      _work.clear();
    }
    @Override public String toString() { return _ary.toString(); }
  }

  // ---------------------------------------------------------------------
  // Small classic tree of T2s, immutable, with sharing at the root parts.
  static class VStack implements Iterable<T2> {
    final VStack _par;
    private T2 _nongen;
    final int _d;
    VStack( VStack par, T2 nongen ) { _par=par; _nongen=nongen; _d = par==null ? 0 : par._d+1; }
    T2 nongen() {
      T2 n = _nongen.find();
      return n==_nongen ? n : (_nongen=n);
    }
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
      @Override public T2 next() { T2 v = _vstk.nongen(); _vstk = _vstk._par;  return v; }
    }
  }

  // ---------------------------------------------------------------------
  static abstract class Syntax {
    Syntax _par;                // Parent in the AST
    VStack _nongen;             // Non-generative type variables
    T2 _hmt;                    // Current HM type
    T2 find() {                 // U-F find
      T2 t = _hmt.find();
      return t== _hmt ? t : (_hmt =t);
    }
    T2 debug_find() { return _hmt.debug_find(); } // Find, without the roll-up

    // Dataflow types.  Varies during a run of GCP.
    Type _flow;

    // Compute a new HM type.
    // If no change, return false.
    // If a change, return always true, however:
    // - If 'work' is null do not change/set anything.
    // - If 'work' is available, update the worklist.
    abstract boolean hm(Worklist work);

    abstract void add_hm_work(Worklist work); // Add affected neighbors to worklist

    // Compute and return (and do not set) a new GCP type for this syntax.
    abstract Type val(Worklist work);

    void add_val_work(Syntax child, Worklist work) {} // Add affected neighbors to worklist

    // First pass to "prepare" the tree; does e.g. Ident lookup, sets initial
    // type-vars and counts tree size.
    abstract int prep_tree(Syntax par, VStack nongen, Worklist work);
    final void prep_tree_impl( Syntax par, VStack nongen, Worklist work, T2 t ) {
      _par = par;
      _hmt = t;
      _flow= TypeNil.XSCALAR;
      _nongen = nongen;
      work.push(this);
    }
    void prep_lookup_deps(Ident id) {}

    // Giant Assert: True if OK; all Syntaxs off worklist do not make progress
    abstract boolean more_work(Worklist work);
    final boolean more_work_impl(Worklist work) {
      if( work.has(this) ) return true;
      if( DO_HM && hm(null) )   // Any more HM work?
        return false;           // Found HM work not on worklist
      if( DO_GCP && val(null)!=_flow )
        return false;           // Found GCP work not on worklist
      return true;
    }
    // Print for debugger
    @Override final public String toString() { return str(new SB()).toString(); }
    abstract SB str(SB sb);
    // Line-by-line print with more detail
    public String p() { return p0(new SB(), new VBitSet()).toString(); }
    final SB p0(SB sb, VBitSet dups) {
      _hmt.get_dups(dups);
      VBitSet visit = new VBitSet();
      p1(sb.i());
      if( DO_HM  ) _hmt .str(sb.p(", HM="), visit,dups);
      if( DO_GCP ) _flow.str(sb.p(", CCP="), false, false);
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
    @Override SB p1(SB sb) { return sb.p(_con.toString()); }
    @Override SB p2(SB sb, VBitSet dups) { return sb; }
    @Override boolean hm(Worklist work) { return false; }
    @Override Type val(Worklist work) { return _con; }
    @Override void add_hm_work(Worklist work) { }
    @Override int prep_tree( Syntax par, VStack nongen, Worklist work ) {
      prep_tree_impl(par, nongen, work, T2.make_base(_con));
      return 1;
    }
    @Override boolean more_work(Worklist work) { return more_work_impl(work); }
  }


  static class Ident extends Syntax {
    final String _name;         // The identifier name
    Syntax _def;                // Cached syntax defining point
    int _idx;                   // Index in Lambda (which arg of many)
    T2 _idt;                    // Cached type var for the name in scope
    Ident(String name) { _name=name; }
    @Override SB str(SB sb) { return p1(sb); }
    @Override SB p1(SB sb) { return sb.p(_name); }
    @Override SB p2(SB sb, VBitSet dups) { return sb; }
    T2 idt() {
      T2 idt = _idt.find();
      return idt==_idt ? idt : (_idt=idt);
    }
    @Override boolean hm(Worklist work) {
      return idt().fresh_unify(find(),_nongen,work);
    }
    @Override void add_hm_work(Worklist work) {
      work.push(_par);
      T2 t = idt();
      if( t.nongen_in(_par == null ? null : _par._nongen) ) // Got captured in some parent?
        t.add_deps_work(work);                              // Need to revisit dependent ids
      if( _par instanceof Apply && ((Apply)_par)._fun instanceof NotNil )
        work.push(((Apply)_par)._fun);
    }
    @Override Type val(Worklist work) {
      return _def instanceof Let ? ((Let)_def)._def._flow : ((Lambda)_def)._types[_idx];
    }
    @Override int prep_tree( Syntax par, VStack nongen, Worklist work ) {
      prep_tree_impl(par,nongen,work,T2.make_leaf());
      for( Syntax syn = _par; syn!=null; syn = syn._par )
        syn.prep_lookup_deps(this);

      // Lookup, and get the T2 type var and a pointer to the flow type.
      for( Syntax syn = _par; syn!=null; syn = syn._par ) {
        if( syn instanceof Lambda ) {
          Lambda lam = (Lambda)syn;
          if( (_idx = Util.find(lam._args,_name)) != -1 )
            return _init(lam,lam.targ(_idx));
        } else if( syn instanceof Let ) {
          Let let = (Let)syn;  _idx=-1;
          if( Util.eq(let._arg0,_name) )
            return _init(let,let._targ);
        }
      }
      throw new RuntimeException("Parse error, "+_name+" is undefined");
    }
    private int _init(Syntax def,T2 idt) { _def = def; _idt = idt; return 1; }
    @Override boolean more_work(Worklist work) { return more_work_impl(work); }
  }


  static class Lambda extends Syntax {
    // Map from FIDXs to Lambdas
    static final NonBlockingHashMapLong<Lambda> FUNS = new NonBlockingHashMapLong<>();
    final String[] _args;
    final Syntax _body;
    final T2[] _targs;
    final Type[] _types;
    final int _fidx;

    Lambda(Syntax body, String... args) {
      _args=args;
      _body=body;
      // Type variables for all arguments
      _targs = new T2[args.length];
      for( int i=0; i<args.length; i++ ) _targs[i] = T2.make_leaf();
      // Flow types for all arguments
      _types = new Type[args.length];
      for( int i=0; i<args.length; i++ ) _types[i] = TypeNil.XSCALAR;
      // A unique FIDX for this Lambda
      _fidx = BitsFun.new_fidx();
      FUNS.put(_fidx,this);
      _flow = val(null);
    }
    @Override SB str(SB sb) {
      sb.p("{ ");
      for( String arg : _args ) sb.p(arg).p(' ');
      return _body.str(sb.p("-> ")).p(" }");
    }
    @Override SB p1(SB sb) {
      sb.p("{ ");
      for( int i=0; i<_args.length; i++ ) {
        sb.p(_args[i]);
        if( DO_HM  ) sb.p(", HM=" ).p(targ(i).toString());
        if( DO_GCP ) sb.p(", CCP=").p(_types[i]);
        sb.nl().i().p("  ");
      }
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
      T2 fun = T2.make_fun(BitsFun.make0(_fidx),targs);
      return old.unify(fun,work);
    }
    @Override void add_hm_work(Worklist work) {
      work.push(_par );
      work.push(_body);
      for( int i=0; i<_targs.length; i++ )
        if( targ(i).occurs_in_type(find()) ) work.addAll(targ(i)._deps);
    }
    @Override Type val(Worklist work) { return TypeFunPtr.make(_fidx,_args.length,Type.ANY,TypeNil.SCALAR); }
    // Ignore arguments, and return body type.  Very conservative.
    Type apply(Syntax[] args) { return _body._flow; }
    @Override void add_val_work(Syntax child, Worklist work) {
      // Body changed, all Apply sites need to recompute
      work.addAll(find()._deps);
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
    @Override boolean hm(Worklist work) { return false;  }
    @Override void add_hm_work(Worklist work) {
      work.push(_par);
      work.push(_body);
      work.push(_def);
      work.addAll(_def.find()._deps);
    }
    @Override Type val(Worklist work) { return _body._flow; }
    @Override void add_val_work(Syntax child, Worklist work) {
      if( child==_def )
        work.addAll(_def.find()._deps);
    }

    @Override int prep_tree( Syntax par, VStack nongen, Worklist work ) {
      prep_tree_impl(par,nongen,work,_body._hmt);
      int cnt = _body.prep_tree(this,           nongen       ,work) +
                _def .prep_tree(this,new VStack(nongen,_targ),work);
      _hmt = _body._hmt;            // Unify 'Let._hmt' with the '_body'
      _targ.unify(_def.find(),work);
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
        BitsAlias aliases = str._alias;
        if( !aliases.test(0) ) {
          str._alias = str._alias.meet_nil(); // Nil is allowed on the tested value
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
        T2 nfun = T2.make_fun(BitsFun.NALL,targs);
        progress = tfun.unify(nfun,work);
        return tfun.find().is_err() ? find().unify(tfun.find(),work) : progress;
      }

      if( tfun._args.length != _args.length+1 )
        progress |= T2.make_err("Mismatched argument lengths").unify(find(),work);
      // Check for progress amongst arg pairs
      for( int i=0; i<_args.length; i++ ) {
        progress |= tfun.args(i).unify(_args[i].find(),work);
        if( progress && work==null ) return true; // Will-progress & just-testing early exit
        if( (tfun=tfun.find()).is_err() ) return find().unify(tfun,work);
      }
      // Check for progress on the return
      progress |= tfun.args(_args.length).unify(find(),work);
      if( (tfun=tfun.find()).is_err() ) return find().unify(tfun,work);

      return progress;
    }
    @Override void add_hm_work(Worklist work) {
      work.push(_par);
      for( Syntax arg : _args ) work.push(arg);
    }
    static private final HashMap<T2,Type> T2MAP = new HashMap<>();
    static private final NonBlockingHashMapLong<String> WDUPS = new NonBlockingHashMapLong<>();
    @Override Type val(Worklist work) {
      Type flow = _fun._flow;
      if( flow.above_center() ) return TypeNil.XSCALAR;
      if( !(flow instanceof TypeFunPtr) ) return TypeNil.SCALAR;
      TypeFunPtr tfp = (TypeFunPtr)flow;
      // Have some functions, meet over their returns.
      Type rez = TypeNil.XSCALAR;
      if( tfp._fidxs==BitsFun.NALL ) rez = TypeNil.SCALAR;
      else
        for( int fidx : tfp._fidxs )
          rez = rez.meet(Lambda.FUNS.get(fidx).apply(_args));
      if( rez==TypeNil.XSCALAR ) // Fast path cutout, no improvement possible
        return rez;

      // Attempt to lift the result, based on HM types.  Walk the input HM type
      // and CCP flow type in parallel and create a mapping.  Then walk the
      // output HM type and CCP flow type in parallel, and join output CCP
      // types with the matching input CCP type.
      if( DO_HM ) {
        T2MAP.clear();  WDUPS.clear();
        // Walk the inputs, building a mapping
        _fun.find().walk_types_in(_fun._flow);
        for( Syntax arg : _args )
          { WDUPS.clear(); arg.find().walk_types_in(arg._flow); }
        // Walk the outputs, building an improved result
        Type rez2 = find().walk_types_out(rez);
        rez = rez2.join(rez);   // Lift result
        if( !_flow.isa(rez) )
          rez = _flow; // TODO: Cheaty force monotonic
      }
      return rez;
    }
    @Override void add_val_work(Syntax child, Worklist work) {
      // If function changes type, recompute self
      if( child==_fun ) work.push(this);
      // If an argument changes type, adjust the lambda arg types
      Type flow = _fun._flow;
      if( flow.above_center() ) return;
      if( !(flow instanceof TypeFunPtr) ) return;
      // Meet the actuals over the formals.
      for( int fidx : ((TypeFunPtr)flow)._fidxs ) {
        Lambda fun = Lambda.FUNS.get(fidx);
        if( fun!=null ) {
          fun.find().push_update(this); // Discovered as call-site; if the Lambda changes the Apply needs to be revisited.
          for( int i=0; i<fun._types.length; i++ ) {
            Type formal = fun._types[i];
            Type actual = this instanceof Root ? Root.widen(fun.targ(i)) : _args[i]._flow;
            Type rez = formal.meet(actual);
            if( formal != rez ) {
              fun._types[i] = rez;
              work.addAll(fun.targ(i)._deps);
              work.push(fun._body);
              if( i==0 && fun instanceof If ) work.push(fun); // Specifically If might need more unification
            }
          }
        }
      }
    }

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
      return _fun instanceof If && _args[0] instanceof Ident ? _args[0].find() : null;
    }
  }


  static class Root extends Apply {
    Root(Syntax body) { super(body); }
    @Override SB str(SB sb) { return _fun.str(sb); }
    @Override boolean hm(Worklist work) { return find().unify(_fun.find(),work); }
    @Override void add_hm_work(Worklist work) { }
    // Root-widening is when Root acts as-if it is calling the returned
    // function with the worse-case legal args.
    static Type widen(T2 t2) { return t2.as_flow(); }
    private static Type xval(TypeFunPtr fun) {
      Type rez = TypeNil.XSCALAR;
      for( int fidx : fun._fidxs )
        rez = rez.meet(Lambda.FUNS.get(fidx).apply(null));
      return rez;
    }
    @Override Type val(Worklist work) {
      // Here we do some extra work, "as if" our arguments (which only lazily exist)
      // may have had their types change.
      add_val_work(null,work);

      return _fun._flow;
    }
    // Expand functions to full signatures, recursively
    Type flow_type() { return add_sig(_flow); }

    private static Type add_sig(Type t) {
      if( t instanceof TypeFunPtr ) {
        Type rez = add_sig(xval((TypeFunPtr)t));
        //return TypeFunSig.make1(TypeTuple.make_args());
        throw unimpl();
      } else {
        return t;
      }
    }
  }


  // Structure or Records.
  static class Struct extends Syntax {
    final int _alias;
    final String[]  _ids;
    final Syntax[] _flds;
    Struct( String[] ids, Syntax[] flds ) {
      _ids=ids;
      _flds=flds;
      // Make a TMP
      _alias = BitsAlias.new_alias(BitsAlias.ALLX);
    }
    @Override SB str(SB sb) {
      sb.p("@{").p(_alias);
      for( int i=0; i<_ids.length; i++ ) {
        sb.p(' ').p(_ids[i]).p(" = ");
        _flds[i].str(sb);
        if( i < _ids.length-1 ) sb.p(',');
      }
      return sb.p("}");
    }
    @Override SB p1(SB sb) { return sb.p("@{").p(_alias).p(" ... } "); }
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
        T2.make_struct(BitsAlias.make0(_alias),_ids,t2s).unify(rec,work);
        rec=find();
        progress = true;
      }

      // Extra fields are unified with ERR since they are not created here:
      // error to load from a non-existing field
      for( int i=0; i<rec._ids.length; i++ ) {
        if( Util.find(_ids,rec._ids[i])== -1 && !rec.args(i).is_err() ) {
          if( work==null ) return true;
          progress |= rec.args(i).unify(find().miss_field(rec._ids[i]),work);
        }
      }

      // Unify existing fields.  Ignore extras on either side.
      for( int i=0; i<_ids.length; i++ ) {
        int idx = Util.find(rec._ids,_ids[i]);
        if( idx!= -1 ) progress |= rec.args(idx).unify(_flds[i].find(),work);
        if( work==null && progress ) return true;
      }
      rec.push_update(this);

      return progress;
    }
    @Override void add_hm_work(Worklist work) {
      work.push(_par);
      for( Syntax fld : _flds ) work.push(fld);
    }
    @Override Type val(Worklist work) {
      //TypeFld[] ts = TypeFlds.get(_flds.length+1);
      //ts[0] = TypeFld.NO_DISP;
      //for( int i=0; i<_flds.length; i++ )
      //  ts[i+1] = TypeFld.make(_ids[i],_flds[i]._flow,Access.Final,i+1);
      //TypeStruct tstr = TypeStruct.make(ts);
      //TypeStruct t2 = tstr.approx(1,_alias);
      //return TypeMemPtr.make(_alias,t2);
      throw unimpl();
    }

    @Override int prep_tree(Syntax par, VStack nongen, Worklist work) {
      T2[] t2s = new T2[_ids.length];
      prep_tree_impl(par, nongen, work, T2.make_struct(BitsAlias.make0(_alias),_ids,t2s));
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
      if( find().is_err() ) return false; // Already an error; no progress
      T2 rec = _rec.find();
      if( (rec._alias!=null && rec._alias.test(0)) || rec._flow == TypeNil.NIL )
        return find().unify(T2.make_err("May be nil when loading field "+_id),work);
      int idx = rec._ids==null ? -1 : Util.find(rec._ids,_id);
      if( idx!= -1 )            // Unify against a pre-existing field
        return rec.args(idx).unify(find(), work);
      // The remaining cases all make progress and return true
      if( work==null ) return true;
      if( rec.is_err() ) return find().unify(rec,work);
      // Not a struct or no field, force it to be one
      if( rec.is_struct() && rec._open ) // Effectively unify with an extended struct.
        return rec.add_fld(_id,find(),work);
      if( rec.is_leaf() )
        return T2.make_struct(BitsAlias.EMPTY,new String[]{_id}, new T2[]{find().push_update(rec._deps)},true).unify(rec.push_update(this), work);

      return find().unify(rec.miss_field(_id),work);
    }
    @Override void add_hm_work(Worklist work) {
      work.push(_par);
      work.push(_rec);
      _rec.add_hm_work(work);
    }
    @Override Type val(Worklist work) {
      Type trec = _rec._flow;
      if( trec.above_center() ) return TypeNil.XSCALAR;
      if( trec instanceof TypeMemPtr ) {
        TypeMemPtr tmp = (TypeMemPtr)trec;
        if( tmp._obj instanceof TypeStruct ) {
          //TypeStruct tstr = (TypeStruct)tmp._obj;
          //int idx = tstr.fld_find(_id);
          //if( idx!=-1 ) return tstr.at(idx); // Field type
          throw unimpl();
        }
        if( tmp._obj.above_center() ) return TypeNil.XSCALAR;
      }
      // TODO: Need an error type here
      return TypeNil.SCALAR;
    }
    @Override int prep_tree(Syntax par, VStack nongen, Worklist work) {
      prep_tree_impl(par, nongen, work, T2.make_leaf());
      return _rec.prep_tree(this,nongen,work)+1;
    }
    @Override boolean more_work(Worklist work) {
      if( !more_work_impl(work) ) return false;
      return _rec.more_work(work);
    }
  }


  abstract static class PrimSyn extends Lambda implements Cloneable {
    static T2 BOOL, INT64, FLT64, STRP;
    static Worklist WORK;
    static int PAIR_ALIAS, TRIPLE_ALIAS;
    static void reset() {
      PAIR_ALIAS   = BitsAlias.new_alias(BitsAlias.ALLX);
      TRIPLE_ALIAS = BitsAlias.new_alias(BitsAlias.ALLX);
      BOOL  = T2.make_base(TypeInt.BOOL);
      INT64 = T2.make_base(TypeInt.INT64);
      FLT64 = T2.make_base(TypeFlt.FLT64);
      STRP  = null; //T2.make_base(TypeMemPtr.STRPTR);
    }
    abstract String name();
    private static final String[][] IDS = new String[][] {
      null,
      {"x"},
      {"x","y"},
      {"x","y","z"},
    };
    PrimSyn(T2 ...t2s) {
      super(null,IDS[t2s.length-1]);
      _hmt = T2.make_fun(BitsFun.make0(_fidx),t2s).fresh();
      for( int i=0; i<_targs.length; i++ )
        _targs[i] = _hmt.args(i).push_update(this);
    }
    abstract PrimSyn make();
    @Override int prep_tree(Syntax par, VStack nongen, Worklist work) {
      prep_tree_impl(par,nongen,work, _hmt);
      return 1;
    }
    @Override boolean hm(Worklist work) {
      T2 old = find();
      if( old.is_err() ) return false;
      assert old.is_fun();
      for( int i=0; i<_targs.length; i++ )
        if( targ(i).is_err() )
          return old.unify(targ(i),work);

      return false;
    }
    @Override void add_hm_work(Worklist work) {
      if( find().is_err() ) work.push(_par);
    }
    @Override void add_val_work(Syntax child, Worklist work) { throw unimpl(); }
    @Override boolean more_work(Worklist work) { return more_work_impl(work); }
    @Override SB str(SB sb){ return sb.p(name()); }
    @Override SB p1(SB sb) { return sb.p(name()); }
    @Override SB p2(SB sb, VBitSet dups){ return sb; }
  }


  // Curried Pair
  static class Pair1 extends PrimSyn {
    @Override String name() { return "pair1"; }
    static private T2 var1,var2;
    static HashMap<Type,Pair1X> PAIR1S = new HashMap<>();
    public Pair1() {
      super(var1=T2.make_leaf(),T2.make_fun(BitsFun.NANY,var2=T2.make_leaf(),T2.make_struct(BitsAlias.make0(PAIR_ALIAS),new String[]{"0","1"},new T2[]{var1,var2})));
    }
    @Override PrimSyn make() { return new Pair1(); }
    @Override Type apply(Syntax[] args) {
      Type t = args[0]._flow;
      Pair1X p1x = PAIR1S.get(t);
      if( p1x == null )
        PAIR1S.put(t,p1x = new Pair1X(t));
      return p1x._flow;
    }
    static class Pair1X extends PrimSyn {
      final Type _con;
      @Override String name() { return "Pair1_"+_con; }
      static private T2 var2;
      public Pair1X(Type con) {
        super(var2=T2.make_leaf(),T2.make_struct(BitsAlias.make0(PAIR_ALIAS),new String[]{"0","1"},new T2[]{T2.make_base(con),var2}));
        _con=con;
      }
      @Override PrimSyn make() { throw unimpl(); }
      //@Override boolean hm(Worklist work) { throw unimpl(); }
      @Override Type apply(Syntax[] args) {
        T2 tcon = find().args(1).args(0);
        assert tcon.is_base();
        //return TypeMemPtr.make(PAIR_ALIAS,TypeStruct.maket(tcon._flow,args.length==0 ? Root.widen(_targs[0]) : args[0]._flow));
        throw unimpl();
      }
    }
  }

  // Pair
  static class Pair extends PrimSyn {
    @Override String name() { return "pair"; }
    static private T2 var1,var2;
    public Pair() {
      super(var1=T2.make_leaf(),var2=T2.make_leaf(),T2.make_struct(BitsAlias.make0(PAIR_ALIAS),new String[]{"0","1"},new T2[]{var1,var2}));
    }
    @Override PrimSyn make() { return new Pair(); }
    @Override Type apply(Syntax[] args) {
      //TypeFld[] ts = TypeFlds.get(args.length+1);
      //ts[0] = TypeFld.NO_DISP;       // Display
      //for( int i=0; i<args.length; i++ ) ts[i+1] = TypeFld.make_tup(args[i]._flow,i);
      //return TypeMemPtr.make(PAIR_ALIAS,TypeStruct.make(ts));
      throw unimpl();
    }
  }


  // Triple
  static class Triple extends PrimSyn {
    @Override String name() { return "triple"; }
    static private T2 var1,var2,var3;
    public Triple() { super(var1=T2.make_leaf(),var2=T2.make_leaf(),var3=T2.make_leaf(),T2.make_struct(BitsAlias.make0(TRIPLE_ALIAS),new String[]{"0","1","2"},new T2[]{var1,var2,var3})); }
    @Override PrimSyn make() { return new Triple(); }
    @Override Type apply(Syntax[] args) {
      //TypeFld[] ts = TypeFlds.get(args.length+1);
      //ts[0] = TypeFld.NO_DISP;       // Display
      //for( int i=0; i<args.length; i++ ) ts[i+1] = TypeFld.make_tup(args[i]._flow,i);
      //return TypeMemPtr.make(TRIPLE_ALIAS,TypeStruct.make(ts));
      throw unimpl();
    }
  }

  // Special form of a Lambda body for IF which changes the H-M rules.
  // None-executing paths do not unify args.
  static class If extends PrimSyn {
    @Override String name() { return "if"; }
    public If() { super(T2.make_leaf(),T2.make_leaf(),T2.make_leaf(),T2.make_leaf()); }
    @Override PrimSyn make() { return new If(); }
    @Override boolean hm(Worklist work) {
      T2 rez = find().args(3);
      // GCP helps HM: do not unify dead control paths
      if( DO_GCP ) {            // Doing GCP during HM
        Type pred = _types[0];
        if( pred == TypeNil.XNIL || pred==TypeNil.NIL )
          return rez.unify(targ(2),work); // Unify only the false side
        if( pred.above_center() ) // Neither side executes
          return false;           // Unify neither side
        //if( !pred.must_nil() )    // Unify only the true side
        //  return rez.unify(targ(1),work);
        throw unimpl();
      }
      // Unify both sides with the result
      return
        rez.unify(targ(1),work) |
        rez.find().unify(targ(2),work);
    }
    @Override Type apply( Syntax[] args) {
      Type pred= args[0]._flow;
      Type t1  = args[1]._flow;
      Type t2  = args[2]._flow;
      // Conditional Constant Propagation: only prop types from executable sides
      if( pred == TypeNil.XNIL || pred==TypeNil.NIL )
        return t2;              // False only
      if( pred.above_center() ) // Delay any values
        return TypeNil.XSCALAR;    // t1.join(t2);     // Join of either
      //if( !pred.must_nil() )    // True only
      //  return t1;
      //// Could be either, so meet
      //return t1.meet(t2);
      throw unimpl();
    }
  }

  // EQ
  static class EQ extends PrimSyn {
    @Override String name() { return "eq"; }
    static private T2 var1;
    public EQ() { super(var1=T2.make_leaf(),var1,BOOL); }
    @Override PrimSyn make() { return new EQ(); }
    @Override Type apply( Syntax[] args) {
      Type x0 = args[0]._flow;
      Type x1 = args[1]._flow;
      if( x0.above_center() || x1.above_center() ) return TypeInt.BOOL.dual();
      if( x0.is_con() && x1.is_con() && x0==x1 )
        return TypeInt.TRUE;
      // TODO: Can also know about nil/not-nil
      return TypeInt.BOOL;
    }
  }

  // ?0
  static class EQ0 extends PrimSyn {
    @Override String name() { return "?0"; }
    public EQ0() { super(INT64,BOOL); }
    @Override PrimSyn make() { return new EQ0(); }
    @Override Type apply( Syntax[] args) {
      Type pred = args[0]._flow;
      if( pred.above_center() ) return TypeInt.BOOL.dual();
      if( pred==Type.ALL ) return TypeInt.BOOL;
      if( pred == TypeNil.XNIL || pred==TypeNil.NIL )
        return TypeInt.TRUE;
      //if( pred.meet_nil(TypeNil.NIL)!=pred )
      //  return TypeInt.FALSE;
      //return TypeInt.BOOL;
      throw unimpl();
    }
  }

  static class IsEmpty extends PrimSyn {
    @Override String name() { return "isempty"; }
    public IsEmpty() { super(STRP,BOOL); }
    @Override PrimSyn make() { return new IsEmpty(); }
    @Override Type apply( Syntax[] args) {
      Type pred = args[0]._flow;
      if( pred.above_center() ) return TypeInt.BOOL.dual();
      //TypeObj to;
      //if( pred instanceof TypeMemPtr && (to=((TypeMemPtr)pred)._obj) instanceof TypeStr && to.is_con() )
      //  return TypeInt.con(to.getstr().isEmpty() ? 1 : 0);
      //return TypeInt.BOOL;
      throw unimpl();
    }
  }

  // Remove a nil from a struct after a guarding if-test
  static class NotNil extends PrimSyn {
    @Override String name() { return "notnil"; }
    public NotNil() { super(T2.make_leaf(),T2.make_leaf()); }
    @Override PrimSyn make() { return new NotNil(); }
    @Override int prep_tree( Syntax par, VStack nongen, Worklist work ) {
      int cnt = super.prep_tree(par,nongen,work);
      find().args(1).push_update(this);
      return cnt;
    }
    @Override boolean hm(Worklist work) {
      assert find().is_fun();
      T2 arg = targ(0);
      T2 ret = find().args(1);
      if( arg.is_err () || ret.is_err () ) return false;
      if( arg.is_leaf() && ret.is_leaf() ) return false;

      // One or the other is a base.  If they are unrelated, strip the nil.
      // If they are forced together, leave the nil.
      if( arg.is_base() || ret.is_base() ) {
        if( arg.is_base() && ret.is_base() && ret._flow == arg._flow.join(TypeNil.NSCALR) ) return false;
        if( arg==ret ) return false; // Cannot not-nil from self
        if( work==null ) return true; // Progress will be made
        if( arg.is_leaf() ) { arg.unify(T2.make_base(ret._flow),work); arg = arg.find(); }
        if( ret.is_leaf() ) { ret.unify(T2.make_base(arg._flow),work); ret = ret.find(); }
        assert arg.is_base() && ret.is_base();
        ret._flow = arg._flow.join(TypeNil.NSCALR); // Strip nil from base
        return true;
      }
      // One or the other is a function.  Same as structs, can strip the nil from nil-able functions.
      if( arg.is_fun() || ret.is_fun() )
        throw unimpl();         // Strip nil from fidxs


      // One or the other is a struct.
      assert arg.is_struct() || ret.is_struct();
      // See if the input and outputs vary anywhere
      if( arg.is_struct() && ret.is_struct() && ret._alias == arg._alias.clear(0) && ret._ids.length==arg._ids.length ) {
        int i=0; for( ; i<arg._ids.length; i++ ) {
          int idx = Util.find(ret._ids,arg._ids[i]);
          if( idx== -1 || arg.args(i)!=ret.args(idx) )
            break;              // Missing or unequal fields
        }
        if( i==arg._ids.length )
          return false;       // All fields are unified; only the alias differs by nil
      }

      // Make sure both are structs
      if( work==null ) return true; // Progress will be made
      if( arg.is_leaf() ) { arg.unify(T2.make_struct(ret._alias,new String[0],new T2[0],arg._open),work); arg = arg.find(); }
      if( ret.is_leaf() ) { ret.unify(T2.make_struct(arg._alias,new String[0],new T2[0],arg._open),work); ret = ret.find(); }
      assert arg.is_struct() && ret.is_struct();
      ret._alias = arg._alias.clear(0); // Alias relationship is clear

      // Unify all fields, but not the aliases, so cannot unify at the top level.
      // Ignoring the open/not-open as expecting these to be the same.
      for( int i=0; i<arg._ids.length; i++ ) {
        String id = arg._ids[i];
        int idx = Util.find(ret._ids,id);
        if( idx==-1 ) ret.add_fld(id,arg.args(i),work);
        else ret.args(idx).unify(arg.args(i),work);
      }
      for( int i=0; i<ret._ids.length; i++ ) {
        String id = ret._ids[i];
        if( Util.find(arg._ids,id)== -1 )
          arg.add_fld(id,ret.args(i),work);
      }

      return true;            // Progress
    }
    @Override Type apply( Syntax[] args) {
      Type val = args[0]._flow;
      if( val==TypeNil.NIL ) return TypeNil.XSCALAR; // Weird case of not-nil nil
      return val.join(TypeNil.NSCALR);
    }
  }

  // multiply
  static class Mul extends PrimSyn {
    @Override String name() { return "*"; }
    public Mul() { super(INT64,INT64,INT64); }
    @Override PrimSyn make() { return new Mul(); }
    @Override Type apply( Syntax[] args) {
      Type t0 = args[0]._flow;
      Type t1 = args[1]._flow;
      if( t0.above_center() || t1.above_center() )
        return TypeInt.INT64.dual();
      if( t0 instanceof TypeInt && t1 instanceof TypeInt ) {
        if( t0.is_con() && t0.getl()==0 ) return TypeNil.XNIL;
        if( t1.is_con() && t1.getl()==0 ) return TypeNil.XNIL;
        if( t0.is_con() && t1.is_con() )
          return TypeInt.con(t0.getl()*t1.getl());
      }
      return TypeInt.INT64;
    }
  }

  // decrement
  static class Dec extends PrimSyn {
    @Override String name() { return "dec"; }
    public Dec() { super(INT64,INT64); }
    @Override PrimSyn make() { return new Dec(); }
    @Override Type apply( Syntax[] args) {
      Type t0 = args[0]._flow;
      if( t0.above_center() ) return TypeInt.INT64.dual();
      if( t0 instanceof TypeInt && t0.is_con() )
        return TypeInt.con(t0.getl()-1);
      return TypeInt.INT64;
    }
  }

  // int->str
  static class Str extends PrimSyn {
    @Override String name() { return "str"; }
    public Str() { super(INT64,STRP); }
    @Override PrimSyn make() { return new Str(); }
    @Override Type apply( Syntax[] args) {
      Type i = args[0]._flow;
      //if( i.above_center() ) return TypeMemPtr.STRPTR.dual();
      //if( i instanceof TypeInt && i.is_con() )
      //  return TypeMemPtr.make(BitsAlias.STRBITS,TypeStr.con(String.valueOf(i.getl()).intern()));
      //return TypeMemPtr.STRPTR;
      throw unimpl();
    }
  }


  // flt->(factor flt flt)
  static class Factor extends PrimSyn {
    @Override String name() { return "factor"; }
    public Factor() { super(FLT64,FLT64); }
    @Override PrimSyn make() { return new Factor(); }
    @Override Type apply( Syntax[] args) {
      Type flt = args[0]._flow;
      if( flt.above_center() ) return TypeFlt.FLT64.dual();
      return TypeFlt.FLT64;
    }
  }

  // ---------------------------------------------------------------------
  // T2 types form a Lattice, with 'unify' same as 'meet'.  T2's form a DAG
  // (cycles if i allow recursive unification) with sharing.  Each Syntax has a
  // T2, and the forest of T2s can share.  Leaves of a T2 can be either a
  // simple concrete base type, or a sharable leaf.  Unify is structural, and
  // where not unifyable the union is replaced with an Error.
  static class T2 implements Cloneable {
    private static int CNT=0;
    final int _uid;

    // A plain type variable starts with a 'V', and can unify directly.
    // Everything else is structural - during unification they must match names
    // and arguments and Type constants.
    @NotNull String _name; // name, e.g. "->" or "pair" or "V123" or "base"

    // Structural parts to unify with, or slot 0 is used during normal U-F
    T2[] _args;

    // A dataflow type.  Unused for everything except base type-vars (i.e.
    // constants, primitive tvars).  Splitting these to make it easier to tease
    // apart when they should be used, and when not.  Root needs a way to
    // recursively make a flow type from an HM type and the confusion is that
    // the _flow field is a valid flow type... it is not except and only for
    // Base types.
    Type _flow;
    BitsFun _fidxs;             // Unused except for is_fun
    // Structs have field names and aliases
    BitsAlias _alias;           // Unused except for is_struct and NIL
    String[] _ids;
    boolean _open;              // Struct can be extended
    String _err;                // Error

    // Dependent (non-local) tvars to revisit
    Ary<Syntax> _deps;

    // Constructor factories.
    static T2 make_leaf() { return new T2("V"+CNT); }
    static T2 make_base(Type flow) { T2 base = new T2("Base"); base._flow = flow; return base; }
    static T2 make_fun(BitsFun fidxs, T2... args) { T2 tfun = new T2("->",args); tfun._fidxs = fidxs; return tfun; }
    static T2 make_struct( BitsAlias aliases, String[] ids, T2[] flds ) { return make_struct(aliases,ids,flds,false); }
    static T2 make_struct( BitsAlias aliases, String[] ids, T2[] flds, boolean open ) {
      T2 tstr = new T2("@{}",flds);
      tstr._alias=aliases;
      tstr._ids = ids;
      tstr._open= open;
      return tstr;
    }
    static T2 make_err(String s)   { T2 terr = new T2("Err"); terr._err = s.intern(); return terr; }
    T2 miss_field(String id) { return make_err("Missing field "+id+" in "+p()); }
    T2 copy() {
      T2 t = new T2(_name);
      if( _args!=null ) t._args = new T2[_args.length];
      t._flow  = _flow;
      t._fidxs = _fidxs;
      t._alias = _alias;
      t._ids   = _ids;
      t._err   = _err;
      t._deps  = _deps;
      t._open  = _open;
      return t;
    }

    private T2(@NotNull String name) { _uid = CNT++; _name= name; }
    private T2(@NotNull String name, T2 @NotNull ... args) {
      this(name);
      _args= args;
    }

    // A type var, not a concrete leaf.  Might be U-Fd or not.
    boolean is_leaf() { return _name.charAt(0)=='V' || _name.charAt(0)=='X'; }
    boolean no_uf()   { return _name.charAt(0)!='X'; }
    boolean isa(String name) { return Util.eq(_name,name); }
    boolean is_base() { return isa("Base"); }
    boolean is_fun () { return isa("->"); }
    boolean is_struct() { return isa("@{}"); }
    boolean is_err()  { return isa("Err"); }

    T2 debug_find() {// Find, without the roll-up
      if( !is_leaf() ) return this; // Shortcut
      if( _args==null ) return this;
      T2 u = _args[0];
      if( u.no_uf() ) return u;  // Shortcut
      // U-F fixup
      while( u.is_leaf() && !u.no_uf() ) u = u._args[0];
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

    // Recursively build a conservative flow type from an HM type.  The HM
    // is_struct wants to be a TypeMemPtr, but the recursive builder is built
    // around TypeStruct.

    // No function arguments, just function returns.
    static final NonBlockingHashMapLong<TypeStruct> ADUPS = new NonBlockingHashMapLong<>();
    Type as_flow() {
      assert ADUPS.isEmpty();
      Type t = _as_flow();
      ADUPS.clear();
      assert Type.intern_check();
      return t;
    }
    Type _as_flow() {
      assert no_uf();
      if( is_base() ) return _flow;
      if( is_leaf() ) return TypeNil.SCALAR;
      if( is_err()  ) throw unimpl(); //return TypeMemPtr.make(BitsAlias.STRBITS,TypeStr.con(_err));
      if( is_fun()  ) return _flow;
      if( is_struct() ) {
        TypeStruct tstr = ADUPS.get(_uid);
        if( tstr==null ) {
          Type.RECURSIVE_MEET++;
          //TypeFld[] ts = TypeFlds.get(_ids.length+1);
          //ts[0] = TypeFld.NO_DISP;
          //for( int i=0; i<_ids.length; i++ )
          //  ts[i+1] = TypeFld.malloc(_ids[i],null,Access.Final,i);
          //tstr = TypeStruct.malloc("",false,ts,true);
          //tstr._hash = tstr.compute_hash();
          //ADUPS.put(_uid,tstr); // Stop cycles
          //for( int i=0; i<_ids.length; i++ )
          //  ts[i+1].setX(args(i)._as_flow()); // Recursive
          //if( --Type.RECURSIVE_MEET == 0 ) {
          //  // Shrink / remove cycle dups.  Might make new (smaller)
          //  // TypeStructs, so keep RECURSIVE_MEET enabled.
          //  Type.RECURSIVE_MEET++;
          //  tstr = TypeStruct.shrink(tstr.reachable(),tstr);
          //  TypeStruct.UF.clear();
          //  Type.RECURSIVE_MEET--;
          //  // Walk the final cyclic structure and intern everything.
          //  tstr.install_cyclic(tstr.reachable());
          //}
        } else {
          //tstr.set_cyclic();    // Been there, done that, just mark it cyclic
        }
        throw unimpl();
        //return TypeMemPtr.make(_alias,tstr);
      }

      throw unimpl();
    }


    // If LHS is null, return RHS (and no progress)
    // If RHS is null, return LHS (and progress)
    // Else return meet (and progress is LHS!=RHS)
    private Type meet_flow(T2 that) {
      if( this._flow==null ) return that._flow;
      if( that._flow==null ) return this._flow;
      return _flow.meet(that._flow);
    }
    private BitsFun meet_fidxs(T2 that) {
      if( this._fidxs==null ) return that._fidxs;
      if( that._fidxs==null ) return this._fidxs;
      return _fidxs.meet(that._fidxs);
    }
    private BitsAlias meet_alias(T2 that) {
      if( this._alias==null ) return that._alias;
      if( that._alias==null ) return this._alias;
      return _alias.meet(that._alias);
    }
    private String[] meet_ids(T2 that) {
      String[] ids = that._ids;
      if( _ids==ids ) return ids;
      if( _ids==null ) return ids;
      if( ids==null ) return _ids;
      if( _ids.length!=ids.length ) throw unimpl(); // Handled at a higher level
      for( String id : ids )
        if( Util.find(_ids, id) == -1 )
          throw unimpl();
      return ids;               // Return RHS
    }
    private boolean meet_opens(T2 that) {
      if( _open==that._open ) return that._open;
      if( !is_struct() ) return that._open;
      if( !that.is_struct() ) return _open;
      throw unimpl();
    }
    private String meet_err(T2 that) {
      if( this._err==null ) return that._err;
      if( that._err==null ) return this._err;
      // TODO: Probably gather unrelated strings in a set
      return _uid < that._uid ? _err : that._err;
    }
    private int base_states() {
      int cnt=0;
      if( _flow !=null ) cnt++;
      if( _fidxs!=null ) cnt++;
      if( _err  !=null ) cnt++;
      if( _alias!=null ) { cnt++; assert _ids!=null; }
      else assert _ids==null;
      return cnt;
    }

    // U-F union; this becomes that; returns 'that'.
    // No change if only testing, and reports progress.
    boolean union(T2 that, Worklist work) {
      assert no_uf(); // Cannot union twice
      assert base_states()<=1 && that.base_states()<=1;
      if( this==that ) return false;
      if( work==null ) return true; // Report progress without changing
      // Keep the merge of all base types, revisiting deps if any changes
      if( _flow !=that._flow  ||
          _fidxs!=that._fidxs ||
          _alias!=that._alias ||
          _ids  !=that._ids   ||
          _open !=that._open  ||
          !Util.eq(_err,that._err) )
        work.addAll(that._deps); // Any progress, revisit deps
      // If flow types are not compatible, return an error now
      if( _flow!=null & that._flow!=null && (_flow.widen() != that._flow.widen() && !_flow.isa(that._flow.widen())) )
        return union_err(that,work,"Cannot unify "+this.p()+" and "+that.p());
      that._flow  = meet_flow (that);
      that._fidxs = meet_fidxs(that);
      that._alias = meet_alias(that);
      that._ids   = meet_ids  (that);
      that._open  = meet_opens(that);
      that._err   = meet_err  (that);
      if( this._flow==TypeNil.NIL && that.is_struct() ) {
        that._alias = that._alias.meet_nil();
        that._flow = null;
      }
      if( that._err!=null ) {   // Kill the base types in an error
        that._flow=null;  that._fidxs=null;  that._alias=null;  that._ids=null;
      }
      _flow=null;  _fidxs=null;  _alias=null; _ids=null; _err=null; // Kill the base types in a unified type

      // Worklist: put updates on the worklist for revisiting
      if( _deps != null ) {
        work.addAll(_deps); // Re-Apply
        // Merge update lists, for future unions
        if( that._deps==null && that._args==null ) that._deps = _deps;
        else for( Syntax dep : _deps ) that.push_update(dep);
        _deps = null;
      }
      if( _args==null || _args.length!=1 ) _args = new T2[1];
      // Unify the two base types, preserving errors
      _args[0] = that;         // U-F update
      _name = "X"+_uid; // Flag as a leaf & unified
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

      // All leaf types immediately unify.
      if( this._args==null && that._args==null ) {
        T2 lhs=this, rhs=that;
        if( is_err() ||         // Errors beat all others
            (!that.is_err() && is_base()) )
          { rhs=this; lhs=that; } // Base beats plain leaf
        // If tied, keep lower uid
        if( Util.eq(lhs._name,rhs._name) && _uid<that._uid ) { rhs=this; lhs=that; }
        return lhs.union(rhs,work);
      }
      // Any leaf immediately unifies with any non-leaf
      if( this.is_leaf() || that.is_err() ) return this.union(that,work);
      if( that.is_leaf() || this.is_err() ) return that.union(this,work);
      // Special case for nil and struct
      if( this.is_struct() && that.is_base() && that._flow==TypeNil.NIL )
        return that.union(this,work);
      if( that.is_struct() && this.is_base() && this._flow==TypeNil.NIL )
        return this.union(that,work);

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
        _unify_struct(that,work);
      } else {                                // Normal structural unification
        for( int i=0; i<_args.length; i++ ) { // For all fields in LHS
          args(i)._unify(that.args(i),work);
          if( (that=that.find()).is_err() ) break;
        }
      }
      if( find().is_err() && !that.find().is_err() )
        // TODO: Find a more elegant way to preserve errors
        return that.find().union(find(),work); // Preserve errors
      return find().union(that,work);
    }

    private void _unify_struct(T2 that, Worklist work) {
      assert this.is_struct() && that.is_struct();
      // Unification for structs is more complicated; args are aligned via
      // field names and not by position.  Conceptually, fields in one struct
      // and not the other are put in both before unifying the structs.  Open
      // structs copy from the other side; closed structs insert a missing
      // field error.
      for( int i=0; i<_ids.length; i++ ) { // For all fields in LHS
        int idx = Util.find(that._ids,_ids[i]);
        if( idx==-1 )           // Missing that field?  Copy from left if open, error if closed.
          that.add_fld(_ids[i], that._open ? args(i) : that.miss_field(_ids[i]),  work);
        else args(i)._unify(that.args(idx),work);    // Unify matching field
        if( (that=that.find()).is_err() ) return; // Recursively, might have already rolled this up
      }
      // Fields in RHS and not the LHS are also merged; if the LHS is open we'd
      // just copy the missing fields into it, then unify the structs
      // (shortcut: just skip the copy).  If the LHS is closed, then the extra
      // RHS fields are an error.
      if( !_open )              // LHS is closed, so extras in RHS are errors
        for( int i=0; i<that._ids.length; i++ )    // For all fields in RHS
          if( Util.find(_ids,that._ids[i]) == -1 ) // Missing in LHS
            that.args(i)._unify(miss_field(that._ids[i]),work); // If closed, extra field is an error
      // Shortcut (for asserts): LHS gets same ids as RHS, since its about to be top-level unified
      _ids = that._ids;
      _open= that._open;
    }

    // Insert a new field; keep fields sorted
    private boolean add_fld(String id, T2 fld, Worklist work) {
      assert is_struct();
      int len = _ids.length;
      // Find insertion point
      int idx = Arrays.binarySearch(_ids,id);
      assert idx<0;             // Never found
      idx = -idx-1;               // Insertion point
      // Insert in sorted order
      _ids  = Arrays.copyOf( _ids,len+1);
      _args = Arrays.copyOf(_args,len+1);
      System.arraycopy( _ids,idx, _ids,idx+1,len-idx);
      System.arraycopy(_args,idx,_args,idx+1,len-idx);
      _ids [idx] = id ;
      _args[idx] = fld;
      fld.push_update(_deps); // If field changes, all deps change
      work.addAll(_deps); //
      return true;        // Always progress
    }

    private long dbl_uid(T2 t) { return dbl_uid(t._uid); }
    private long dbl_uid(long uid) { return ((long)_uid<<32)|uid; }

    private boolean fresh_base(T2 that, Worklist work) {
      assert base_states()<=1 && that.base_states()<=1;
      boolean progress=false;
      Type      flow  = meet_flow (that);  progress |= flow  != that._flow ;
      BitsFun   fidxs = meet_fidxs(that);  progress |= fidxs != that._fidxs;
      BitsAlias alias = meet_alias(that);  progress |= alias != that._alias;
      String[]  ids   = meet_ids  (that);  progress |= ids   != that._ids;
      boolean   open  = meet_opens(that);  progress |= open  != that._open;
      String    err   = meet_err  (that);  progress |= !Util.eq(err,that._err);
      if( !progress ) return false;
      if( work==null ) return true;
      // Progress
      Type that_flow = that._flow;
      that._flow  = flow ;
      that._fidxs = fidxs;
      that._alias = alias;
      that._ids   = ids;
      that._open  = open;
      that._err   = err;
      if( !_can_be_HM_base(that,that_flow) ) {
        that._flow = that_flow; // Unwind for error message
        String msg = "Cannot unify "+this.p()+" and "+that.p();
        that._flow=null;  that._fidxs=null;  that._alias=null;  that._ids=null; // Now kill the base types, since in-error
        return that.union(make_err(msg),work);
      }
      assert that.base_states()<=1;
      that.add_deps_work(work);
      if( that.is_leaf() ) that._name = _name; // That is a base/err now
      return true;
    }
    private boolean _can_be_HM_base(T2 that, Type that_flow) {
      if( that.base_states() > 1 ) return false;
      if( _flow==null || that_flow==null ) return true;
      Type wthisflow =     _flow.widen();
      Type wthatflow = that_flow.widen();
      if( wthisflow==wthatflow ) return true;
      return wthisflow.isa(wthatflow);
    }
    private boolean union_err(T2 that, Worklist work, String msg) {
      that._flow=null;  that._fidxs=null;  that._alias=null;  that._ids=null; // Now kill the base types, since in-error
      union(that,work);
      return that.union(make_err(msg),work);
    }

    // -----------------
    // Make a (lazy) fresh copy of 'this' and unify it with 'that'.  This is
    // the same as calling 'fresh' then 'unify', without the clone of 'this'.
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

      // In the non-generative set, so do a hard unify, not a fresh-unify.
      if( nongen_in(nongen) ) return vput(that,_unify(that,work)); // Famous 'occurs-check', switch to normal unify

      // LHS is a nil, RHS is a struct; add nil to RHS
      if( is_base() && _flow==TypeNil.NIL && that.is_struct() ) {
        if( that._alias.test(0) ) return false; // Already nil
        if( work != null )
          that._alias = that._alias.set(0); // Add nil
        return true;
      }
      // If RHS is a nil, LHS is a struct; fresh-clone to RHS and add nil
      if( that.is_base() && that._flow==TypeNil.NIL && this.is_struct() ) {
        if( work==null ) return true;
        T2 t2 = _fresh(nongen);
        t2._alias = BitsAlias.EMPTY;
        return t2._unify(that, work);
      }


      // LHS is a leaf, base, or error
      if( this._args==null ) return vput(that,fresh_base(that,work));
      if( that.is_leaf() )  // RHS is a tvar; union with a deep copy of LHS
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
        assert is_fun() && that.is_fun() && _flow==null && that._flow==null;
        for( int i=0; i<_args.length; i++ ) {
          progress |= args(i)._fresh_unify(that.args(i),nongen,work);
          if( progress && work==null ) return true;
          if( (that=that.find()).is_err() ) return true;
        }
        BitsFun fidxs = meet_fidxs(that);
        if( fidxs!=that._fidxs ) progress=true;
        if( progress && work==null ) return true;
        that._fidxs = fidxs;
      }
      return progress;
    }

    // Unification with structs must honor field names.
    private boolean _fresh_unify_struct(T2 that, VStack nongen, Worklist work) {
      assert is_struct() && that.is_struct();
      boolean progress = false;
      // Unification for structs is more complicated; args are aligned via
      // field names and not by position.  Conceptually, fields in one struct
      // and not the other are put in both before unifying the structs.  Open
      // structs copy from the other side; closed structs insert a missing
      // field error.
      for( int i=0; i<_ids.length; i++ ) {
        int idx = Util.find(that._ids,_ids[i]);
        if( idx == -1 ) {       // Missing field on RHS
          if( work==null ) return true; // Will definitely make progress
          progress = true;
          // if both are closed, error on RHS
          that.add_fld(_ids[i], that._open ? args(i)._fresh(nongen) : that.miss_field(_ids[i]),  work);
        } else
          progress |= args(i)._fresh_unify(that.args(idx),nongen,work);
        if( progress && work==null ) return true;
      }
      // Fields in RHS and not the LHS are also merged; if the LHS is open we'd
      // just copy the missing fields into it, then unify the structs
      // (shortcut: just skip the copy).  If the LHS is closed, then the extra
      // RHS fields are an error.
      if( !_open )
        for( int i=0; i<that._ids.length; i++ )    // For all fields in RHS
          if( Util.find(_ids,that._ids[i]) == -1 &&// Missing in LHS
              !that.args(i).is_err() ) {           // And not yet an error
            if( work == null ) return true; // Will definitely make progress
            progress |= that.args(i).unify(miss_field(that._ids[i]), work);
          }

      // Unify aliases
      BitsAlias alias = meet_alias(that);
      if( alias!=that._alias ) progress=true;
      if( progress && work==null ) return true;
      that._alias = alias;
      return progress;
    }

    private boolean vput(T2 that, boolean progress) { VARS.put(this,that); return progress; }

    // Return a fresh copy of 'this'
    T2 fresh() {
      assert VARS.isEmpty();
      T2 rez = _fresh(null);
      VARS.clear();
      return rez;
    }
    private T2 _fresh(VStack nongen) {
      assert no_uf();
      T2 rez = VARS.get(this);
      if( rez!=null ) return rez; // Been there, done that

      if( is_leaf() ) {
        // If occurs_in lexical scope, keep same variable, else make a new leaf
        T2 t = nongen_in(nongen) ? this : T2.make_leaf();
        VARS.put(this,t);
        return t;
      } else {                  // Structure is deep-replicated
        T2 t = copy();
        VARS.put(this,t);       // Stop cyclic structure looping
        if( _args!=null )
          for( int i=0; i<_args.length; i++ )
            t._args[i] = args(i)._fresh(nongen);
        return t;
      }
    }

    // -----------------
    private static final VBitSet ODUPS = new VBitSet();
    boolean _occurs_in_type(T2 x) {
      assert no_uf() && x.no_uf();
      if( x==this ) return true;
      if( ODUPS.tset(x._uid) ) return false; // Been there, done that
      if( !x.is_leaf() && x._args!=null )
        for( int i=0; i<x._args.length; i++ )
          if( _occurs_in_type(x.args(i)) )
            return true;
      return false;
    }

    boolean occurs_in_type(T2 x) {
      ODUPS.clear();
      return _occurs_in_type(x);
    }

    boolean nongen_in(VStack vs) {
      if( vs==null ) return false;
      ODUPS.clear();
      for( T2 t2 : vs )
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
      if( _flow !=t._flow  ||  // Base-cases have to be completely identical
          _fidxs!=t._fidxs ||
          _alias!=t._alias ||
          !Util.eq(_err,t._err) )
        return false;
      if( !Util.eq(_name,t._name) ) return false; // Wrong type-var names
      if( _args==t._args ) return true;           // Same arrays (generally both null)
      if( _args.length != t._args.length )        // Mismatched sizes
        return false;
      // Cycles stall the equal/unequal decision until we see a difference.
      T2 tc = CDUPS.get(this);
      if( tc!=null )  return tc==t; // Cycle check; true if both cycling the same
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
      for( int i=0; i<_args.length; i++ ) {
        int idx = Util.find(t._ids,_ids[i]);
        if( idx==-1 || !args(i)._cycle_equals(t.args(idx)) )
          return false;
      }
      return true;
    }

    // -----------------
    // Walk a T2 and a matching flow-type, and build a map from T2 to flow-types.
    // Stop if either side loses structure.
    Type walk_types_in(Type t) {
      long duid = dbl_uid(t._uid);
      if( Apply.WDUPS.putIfAbsent(duid,"")!=null ) return t;
      assert no_uf();
      if( t==TypeNil.SCALAR ) return fput(t); // Will be scalar for all the breakdown types
      if( is_err() ) return fput(t); //
      // Base variables (when widened to an HM type) might force a lift.
      if( is_base() ) return fput(_flow.widen().join(t));
      // Free variables keep the input flow type.
      if( is_leaf() ) return fput(t);
      if( is_fun() ) {
        if( !(t instanceof TypeFunPtr) ) return t; // Typically some kind of error situation
        // TODO: PAIR1 should report better
        TypeFunPtr tfp = (TypeFunPtr)t;
        T2 ret = args(_args.length-1);
        if( tfp._fidxs==BitsFun.NALL        ) return ret.walk_types_in(TypeNil. SCALAR);
        if( tfp._fidxs==BitsFun.NALL.dual() ) return ret.walk_types_in(TypeNil.XSCALAR);
        for( int fidx : ((TypeFunPtr)t)._fidxs ) {
          Lambda lambda = Lambda.FUNS.get(fidx);
          Type body = lambda.find().is_err()
            ? TypeNil.SCALAR           // Error, no lift
            : (lambda._body == null // Null only for primitives
               ? lambda.find().args(lambda._targs.length).as_flow() // Get primitive return type
               : lambda._body._flow); // Else use body type
          ret.walk_types_in(body);
        }
        return t;
      }

      if( is_struct() ) {
        fput(t);                // Recursive types need to put themselves first
        if( !(t instanceof TypeMemPtr) )  return t;
        TypeMemPtr tmp = (TypeMemPtr)t;
        if( !(tmp._obj instanceof TypeStruct) ) return t;
        TypeStruct ts = tmp._obj;
        for( int i=0; i<_args.length; i++ ) {
          //int idx = ts.fld_find(_ids[i]);
          //// Missing fields are walked as SCALAR
          //args(i).walk_types_in(idx==-1 ? TypeNil.SCALAR : ts.at(idx));
          throw unimpl();
        }
        return ts;
      }

      throw unimpl();
    }
    private Type fput(final Type t) {
      Apply.T2MAP.merge(this, t, Type::meet);
      return t;
    }

    Type walk_types_out(Type t) {
      assert no_uf();
      if( t == TypeNil.XSCALAR ) return t;  // No lift possible
      Type tmap = Apply.T2MAP.get(this);
      if( tmap != null ) return tmap;
      if( is_err() ) throw unimpl();
      assert !is_leaf() && !is_base();        // All output leafs found as inputs already
      if( is_fun() ) return t; // No change, already known as a function (and no TFS in the flow types)
      if( is_struct() ) {
        if( !(t instanceof TypeMemPtr) ) throw unimpl();
        TypeMemPtr tmp = (TypeMemPtr)t;
        if( !(tmp._obj instanceof TypeStruct) ) throw unimpl();
        TypeStruct ts = tmp._obj;
        boolean progress=false;
        //for( int i=0; i<_args.length; i++ ) {
        //  int idx = ts.fld_find(_ids[i]);
        //  if( idx==-1 ) continue;
        //  Type targ = ts.at(idx);
        //  Type rez = args(i).walk_types_out(targ);
        //  progress |= targ != rez;
        //}
        //if( !progress ) return t;
        //// Make a new result
        //TypeFld[] flds = TypeFlds.get(ts.len());
        //for( int i=0; i<_args.length; i++ ) {
        //  int idx = ts.fld_find(_ids[i]);
        //  if( idx==-1 ) continue;
        //  Type targ = ts.at(idx);
        //  Type rez = args(i).walk_types_out(targ);
        //  flds[i] = ts.fld(i).make_from(rez);
        //}
        //return tmp.make_from(ts.make_from(flds));
        throw unimpl();
      }
      throw unimpl();           // Handled all cases
    }

    // -----------------
    // This is a T2 function that is the target of 'fresh', i.e., this function
    // might be fresh-unified with some other function.  Push the application
    // down the function parts; if any changes the fresh-application may make
    // progress.
    static final VBitSet UPDATE_VISIT  = new VBitSet();
    T2 push_update( Ary<Syntax> as ) { if( as != null ) for( Syntax a : as ) push_update(a);  return this;   }
    T2 push_update( Syntax a) { assert UPDATE_VISIT.isEmpty(); push_update_impl(a); UPDATE_VISIT.clear(); return this; }
    private void push_update_impl(Syntax a) {
      assert no_uf();
      if( UPDATE_VISIT.tset(_uid) ) return;
      if( _deps==null ) _deps = new Ary<>(Syntax.class);
      if( _deps.find(a)==-1 ) _deps.push(a);
      if( _args!=null )
        for( int i=0; i<_args.length; i++ )
          if( _args[i]!=null )
            args(i).push_update_impl(a);
    }

    // Recursively add-deps to worklist
    void add_deps_work( Worklist work ) { assert UPDATE_VISIT.isEmpty(); add_deps_work_impl(work); UPDATE_VISIT.clear(); }
    private void add_deps_work_impl( Worklist work ) {
      if( is_leaf() ) {
        work.addAll(_deps);
      } else {
        if( UPDATE_VISIT.tset(_uid) ) return;
        if( _args != null )
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
        dups.set(debug_find()._uid);
      } else
        if( _args!=null )
          for( T2 t : _args )
            if( t!=null )
              t._get_dups(visit,dups);
      return dups;
    }

    // Fancy print for Debuggers - includes explicit U-F re-direction.
    // Does NOT roll-up U-F, has no side-effects.
    @Override public String toString() { return str(new SB(), new VBitSet(), get_dups(new VBitSet()) ).toString(); }
    SB str(SB sb, VBitSet visit, VBitSet dups) {

      if( is_err () ) return sb.p(_err);
      if( is_base() ) return sb.p(_flow);
      boolean dup = dups.get(_uid);
      if( is_leaf() ) {
        sb.p(_name);
        return no_uf() ? sb : _args[0].str(sb.p(">>"), visit, dups);
      }
      if( dup ) sb.p("$V").p(_uid);
      if( visit.tset(_uid) && dup ) return sb;
      if( dup ) sb.p(':');

      // Special printing for functions
      if( is_fun() ) {
        _fidxs.str(sb.p("{")).p(' ');
        for( int i=0; i<_args.length-1; i++ )
          str(sb,visit,_args[i],dups).p(" ");
        return str(sb.p("-> "),visit,_args[_args.length-1],dups).p(" }");
      }

      // Special printing for structures
      if( is_struct() ) {
        _alias.str(sb.p("@{")).p(' ');
        for( int i=0; i<_ids.length; i++ )
          str(sb.p(' ').p(_ids[i]).p(" = "),visit,_args[i],dups).p(',');
        return sb.unchar().p("}");
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
      if( is_base() ) return sb.p(_flow); // One-shot bases just do type
      if( is_leaf() || dups.get(_uid) ) { // Leafs or Duplicates?  Take some effort to pretty-print cycles
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
      if( is_err () ) return sb.p(_err);

      // Special printing for functions: { arg -> body }
      if( is_fun() ) {
        sb.p("{ ");
        for( int i=0; i<_args.length-1; i++ )
          args(i)._p(sb,visit,dups).p(" ");
        return args(_args.length-1)._p(sb.p("-> "),visit,dups).p(" }");
      }

      // Special printing for structures: @{ fld0 = body, fld1 = body, ... }
      if( is_struct() ) {
        if( is_tuple() ) {
          sb.p('(');
          for( int i=0; i<_ids.length; i++ ) {
            int idx = Util.find(_ids,new String(new char[]{(char)('0'+i)}).intern());
            args(idx)._p(sb.p(' '),visit,dups).p(',');
          }
          sb.unchar().p(')');

        } else {
          sb.p("@{");
          TreeMap<String,Integer> map = new TreeMap<String,Integer>();
          for( int i=0; i<_ids.length; i++ )
            map.put( _ids[i], i );
          for( int i : map.values() )
            args(i)._p(sb.p(' ').p(_ids[i]).p(" = "),visit,dups).p(',');
          sb.unchar().p("}");
        }
        return _alias.str(sb);
      }

      // Generic structural T2: (fun arg0 arg1...)
      sb.p("(").p(_name).p(" ");
      for( int i=0; i<_args.length; i++ ) args(i)._p(sb,visit,dups).p(" ");
      return sb.unchar().p(")");
    }

    boolean is_tuple() {
      if( _ids==null ) return false;
      for( String id : _ids )
        if( !isDigit((byte) id.charAt(0)) )
          return false;
      return true;
    }

    static void reset() { CNT=0; DUPS.clear(); VARS.clear(); ODUPS.clear(); CDUPS.clear(); UPDATE_VISIT.clear(); }
  }

}
