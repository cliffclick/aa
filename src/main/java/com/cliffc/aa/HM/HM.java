package com.cliffc.aa.HM;

import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;
import org.jetbrains.annotations.NotNull;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.IntSupplier;

import static com.cliffc.aa.AA.unimpl;
import static com.cliffc.aa.AA.DSP_IDX;

/**
Combined Hindley-Milner and Global Constant Propagation typing.

Complete stand-alone, for research.

Treats HM as a Monotone Analysis Framework; converted to a worklist style.  The
type-vars are monotonically unified, gradually growing over time - and this is
treated as the MAF lattice.  Some normal Algo-W work gets done in a prepass;
e.g. discovering identifier sources (SSA form), and building the non-generative
set.  Because of the non-local unification behavior type-vars include a
"dependent Syntax" set; a set of Syntax elements put back on the worklist if
this type unifies, beyond the expected parent and AST children.

The normal HM unification steps are treated as the MAF transfer "functions",
taking type-vars as inputs and producing new, unified, type-vars.  Because
unification happens in-place (normal Tarjan disjoint-set union), the transfer
"functions" are executed for side effects only, and return a progress flag.
The transfer functions are virtual calls on each Syntax element.  Some steps
are empty because of the pre-pass (Let,Con).

HM Bases include anything from the GCP lattice, and are generally sharper than
e.g. 'int'.  Bases with values of '3' and "abc" are fine.  These are widened to
the normal HM types if returned from any primitive; they remain sharp if
returned or passed to primitives.  HM functions that escape have their GCP type
widened "as if" called from the most HM-general legal call site; otherwise GCP
assumes escaping functions are never called and their arguments have
unrealistic high flow types.

HM includes polymorphic structures and fields (structural typing not duck
typing), polymorphic nil-checking, constant bases and an error type-var.  Both
HM and GCP types fully support recursive/cyclic types.

HM includes ad-hoc polymorphim via overloading.  An overload is just a normal
tuple/struct which is loaded via a Field with an unknown label.  The label is
inferred as being the only field than can unify without error.  This is done by
doing *trial-unifications* until only a single overload target resolves without
an error.

HM errors keep all the not-unifiable types, all at once, as a special case of a
union type.  Further unifications with the error either add a new not-unifiable
type, or unify with one of the prior types.  These means that types can ALWAYS
unify, including nonsensical unifications between e.g. the constant 5 and a
struct @{ x,y }.  The errors are reported when a type prints.  If the program
contains an error that is not printed at the top-level, then the error code is
dead and the program is considered well typed.

Unification typically makes many temporary type-vars and immediately unifies
them.  For efficiency, this algorithm checks to see if unification requires an
allocation first, instead of just "allocate and unify".  The major place this
happens is identifiers, which normally make a "fresh" copy of their type-var,
then unify.  I use a combined "make-fresh-and-unify" unification algorithm
there.  It is a structural clone of the normal unify, except that it lazily
makes a fresh-copy of the left-hand-side on demand only; typically discovering
that no fresh-copy is required.  This appears to reduce some worst case
examples to near linear time.

To engineer and debug the algorithm, the unification step includes a flag to
mean "actually unify, and report a progress flag" vs "report if progress".  The
report-only mode is aggressively asserted for in the main loop; all Syntax
elements that can make progress are asserted as on the worklist.

GCP gets the normal MAF treatment, no surprises there except perhaps the size
of the GCP lattice.  The GCP lattice includes the obvious int and float ranges
and constants, structs, aliases broken into equivalence classes, function
indices (fidxs) also broken into equivalence classes (and this allows GCP to
compute a reasonably precise Call Graph), contents of memory, and Return
Program Counters ala continuations (no real use is made of these yet).

The combined algorithm includes transfer functions taking facts from both MAF
lattices, producing results in the other lattice.

For the GCP->HM direction, the HM 'if' has a custom transfer function instead
of the usual one.  Unification looks at the GCP value, and unifies either the
true arm, or the false arm, or both or neither.  In this way GCP allows HM to
avoid picking up constraints from dead code.

Also for GCP->HM, the HM ground terms or base terms include anything from the
GCP lattice.  The GCP fidxs / Call Graph is used to track HM terms that might
come from a primitive or a escaped input.

For the HM->GCP direction, the GCP 'apply' has a customer transfer function
where the result from a call gets lifted (JOINed) based on the matching GCP
inputs - and the match comes from using the same HM type-var on both inputs and
outputs.  This allows e.g. "map" calls which typically merge many GCP values at
many applies (call sites) and thus end up typed as a Scalar to Scalar, to
improve the GCP type on a per-call-site basis.

Also for HM->GCP, the HM types are used to constrain the GCP types that can
call any escaped function.  You can think of this as using HM "module types" to
derive the GCP calling types.

Also for HM->GCP, Overloads produce a GCP Union before the overload resolves,
one Type for each choice.  Once HM resolves the Overload the correct Type is
used instead.

Test case 45 demonstrates this combined algorithm, with a program which can
only be typed using the combination of GCP and HM.

BNF for the "core AA" syntax:
   e  = number         | // Primitive numbers; note that wrapped AA numbers are explicitly wrapped in tests
        string         | // More or less a proxy for arrays.
        primitives     | // +, -, *, /, eq, (,) tuple pair, etc
        (fe0 fe1*)     | // Application.  Multiple args are allowed and tracked
        { id* -> fe0 } | // Lambda.  Multiple args are allowed and tracked.  Numbered uniquely
        id             | // Use of an id, either a lambda arg or in a Let/In
        id = fe0; fe1  | // Eqv: letrec id = fe0 in fe1
        @{ (label = fe0;)* } | Structures.  Numbered uniquely.  ';' is a field-separator not a field-end
        fe = e         | // No  field after expression
        fe.label       | // Yes field after expression
        fe._           | // Yes field after expression; field label will be inferred

BNF for the "core AA" pretty-printed types:
   T = Vnnn               | // Leaf number nnn
       >>T1               | // Unified; lazily collapsed with 'find()' calls
       base               | // any lattice element, all are nilable
       T0?T1              | // T1 is a not-nil T0; stacked not-nils collapse
       { T* -> Tret }     | // Lambda, arg count is significant
       *T0                | // Ptr-to-struct; T0 is either a leaf, or unified, or a struct
       @{ (label = T;)* } | // ';' is a field-separator not a field-end
       @{ (_nnn = T;)* }  | // Some field labels are inferred; nnn is the Field uid, and will be inferred to the actual label
       [Error base* T0*]  | // A union of base and not-nil, lambda, ptr, struct

*/

public class HM {
  // Mapping from primitive name to PrimSyn
  static final HashMap<String,PrimSyn> PRIMSYNS = new HashMap<>();
  // Mapping from alias#s to either Struct, Pair or Triple
  static final Ary<Alloc> ALIASES = new Ary<>(Alloc.class);

  static {
    BitsAlias.init0();
    BitsFun.init0();
    // Pre-cook some EXTX aliases, so they get the same number in every test
    for( int i=0; i<10; i++ ) BitsAlias.new_alias(BitsAlias.EXTX);
    // Pre-cook some EXTX fidxs, so they get the same number in every test
    for( int i=0; i<10; i++ ) BitsFun.new_fidx(BitsFun.EXTX);
  }

  static boolean DO_HM ;        // Do Hindley-Milner typing
  static boolean DO_GCP;        // Do forwards-flow Global Constant Propagation typing

  static Work<Syntax> WORK;

  static boolean HM_NEW_LEAF;   // After 1st pass, potential HM new leafs will no longer lift Apply results
  static boolean HM_AMBI;       // After 2nd pass, unresolved Fields are ambiguous
  static boolean HM_FREEZE;     // After 3rd pass, HM types are frozen but GCP types continue to fall

  static Root ROOT;

  static final String RET = " ret";

  public static Root hm( String sprog, int rseed, boolean do_hm, boolean do_gcp ) {
    Type.RECURSIVE_MEET=0;      // Reset between failed tests
    DO_HM  = do_hm ;
    DO_GCP = do_gcp;

    // Initialize the primitives
    for( PrimSyn prim : new PrimSyn[]{ new If(), new Pair(), new EQ(), new EQ0(), new IMul(), new FMul(), new I2F(), new Add(), new Dec(), new IRand(), new Str(), new Triple(), new Factor(), new IsEmpty(), new NotNil()} )
      PRIMSYNS.put(prim.name(),prim);
    new EXTStruct(T2.make_str(TypeMemPtr.STRPTR),TypeMemPtr.STR_ALIAS,null);

    // Parse
    Root prog = ROOT = parse( sprog );

    // Pass 0: Prep for SSA; pre-gather all the (unique) ids
    Work<Syntax> work = WORK = new Work<>(rseed);
    prog.prep_tree(null,null,work);

    // Pass 1: Everything starts high/top/leaf and falls; escaping function args are assumed high
    HM_NEW_LEAF=false;
    HM_AMBI   = false;
    HM_FREEZE = false;
    main_work_loop(prog,work,1);

    // Pass 2: Potential new Leafs quit lifting GCP in Apply
    HM_NEW_LEAF = true;
    prog.add_new_leaf_work(work);
    assert prog.more_work(work);
    main_work_loop(prog,work,2);

    // Pass 3: Unresolved Fields are ambiguous; propagate errors
    HM_AMBI = true;
    prog.add_ambi_work(work);
    assert prog.more_work(work);
    main_work_loop(prog,work,3);
    
    // Pass 4: H-M types freeze, escaping function args are assumed called with lowest H-M compatible
    // GCP types continue to run downhill.
    HM_FREEZE = true;
    prog.add_freeze_work(work);
    assert prog.more_work(work);
    main_work_loop(prog,work,4);

    // Error propagation, no types change.
    assert prog.more_work(work);
    pass_err(prog);

    return prog;
  }

  static void main_work_loop( Root prog, Work<Syntax> work, int pass ) {

    int cnt=0;
    while( work.len()>0 ) {     // While work
      cnt++; assert cnt<10000;  // Check for infinite loops
      Syntax syn = work.pop();  // Get work

      // Do Hindley-Milner work always, to set unresolved Field labels
      {
        T2 old = syn._hmt;      // Old value for progress assert
        if( syn.hm(work) ) {
          assert syn.debug_find()==old.debug_find(); // monotonic: unifying with the result is no-progress
          syn.add_hm_work(work);// Push affected neighbors on worklist
        }
      }
      // Do Global Constant Propagation work
      if( DO_GCP ) {
        Type old = syn._flow;
        Type t = syn.val(work);
        if( t!=old ) {           // Progress
          assert old.isa(t);     // Monotonic falling
          syn._flow = t;         // Update type
          // Push affected neighbors on worklist
          if( syn._par!=null ) syn._par.add_val_work(syn,work);
          else                 prog    .add_val_work(old,work);
        }
      }

      // VERY EXPENSIVE ASSERT: O(n^2).  Every Syntax that makes progress is on the worklist
      assert prog.more_work(work);
      //if( !work.on(prog) && prog._flow instanceof TypeTuple tt ) {
      //  BitsAlias aliases = Root.EXT_ALIASES;
      //  BitsFun   fidxs   = Root.EXT_FIDXS  ;
      //  prog.escapes(tt.at(0),work);
      //  assert aliases==Root.EXT_ALIASES && fidxs==Root.EXT_FIDXS;
      //}
    }
  }

  static void pass_err( Root prog ) {
    prog.visit( syn -> {
        T2 self = syn.find();
        // Nil check on fields
        if( syn instanceof Field fld ) {
          T2 ptr = fld._ptr.find();
          if( ptr.is_nil() || ptr._may_nil )
            self._err = "May be nil when loading field "+fld._id;

          // Expand "Missing field" error with the full pointer type
          if( self._err!=null && self._err.startsWith("Missing field") ) {
            T2 rec=null, bad=null;
            // If the ptr is a full struct, then do not re-print the missing
            // field when printing the ptr type.
            boolean miss2 = ptr.is_ptr() && ((rec=ptr.arg("*"))!=null ) && rec.is_obj();
            if( miss2 )  bad = rec._args.remove(fld._id); // Remove bad field
            self._err = miss_fld(fld._id)+" in "+ptr.p();
            if( miss2 )  rec._args.put(fld._id,bad); // Put it back after printing
          }
        }

        if( self.is_err2() && self.has_nil() )
          // If any contain nil, then we may have folded in a not-nil.
          // To preserve monotonicity, we make them all nil.
          // Example: (3.unify(notnil)).unify("abc" ) ==       int8     .unify("abc")  == (Error int8,"abc" ) <<-- Should be "abc"?
          // Example: (3.unify("abc" )).unify(notnil) == (Error 3,"abc").unify(notnil) == (Error int8,"abc"?)
          self.add_nil();
        return null;
      }, (a,b)->null);
  }
  static String miss_fld(String id) { return ("Missing field "+id).intern(); }
  

  // Reset global statics between tests.  Tests fail leaving wreckage and
  // broken statics in their wake... and then the next test attempts to start.
  static void reset() {
    //System.out.println("Type.INTERN reprobes");
    //AryInt rps = Type.reprobes();
    //System.out.println(rps);
    //long sum=0, cnt=0;
    //if( rps!=null )
    //  for( int i=0; i<rps._len; i++ ) { sum += (long)i*rps.at(i); cnt += rps.at(i); }
    //System.out.println("Accesses: "+cnt+", total reprobes: "+sum+", size: "+Type.intern_size()+", cap: "+Type.intern_capacity());
    BitsAlias.reset_to_init0();
    BitsFun.reset_to_init0();
    Lambda.FUNS.clear();
    Field.reset();
    Root.reset();
    PRIMSYNS.clear();
    ALIASES.clear();
    Syntax.reset();
    T2.reset();
  }

  // ---------------------------------------------------------------------
  // Program text for parsing
  private static int X;
  private static byte[] BUF;
  @Override public String toString() { return new String(BUF,X,BUF.length-X); }
  static Root parse( String s ) {
    X = 0;
    BUF = s.getBytes();
    Syntax prog = fterm();
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
      Syntax fun = fterm();
      Ary<Syntax> args = new Ary<>(new Syntax[1],0);
      while( skipWS()!= ')' && X<BUF.length ) args.push(fterm());
      require(')');
      // Guarding if-nil test inserts an upcast.  This is a syntactic transform only.
      if( fun instanceof If &&
          args.at(0) instanceof Ident id )
        args.set(1,new Apply(new Lambda(args.at(1), id._name), // Apply always resolves
                             new Apply(new NotNil(),new Ident(id._name))));
      return new Apply(fun, args.asAry());
    }

    if( BUF[X]=='{' ) {         // Lambda of 1 or 2 args
      X++;                      // Skip paren
      Ary<String> args = new Ary<>(new String[1],0);
      while( skipWS()!='-' ) args.push(id());
      require();
      Syntax body = fterm();
      require('}');
      return new Lambda(body, args.asAry());
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
      Syntax def = fterm();
      require(';');
      return new Let(id,def,fterm());
    }

    // Structure
    if( BUF[X]=='@' ) {
      X++;
      require('{');
      Ary<String>  ids = new Ary<>(String.class);
      Ary<Syntax> flds = new Ary<>(Syntax.class);
      while( skipWS()!='}' && X < BUF.length ) {
        String id = require('=',id());
        Syntax fld = fterm();
        if( fld==null ) throw unimpl("Missing term for field "+id);
        ids .push( id);
        flds.push(fld);
        if( skipWS()==';' ) X++;
      }
      require('}');
      return new Struct(true,ids.asAry(),flds.asAry());
    }

    throw unimpl("Unknown syntax");
  }
  // Parse a term with an optional following field.
  private static Syntax fterm() {
    Syntax term=term();
    while( true ) {
      if( term==null || skipWS()!='.' ) return term;
      X++;
      term = new Field(id(),term);
    }
  }
  private static final SB ID = new SB();
  private static String id() {
    ID.clear();
    while( X<BUF.length && isAlpha1(BUF[X]) )
      ID.p((char)BUF[X++]);
    String s = ID.toString().intern();
    if( s.length()==0 ) throw unimpl("Missing id");
    if( Util.eq(s,"_") ) return null; // Field is inferred
    return s;
  }
  private static Syntax number() {
    if( BUF[X]=='0' && (BUF[X+1]!='.' || !isDigit(BUF[X+2])) )
      { X++; return new Con(TypeNil.XNIL); }
    int sum=0;
    while( X<BUF.length && isDigit(BUF[X]) )
      sum = sum*10+BUF[X++]-'0';
    if( X>= BUF.length || BUF[X]!='.' )
      return new Con(TypeInt.con(sum));
    // Ambiguous '.' in: 2.3 vs 2.x (field load from a number)
    if( X+1<BUF.length && isAlpha0(BUF[X+1]) )
      return new Con(TypeInt.con(sum));
    X++;
    float f = (float)sum;
    f = f + (BUF[X++]-'0')/10.0f;
    require('f');
    return new Con(TypeFlt.con(f));
  }
  private static Syntax string() {
    int start = ++X;
    while( X<BUF.length && BUF[X]!='"' ) X++;
    return require('"', new Con(TypeMemPtr.make_str(new String(BUF,start,X-start).intern())));
  }
  private static byte skipWS() {
    while(true) {
      if( X == BUF.length ) return -1;
      if( X+1<BUF.length && BUF[X]=='/' && BUF[X+1]=='/' )
        while( BUF[X]!='\n' ) X++;
      if( !isWS(BUF[X]) ) return BUF[X];
      X++;
    }
  }
  private static boolean isWS    (byte c) { return c == ' ' || c == '\t' || c == '\n' || c == '\r'; }
  private static boolean isDigit (byte c) { return '0' <= c && c <= '9'; }
  private static boolean isAlpha0(byte c) { return ('a'<=c && c <= 'z') || ('A'<=c && c <= 'Z') || (c=='_') || (c=='*') || (c=='?') || (c=='+'); }
  private static boolean isAlpha1(byte c) { return isAlpha0(c) || ('0'<=c && c <= '9') || (c=='/'); }
  private static void require(char c) { if( skipWS()!=c ) throw unimpl("Missing '"+c+"'"); X++; }
  private static <T> T require(char c, T t) { require(c); return t; }
  private static void require() {
    skipWS();
    if( X+2 >= BUF.length || BUF[X]!= '-' || BUF[X+1]!= '>' )
      throw unimpl("Missing '->'");
    X+=2;
  }

  // ---------------------------------------------------------------------
  // Small classic tree of T2s, immutable, with sharing at the root parts.
  static class VStack implements Iterable<T2> {
    final VStack _par;
    private T2 _nongen;
    VStack( VStack par, T2 nongen ) { _par=par; _nongen=nongen; }
    T2 nongen() {
      T2 n = _nongen.find();
      return n==_nongen ? n : (_nongen=n);
    }
    @Override public String toString() {
      // Collect dups across the forest of types
      VBitSet dups = new VBitSet();
      for( VStack vs = this; vs!=null; vs = vs._par )
        vs._nongen._get_dups(new VBitSet(),dups);
      // Now recursively print
      return str(new SB(),dups).toString();
    }
    SB str(SB sb, VBitSet dups) {
      _nongen.str(sb,new VBitSet(),dups,true);
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
  static abstract class Syntax implements IntSupplier {
    private static int CNT=1;
    final int _uid=CNT++;
    @Override public int getAsInt() { return _uid; }
    Syntax() { this(TypeNil.XSCALAR); }
    Syntax(Type init_t) { _flow=init_t; }

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
    abstract boolean hm(Work<Syntax> work);

    abstract void add_hm_work(@NotNull Work<Syntax> work); // Add affected neighbors to worklist

    // Compute and return (and do not set) a new GCP type for this syntax.
    abstract Type val(Work<Syntax> work);

    void add_val_work(Syntax child, @NotNull Work<Syntax> work) {} // Add affected neighbors to worklist

    // Visit whole tree recursively, applying 'map' to self, and reducing that
    // with the recursive value from all children.
    abstract <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce );

    // First pass to "prepare" the tree; does e.g. Ident lookup, sets initial
    // type-vars and counts tree size.
    abstract int prep_tree(Syntax par, VStack nongen, Work<Syntax> work);
    final void prep_tree_impl( Syntax par, VStack nongen, Work<Syntax> work, T2 t ) {
      _par = par;
      _hmt = t;
      _nongen = nongen;
      work.add(this);
    }
    int prep_lookup_deps(Ident id, Syntax prior) { return -99; }
    
    // Giant Assert: True if OK; all Syntaxs off worklist do not make progress
    abstract boolean more_work(Work<Syntax> work);
    final boolean more_work_impl(Work<Syntax> work) {
      if( (!work.on(this) || HM_FREEZE) && hm(null) ) // Anymore HM work?
        return false;           // Found HM work not on worklist or when frozen
      if( DO_GCP ) {            // Doing GCP AND
        Type t = val(null);
        assert _flow.isa(t);    // Flow is not monotonically falling
        if( !work.on(this) && _flow!=t ) // Flow progress not on worklist
          return false;
      }
      return true;
    }
    // Print for debugger
    @Override final public String toString() { return str(new SB()).toString(); }
    abstract SB str(SB sb);
    // Line-by-line print with more detail
    public String p() {
      VBitSet dups  = new VBitSet();
      VBitSet visit = new VBitSet();
      visit(syn -> syn._hmt._get_dups(visit,dups),(a,b)->null);
      return p0(new SB(), new VBitSet(), dups).toString();
    }
    final SB p0(SB sb, VBitSet visit, VBitSet dups) {
      p1(sb.i(),dups).p('#').p(_uid);
      if( DO_HM  ) _hmt .str(sb.p(", HMT="), visit,dups,true);
      if( DO_GCP ) _flow.str(sb.p(", GCP="), true, false );
      sb.nl();
      return p2(sb.ii(2),visit,dups).di(2);
    }
    abstract SB p1(SB sb, VBitSet dups); // Self short print
    abstract SB p2(SB sb, VBitSet visit, VBitSet dups); // Recursion print
    static void reset() { CNT=1; }
    // Utility to find a specific T2 uid
    T2 find( int uid ) {
      return visit( syn -> syn.debug_find().find(uid),
                    (a,b) -> a==null ? b : a );
    }
    Syntax uid( int uid ) {
      return visit( syn -> syn._uid==uid ? syn : null,
                    (a,b) -> a==null ? b : a );
    }
  }

  static class Con extends Syntax {
    final Type _con;
    Con(Type con) { super(con); _con=con; }
    @Override SB str(SB sb) { return p1(sb,null); }
    @Override SB p1(SB sb, VBitSet dups) {
      if( _con==TypeNil.XNIL ) return sb.p("0");
      if( _con instanceof TypeMemPtr cptr && cptr.is_str() )
        return sb.p('"').p(switch( (char)cptr._obj.at(0).getl() ) {
          case 'a' -> "abc";
          case 'd' -> "def";
          case 'r' -> "red";
          case 'b' -> "blue";
          default -> throw unimpl();
          }).p('"');

      return _con.str(sb,true,false);
    }
    @Override SB p2(SB sb, VBitSet visit, VBitSet dups) { return sb; }
    @Override boolean hm(Work<Syntax> work) { return false; }
    @Override Type val(Work<Syntax> work) { return _con; }
    @Override void add_hm_work( @NotNull Work<Syntax> work) { }
    @Override int prep_tree( Syntax par, VStack nongen, Work<Syntax> work ) {
      // A '0' turns into a nilable leaf.
      T2 base = _con==TypeNil.XNIL
        ? T2.make_nil(T2.make_leaf())
        : (_con instanceof TypeMemPtr cptr && cptr.is_str() ? T2.make_str(cptr) : T2.make_base(_con));
      prep_tree_impl(par, nongen, work, base);
      return 1;
    }
    @Override boolean more_work(Work<Syntax> work) { return more_work_impl(work); }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) { return map.apply(this); }
  }


  static class Ident extends Syntax {
    private String _name;       // The identifier name
    private Syntax _def;        // Cached syntax defining point
    private int _idx;           // Index in Lambda (which arg of many), or < 0 for Let
    private T2 _idt;            // Cached type var for the name in scope
    private boolean _fresh;     // True if fresh-unify; short-cut for common case of an id inside its def vs in a Let body.
    Ident(String name) { _name=name; }
    Ident init(Syntax def, int idx, T2 idt, boolean fresh) {
      _def = def;
      _idx = idx;
      _idt = idt;
      _fresh = fresh;
      return this;
    }
    @Override SB str(SB sb) { return p1(sb,null); }
    @Override SB p1(SB sb, VBitSet dups) { return sb.p(_name); }
    @Override SB p2(SB sb, VBitSet visit, VBitSet dups) { return sb; }
    T2 idt() {
      T2 idt = _idt.find();
      return idt==_idt ? idt : (_idt=idt);
    }
    @Override boolean hm(Work<Syntax> work) {
      T2 idt = idt(), hmt=find();
      return _fresh ? idt.fresh_unify(hmt,_nongen,work) : idt.unify(hmt,work);
    }

    @Override void add_hm_work( @NotNull Work<Syntax> work) {
      work.add(_par);
      if( _par!=null && idt().nongen_in(_par._nongen) ) // Got captured in some parent?
        idt().add_deps_work(work);  // Need to revisit dependent ids
      if( _par instanceof Apply && ((Apply)_par)._fun instanceof NotNil )
        work.add(((Apply)_par)._fun);
    }
    @Override Type val(Work<Syntax> work) {
      // Escaping Lambdas are called from Root by most conservative args.
      // Check if this is a parameter from an escaping Lambda.
      if( _def instanceof Lambda lam ) {
        T2 t2 = find();
        if( work!=null &&                       // Not testing
            Root.ext_fidxs().test(lam._fidx) ) {// defining Lambda escaped
          // This argument is HM typed as a function or struct, so can be
          // called with any compatible external function or struct.
          if( t2.is_fun() && !lam.extsetf(_idx) ) { new EXTLambda(t2,work); work.addAll(Root.EXT_DEPS); }
          if( t2.is_ptr() && !lam.extsetp(_idx) ) { new EXTStruct(t2,work); work.addAll(Root.EXT_DEPS); }
        }

        // Meet args across all Applys/Calls.
        for( Apply apl : lam._applys ) {
          Type x = apl instanceof Root
            ? lam.targ(_idx).as_flow(this,false) // Most conservative arg
            // Missing args are XSCALAR here, reported as error later.
            : (_idx < apl._args.length ? apl._args[_idx]._flow : TypeNil.XSCALAR);
          lam.arg_meet(_idx, x, work);
        }
        // Return GCP arg type from meet across all calls
        return lam._types[_idx];
      }
      // Else a Let
      Syntax let = ((Let)_def)._def;
      return let._flow;
    }
    @Override int prep_tree( Syntax par, VStack nongen, Work<Syntax> work ) {
      prep_tree_impl(par,nongen,work,T2.make_leaf());
      for( Syntax syn = par, prior=this; syn!=null; prior=syn, syn = syn._par ) {
        int idx = syn.prep_lookup_deps(this,prior);
        if( idx != -99 ) {
          assert (idx >= 0 && syn instanceof Lambda) ||
                 (idx <  0 && syn instanceof Let   );
          T2 t2 = syn instanceof Lambda lam ? lam.targ(idx) : ((Let)syn).targ();
          // Fresh in body of Let, not-fresh in Let def or Lambda arg
          init(syn,idx,t2,idx == -2);
          return 1;
        }
      }
      throw new RuntimeException("Parse error, "+_name+" is undefined in "+_par);
    }
    @Override boolean more_work(Work<Syntax> work) { return more_work_impl(work); }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) { return map.apply(this); }
  }


  static class Lambda extends Syntax implements Func {
    // Map from FIDXs to Lambdas
    static final NonBlockingHashMapLong<Func> FUNS = new NonBlockingHashMapLong<>();
    final String[] _args;       // Lambda argument names
    Syntax _body;               // Lambda body
    final T2[]      _targs;     // HM argument types
    final Type[]    _types;     // Flow argument types
    final boolean[] _extsetf;   // One-time make external args for an escaping function
    final boolean[] _extsetp;   // One-time make external args for an escaping pointer
    final Ident[][] _refs;      // Identifiers referring to this argument
    final int _fidx;            // Unique function idx
    final Ary<Apply> _applys;   // Applys using this Lambda
    static final String[] ARGNAMES = new String[]{" x"," y"," z"};

    static private int xfidx;

    Lambda(Syntax body, String... args) {
      super(TypeFunPtr.makex(false,BitsFun.make0(xfidx=BitsFun.new_fidx()),args.length+DSP_IDX,Type.ANY,TypeNil.XSCALAR));
      _args=args;
      _body=body;
      // Type variables for all arguments
      _targs = new T2[args.length];
      for( int i=0; i<args.length; i++ ) _targs[i] = T2.make_leaf();
      // Inserted Lambda for not-nil specifically allows overload.
      // Flow types for all arguments
      _types = new Type[args.length];
      for( int i=0; i<args.length; i++ ) _types[i] = TypeNil.XSCALAR;
      _extsetf = new boolean[args.length];
      _extsetp = new boolean[args.length];
      // Idents referring to this argument
      _refs = new Ident[args.length][];
      _applys = new Ary<>(Apply.class);
      // A unique FIDX for this Lambda
      _fidx = xfidx;
      FUNS.put(_fidx,this);
    }
    @Override SB str(SB sb) {
      sb.p("{ ");
      for( String arg : _args ) sb.p(arg).p(' ');
      return _body.str(sb.p("-> ")).p(" }");
    }
    @Override SB p1(SB sb, VBitSet dups) {
      sb.p("{ ");
      for( int i=0; i<_args.length; i++ ) {
        sb.p(_args[i]);
        if( DO_HM  ) _targs[i].str(sb.p(", HMT=" ),new VBitSet(),dups,true);
        if( DO_GCP ) sb.p(", GCP=").p(_types[i]);
        sb.nl().i().p("  ");
      }
      return sb.p(" -> ... } ");
    }
    @Override SB p2(SB sb, VBitSet visit, VBitSet dups) { return _body.p0(sb,visit,dups); }
    @Override public T2 as_fun() { return find(); }
    @Override public int nargs() { return _types.length; }
    public Ident[] refs(int idx) {
      if( idx>=_refs.length ) return null; // Happens for too-many-args cases
      if( _refs[idx]==null ) {
        if( !(this instanceof PrimSyn ) )
          return null; // CNC: TODO: Do this when cloning prims during parse
        Ident id = new Ident(_args[idx]);
        id.init(this,idx,targ(idx),false)._hmt = id._idt;
        id._par = this;
        _refs[idx] = new Ident[]{id};
      }
      assert _refs[idx].length>0; // At least 1 referring to call arg_meet
      return _refs[idx];
    }
    public boolean extsetf(int argn) { boolean old = _extsetf[argn]; _extsetf[argn] = true; return old; }
    public boolean extsetp(int argn) { boolean old = _extsetp[argn]; _extsetp[argn] = true; return old; }
    @Override public void apply_push(Apply apl, Work<Syntax> work) {
      if( _applys.find(apl) != -1 ) return;
      if( work==null ) return;  // Progress
      // New apply discovered
      _applys.push(apl);
      // First time arg_meet for new apply
      for( int i=0; i<nargs(); i++ )
        work.add(refs(i));
    }
    @Override public T2 targ(int i) { T2 targ = _targs[i].find(); return targ==_targs[i] ? targ : (_targs[i]=targ); }
    @Override boolean hm(Work<Syntax> work) {
      // The normal lambda work
      T2 old = find();
      boolean progress = false;
      for( int i=0; i<_targs.length; i++ ) {
        T2 formal = old.arg(ARGNAMES[i]);
        if( formal!=null )      // Can be null if some apply has arg counts wrong
          progress |= formal.unify(targ(i),work);
      }
      progress |= old.arg(RET).unify(_body.find(),work);
      return progress;
    }
    @Override void add_hm_work( @NotNull Work<Syntax> work) { throw unimpl(); }
    @Override Type val(Work<Syntax> work) {
      // Just wrap a function around the body return
      return TypeFunPtr.makex(false,BitsFun.make0(_fidx),_args.length+DSP_IDX,Type.ANY,_body._flow);
    }
    // Meet the formal argument# with a new Apply call site actual arg.
    public void arg_meet(int argn, Type cflow, Work<Syntax> work) {
      if( argn >= _types.length ) return; // Bad argument count
      Type old = _types[argn];
      Type mt = old.meet(cflow);
      if( mt==old ) return;     // No change
      if( work==null ) return;
      _types[argn]=mt;          // Yes change, update
      work.add(_refs[argn]);    // And revisit referrers
      if( this instanceof PrimSyn ) work.add(this); // Primitives recompute
      // Changing _types in Pair or Triple might escape the result
      if( this instanceof Alloc alloc && Root.ext_aliases().test(alloc.alias()) &&
          (mt instanceof TypeMemPtr || mt instanceof TypeFunPtr) )
        work.add(ROOT);
      // Changing _types in Pair or Triple updates referring fields
      if( this instanceof Alloc alloc )
        work.addAll(alloc.rflds());
    }

    // Ignore arguments, and return body type for a particular call site.  Very conservative.
    Type apply(Type[] flows) { throw unimpl(); }
    @Override void add_val_work(Syntax child, @NotNull Work<Syntax> work) {
      work.add(this);
      // Body changed, all Apply sites need to recompute
      work.addAll(_applys);
    }
    @Override int prep_tree( Syntax par, VStack nongen, Work<Syntax> work ) {
      // Prep self
      prep_tree_impl(par,nongen,work,T2.make_leaf());
      // Extend the nongen set by the new variables
      VStack vs = nongen;
      for( T2 targ : _targs ) vs = new VStack(vs, targ);
      // Prep the body
      int cnt = _body.prep_tree(this,vs,work) + 1;
      // Go ahead and pre-unify with a required function
      T2[] targs = Arrays.copyOf(_targs,_targs.length+1);
      targs[_targs.length] = _body.find();
      targs[_targs.length].push_update(this); // Return has a dep on Lambda to support spreading _is_copy
      find().unify(T2.make_fun(targs),work);
      // If this is a NotNil, rename the arg for clarity (no semantic change,
      // no alpha capture).
      if( _par instanceof Apply app0 &&
          app0._args.length==1 && app0._args[0] instanceof Apply app1 &&
          app1._fun instanceof NotNil ) {
        String nid = _args[0] = (" _"+_args[0]).intern(); // Harmless name change
        if( _refs[0]!=null )  for( Ident id : _refs[0] )  id._name = nid;
      }
      return cnt;
    }
    @Override int prep_lookup_deps(Ident id, Syntax prior) {
      for( int i=0; i<_args.length; i++ )
        if( Util.eq(_args[i],id._name) ) {
          // Deps are based on T2, and trigger when the HM types change
          _targs[i].push_update(id); //
          // Refs are based on Syntax, basically a wimpy SSA for GCP propagation
          Ident[] refs = _refs[i];
          if( refs==null ) _refs[i] = refs = new Ident[0];
          // Hard linear-time append ident to the end.  Should be very limited in size.
          _refs[i] = refs = Arrays.copyOf(refs,refs.length+1);
          refs[refs.length-1] = id;
          return i;
        }
      return -99;
    }
    @Override boolean more_work(Work<Syntax> work) {
      if( !more_work_impl(work) ) return false;
      return _body.more_work(work);
    }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      T rez = map.apply(this);
      // Primitives have no body
      return _body==null ? rez : reduce.apply(rez,_body.visit(map,reduce));
    }
  }

  static class Let extends Syntax {
    final String _arg0;
    Syntax _def, _body;
    Syntax[] _refs;               // Identifiers referring here
    Let(String arg0, Syntax def, Syntax body) { _arg0=arg0; _body=body; _def=def; _refs=new Ident[0]; }
    @Override SB str(SB sb) { return _body.str(_def.str(sb.p(_arg0).p(" = ")).p("; ")); }
    @Override SB p1(SB sb, VBitSet dups) { return sb.p(_arg0).p(" = ... ; ..."); }
    @Override SB p2(SB sb, VBitSet visit, VBitSet dups) { _def.p0(sb,visit,dups); return _body.p0(sb,visit,dups); }
    T2 targ() { return _def.find(); }
    @Override boolean hm(Work<Syntax> work) { return false;  }
    @Override void add_hm_work( @NotNull Work<Syntax> work) { throw unimpl();  }
    @Override Type val(Work<Syntax> work) { return _body._flow; }
    // Definition changed; all dependents need to revisit
    @Override void add_val_work( Syntax child, @NotNull Work<Syntax> work) {
      if( child==_def ) work.add(_refs);
      else              work.add(this);
    }

    @Override int prep_tree( Syntax par, VStack nongen, Work<Syntax> work ) {
      prep_tree_impl(par,nongen,work,T2.make_leaf());
      T2 targ = T2.make_leaf();
      int cnt = _def .prep_tree(this,new VStack(nongen,targ),work) +
                _body.prep_tree(this,           nongen      ,work);
      targ.unify(targ(),work);       // Unify targ with _def._hmt
      _hmt.unify(_body.find(),work); // Unify 'Let._hmt' with the '_body'
      return cnt+1;
    }
    @Override int prep_lookup_deps(Ident id, Syntax prior) {
      if( !Util.eq(id._name,_arg0) ) return -99;
      // Deps are based on T2, and trigger when the HM types change
      targ().push_update(id);
      // Refs are based on Syntax, basically a wimpy SSA for GCP propagation
      // Hard linear-time append ident to the end.  Should be very limited in size.
      _refs = Arrays.copyOf(_refs,_refs.length+1);
      _refs[_refs.length-1] = id;
      assert prior==_def || prior==_body;
      return prior==_def ? -1 : -2;
    }
    @Override boolean more_work(Work<Syntax> work) {
      if( !more_work_impl(work) ) return false;
      return _body.more_work(work) && _def.more_work(work);
    }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      T rez = map.apply(this);
      T def = reduce.apply(rez,_def .visit(map,reduce));
      return  reduce.apply(def,_body.visit(map,reduce));
    }
  }


  static class Apply extends Syntax {
    Syntax _fun;
    final Syntax[] _args;
    private Type _old_lift = Type.ANY; // Assert that apply-lift is monotonic

    Apply(Type flow, Syntax fun) { super(flow); _fun = fun; _args = new Syntax[0]; }
    Apply(Syntax fun, Syntax... args) { _fun = fun; _args = args; }
    @Override SB str(SB sb) {
      _fun.str(sb.p("(")).p(" ");
      for( Syntax arg : _args )
        arg.str(sb).p(" ");
      return sb.unchar().p(")");
    }
    @Override SB p1(SB sb, VBitSet dups) { return sb.p("(...)"); }
    @Override SB p2(SB sb, VBitSet visit, VBitSet dups) {
      _fun.p0(sb,visit,dups);
      for( Syntax arg : _args ) arg.p0(sb,visit,dups);
      return sb;
    }

    // Unifying these: make_fun(this.arg0 this.arg1 -> new     )
    //                     _fun{_fun.arg0 _fun.arg1 -> _fun.rez}
    @Override boolean hm(Work<Syntax> work) {
      boolean progress = false;
      // Progress if:
      //   _fun is not a function
      //   any arg-pair-unifies make progress
      //   this-unify-_fun.return makes progress
      T2 tfun = _fun.find();

      if( !tfun.is_fun() ) {    // Not a function, try to make it one
        T2 nfun = make_nfun();
        progress = tfun.unify(nfun,work); // Unify.
        if( work==null )                  // Just testing, but did an allocation for the trial
          { nfun.free(); return progress; }
        tfun = nfun.find();

      } else {                  // function, unify by parts

        // Check for progress amongst arg pairs
        int miss=0;
        for( int i=0; i<_args.length; i++ ) {
          T2 actual = _args[i].find();
          T2 formal = tfun.arg(Lambda.ARGNAMES[i]);
          progress |= formal==null && !tfun.is_err()
            ? find().unify_errs("Bad arg count ",work) // more args than the lambda takes
            : actual.unify(formal,work);
          if( formal==null ) miss++;                //
          if( progress && work==null ) return true; // Will-progress & just-testing early exit
          tfun = tfun.find();
        }
        if( (tfun.size()-1)-(_args.length-miss) > 0 && !tfun.is_err() )
          progress |= tfun.unify_errs("Bad arg count ",work); // less args than the lambda takes
        // Check for progress on the return
        progress |= find().unify(tfun.arg(RET),work);
        tfun=tfun.find();
      }

      // Errors are poisonous
      progress |= find().unify_errs(tfun._err,work);

      // Flag HMT result as widening, if GCP falls to a TFP which widens in HMT.
      T2 tret = tfun.arg(RET);
      if( tret!=null && tret._is_copy && _fun._flow instanceof TypeFunPtr tfp ) {
        for( int fidx : tfp.pos() )
          if( fidx!=BitsFun.ALLX && !Lambda.FUNS.get(fidx).as_fun().arg(RET)._is_copy ) {
            if( work!=null ) tret.clr_cp(work);
            return true;
          }
      }

      return progress;
    }
    // Make a new T2 fun for the Apply
    private T2 make_nfun() {
      T2[] targs = new T2[_args.length+1];
      for( int i=0; i<_args.length; i++ )
        targs[i] = T2.make_leaf();
      targs[_args.length] = find(); // Return
      T2 fun = T2.make_fun(targs);
      fun._err = find()._err;
      fun.push_update(this); // TODO
      return fun; // TODO
    }
    @Override void add_hm_work( @NotNull Work<Syntax> work) {
      work.add(_par);
      work.add(_args);
    }

    @Override Type val(Work<Syntax> work) {
      Type flow = _fun._flow;
      if( !(flow instanceof TypeFunPtr tfp) )
        return flow.oob(TypeNil.SCALAR);

      // Meet arguments to Lambda args.  This code appears in Ident as well,
      // but is needed here in case the arg is unused in the Lambda body.
      if( work!=null && !tfp.is_full() )
        arg_meet(tfp,work);

      // Attempt to lift the result, based on HM types.
      Type lifted = DO_HM
        ? do_apply_lift(find(),tfp, work==null)
        : tfp._ret;
      assert _flow.isa(lifted); // Monotonic...
      return lifted;
    }

    void arg_meet(TypeFunPtr tfp, Work<Syntax> work) {
      assert !tfp.above_center();
      for( int fidx : tfp.fidxs() ) {
        Func func = Lambda.FUNS.get(fidx);
        func.apply_push(this,work);      // External functions gather escaping arguments
        if( func instanceof Lambda lam ) // Filter out external lambdas
          for( int i=0; i<_args.length; i++ ) {
            Type t = this instanceof Root
              ? lam.targ(i).as_flow(null,false)
              : _args[i]._flow;
            lam.arg_meet(i,t,work); // Internal functions gather meet of all args
          }
      }
    }

    // Gate around apply_lift.  Assert monotonic lifting and apply the lift.
    Type do_apply_lift(T2 rezt2, TypeFunPtr tfp, boolean test) {
      Type ret = tfp._ret;
      if( !DO_HM ) return ret;
      if( ret==TypeNil.XSCALAR ) return ret; // Nothing to lift
      if( rezt2.is_err() )       return ret; // Do not lift errors
      Type lift = hm_apply_lift(rezt2, tfp, test);
      assert _old_lift.isa(lift); // Lift is monotonic
      _old_lift=lift;             // Record updated lift
      if( lift==ret ) return ret; // No change
      if( !test ) rezt2.push_update(this);
      return ret.join(lift);      // Lifted result
    }

    // Walk the input HM type and CCP flow type in parallel and create a
    // mapping.  Then walk the output HM type and CCP flow type in parallel,
    // and join output CCP types with the matching input CCP type.
    Type hm_apply_lift(T2 rezt2, TypeFunPtr tfp, boolean test) {
      // Walk the input types, finding all the Leafs.  Repeats of the same Leaf
      // has its flow Types MEETed.
      T2.T2_MAY_NEW_LEAF.clear(); // Assume new leafs can appear
      T2.T2MAP.clear();
      for( Syntax arg : _args ) {
        T2.WDUPS.clear(true);
        arg.find().walk_types_in(arg._flow);
      }
      // Then walk the output types, building a corresponding flow Type, but
      // matching against input Leafs.  If HM_FREEZE Leafs must match
      // exactly, replacing the input flow Type with the corresponding flow
      // Type.  If !HM_FREEZE, replace with a join of flow types.
      T2.WDUPS.clear(true);
      return rezt2.walk_types_out(tfp._ret, this, test);
    }

    @Override void add_val_work( Syntax child, @NotNull Work<Syntax> work) {
      // push self, because self returns the changed-functions' ret.
      // push self, because the changed-functions' FIDXS might need to notice new Call Graph edge.
      if( child==_fun ) { work.add(this); return; }

      if( DO_HM ) work.add(this); // Child input fell, parent may lift less

      // Overloads mean any function anywhere might sharpen an Apply
      if( child instanceof Lambda lam )
        work.addAll(lam._applys);

      // Check for some Lambdas present
      Type flow = _fun._flow;
      if( !(flow instanceof TypeFunPtr tfp) ) return;

      // child arg to a call-site changed; find the arg#;
      int argn = Util.find(_args,child);
      // visit all Lambdas; meet the child flow into the Lambda arg#
      if( argn != -1 && !tfp.is_full() )
        for( int fidx : tfp.fidxs() )
          if( Lambda.FUNS.get(fidx) instanceof Lambda lam )
            work.add(lam.refs(argn));
    }

    @Override int prep_tree(Syntax par, VStack nongen, Work<Syntax> work) {
      prep_tree_impl(par,nongen,work,T2.make_leaf());
      int cnt = 1+_fun.prep_tree(this,nongen,work);
      for( int i=0; i<_args.length; i++ )
        cnt += _args[i].prep_tree(this,nongen,work);
      return cnt;
    }

    @Override boolean more_work(Work<Syntax> work) {
      if( !more_work_impl(work) ) return false;
      if( !_fun.more_work(work) ) return false;
      for( Syntax arg : _args ) if( !arg.more_work(work) ) return false;
      return true;
    }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      T slf = map.apply(this);
      T rez = reduce.apply(slf,_fun.visit(map,reduce));
      for( Syntax arg : _args )
        rez = reduce.apply(rez,arg.visit(map,reduce));
      return rez;
    }
  }


  // -----------------
  // All the Functions and Structs in the Universe, called with the Program
  // result as the argument.  The result of this is used by Root as the
  // possible arguments.
  //   while( !fixedpoint ) {
  //     prog_result = Root(external_args);
  //     external_args = (External prog_result);
  //   }
  static class Root extends Apply {
    private static BitsAlias EXT_ALIASES = BitsAlias.EMPTY;
    private static BitsFun   EXT_FIDXS   = BitsFun  .EMPTY;
    private static final Work<Syntax> NEW_LEAF_DEPS = new Work<>();
    private static final Work<Syntax> FREEZE_DEPS = new Work<>();
    private static final Work<Syntax> EXT_DEPS = new Work<>();
    static final Ary<EXTLambda> EXTS = new Ary<>(EXTLambda.class);
    static void reset() {
      EXT_ALIASES = BitsAlias.EMPTY;
      EXT_FIDXS = BitsFun.EMPTY;
      NEW_LEAF_DEPS.clear();
      FREEZE_DEPS.clear();
      EXT_DEPS.clear();
      EXTS.clear();
      // Default, external 1,2,3 arg functions
      EXTS.push(null);
      EXTS.push(new EXTLambda(T2.make_fun(T2.make_leaf()),null));
      EXTS.push(new EXTLambda(T2.make_fun(T2.make_leaf(),T2.make_leaf()),null));
      EXTS.push(new EXTLambda(T2.make_fun(T2.make_leaf(),T2.make_leaf(),T2.make_leaf()),null));
    }
    public static BitsAlias ext_aliases() { return EXT_ALIASES; }
    public static BitsFun   ext_fidxs  () { return EXT_FIDXS  ; }
    private static <B extends Bits<B>> B add_ext( int x, Work<Syntax> work, B b ) {
      if( b.test(x) ) return b;
      if( work!=null ) work.add(ROOT);
      return b.set(x);
    }
    static void add_ext_alias(int alias, Work<Syntax> work) { assert alias!=1; EXT_ALIASES = add_ext(alias,work,EXT_ALIASES); }
    static void add_ext_fidx (int fidx , Work<Syntax> work) { EXT_FIDXS   = add_ext(fidx ,work,EXT_FIDXS  ); }

    public Root(Syntax body) { super(Type.ANY,body); }
    @Override boolean hm(final Work<Syntax> work) {
      assert debug_find()==_fun.debug_find();
      return false;
    }
    @Override void add_hm_work( @NotNull Work<Syntax> work) { throw unimpl(); }
    @Override Type val(Work<Syntax> work) {
      // arg_meet Root-called Lambdas with Root args.
      if( _fun._flow instanceof TypeFunPtr tfp )
        arg_meet(tfp,work);

      if( work!=null )
        escapes(_fun._flow,work);
      TypeMemPtr tmp = TypeMemPtr.make(false,EXT_ALIASES,TypeStruct.ISUSED);
      TypeFunPtr tfp = TypeFunPtr.make(EXT_FIDXS,1);
      return TypeTuple.make(_fun._flow,tmp,tfp);
    }
    @Override void add_val_work( Syntax child, @NotNull Work<Syntax> work) { work.add(this); }

    // Add new aliases and fidxs to worklist
    void add_val_work( Type old, @NotNull Work<Syntax> work) {
      BitsAlias old_aliases = old instanceof TypeTuple tup ? ((TypeMemPtr)tup.at(1))._aliases : BitsAlias.EMPTY;
      BitsFun   old_fidxs   = old instanceof TypeTuple tup ? ((TypeFunPtr)tup.at(2)).fidxs()  : BitsFun  .EMPTY;
      for( int alias : EXT_ALIASES )
        if( !old_aliases.test(alias) &&
            ALIASES.at(alias) instanceof Syntax syn )
          work.add(syn);

      for( int fidx : EXT_FIDXS )
        if( !old_fidxs.test(fidx) &&
            Lambda.FUNS.get(fidx) instanceof Syntax syn )
          work.add(syn);
      // Revisit fields depending on escaped values
      work.addAll(EXT_DEPS);
    }

    Type flow_type() { return sharpen(((TypeTuple)_flow)._ts[0]); }

    @Override int prep_tree(Syntax par, VStack nongen, Work<Syntax> work) {
      prep_tree_impl(par,nongen,work,null);
      int cnt = 1+_fun.prep_tree(this,nongen,work);
      _hmt = _fun.find();
      return cnt;
    }

    void add_new_leaf_work(Work<Syntax> work) {
      work.addAll(NEW_LEAF_DEPS);
      NEW_LEAF_DEPS.clear();
    }

    void add_ambi_work(Work<Syntax> work) {
      for( Field fld : Field.FIELDS.values() )
        if( Field.is_resolving(fld._id) ) {
          fld.find().unify_errs("Unresolved field "+fld._id,work);
          fld.find().clr_cp(work);
          work.add(fld);        // Type changes as well
          work.addAll(fld.find()._deps);
        }

    }

    void add_freeze_work(Work<Syntax> work) {
      // Freezing HM; all escaped function arguments get called with the most
      // conservative args compatible with their HM types.
      for( int fidx : EXT_FIDXS ) {
        if( Lambda.FUNS.get(fidx) instanceof Lambda lam ) {
          for( int i=0; i<lam.nargs(); i++ )
            work.add(lam.refs(i));
        }
      }

      // All Applys that are lifting with HM, now lift less.
      if( DO_HM )
        for( Func func : Lambda.FUNS.values() )
          if( func instanceof Lambda lam )
            work.addAll(lam._applys);

      work.addAll(FREEZE_DEPS);
      FREEZE_DEPS.clear();
    }

    static BitsAlias matching_escaped_aliases(T2 t2) {
      BitsAlias aliases = BitsAlias.EMPTY;
      for( int alias : EXT_ALIASES )
        if( t2.trial_unify_ok(ALIASES.at(alias).t2(),false) )
          aliases = aliases.set(alias); // Compatible escaping alias
      return aliases;
    }

    static BitsFun matching_escaped_fidxs(T2 t2) {
      assert t2.is_fun();
      BitsFun fidxs = BitsFun.EMPTY;
      // Always poison the BitsFun with a FIDX which always has clr_cp/!_is_copy.
      EXTLambda elam = Root.EXTS.atX(t2.nargs());
      if( elam==null ) throw unimpl();
      fidxs = fidxs.set(elam._fidx);
      // Cannot ask for trial_unify_ok until HM_FREEZE, because trials can fail
      // over time which runs the result backwards in GCP.
      if( HM_FREEZE )
        for( int fidx : EXT_FIDXS ) {
          Func fun = Lambda.FUNS.get(fidx);
          // Dunno (yet), since trial_unify_ok can pass, then filter as HM proceeds
          if( t2.trial_unify_ok(fun.as_fun(),false) )
            fidxs = fidxs.set(fidx); // Compatible escaping fidx
        }
      return fidxs;
    }

    // Escape all Root results.  Escaping functions are called with the most
    // conservative HM-compatible arguments.  Escaping Structs are recursively
    // escaped, and can appear as input arguments.
    private static final VBitSet ESCP = new VBitSet(), ESCF = new VBitSet();
    private void escapes(Type t, Work<Syntax> work) {
      ESCP.clear();  ESCF.clear();
      _escapes(t,work);
    }
    private void _escapes(Type t, Work<Syntax> work) {
      if( t instanceof TypeMemPtr tmp ) {
        // Add to the set of escaped structures
        for( int alias : tmp._aliases ) {
          if( ESCP.tset(alias) ) continue;
          add_ext_alias(alias,work);
          Alloc a = ALIASES.at(alias);
          _escapes(a.tmp()._obj,work);
        }
      }
      if( t instanceof TypeStruct ts )
        for( TypeFld fld : ts )
          if( !Util.eq(fld._fld,"^") )
            _escapes(fld._t,work);
      if( t instanceof TypeFunPtr tfp && !ESCF.tset(tfp._uid) ) {
        // Walk all escaped function args, and call them (like an external
        // Apply might) with the most conservative flow arguments possible.
        // Escaping overloads only count after freezing.
        for( int fidx : tfp.pos() )
          do_fidx(fidx, work);
        // The flow return also escapes
        _escapes(tfp._ret,work);
      }
    }

    private void do_fidx( int fidx, Work<Syntax> work ) {
      if( ESCF.tset(fidx) ) return; // Been there, done that
      if( Lambda.FUNS.get(fidx) instanceof Lambda lam )
        lam.apply_push(this,work);
      add_ext_fidx(fidx,work);
    }

  }

  // External Struct: every possible Struct in the Universe that might be
  // passed in to any escaping Lambda, with compatible T2 structure.
  // These are made in response to Field loads against escaping T2s
  static class EXTStruct implements Alloc {
    final int _alias;
    T2 _t2;
    EXTStruct(T2 t2, Work<Syntax> work) { this(t2,BitsAlias.new_alias(BitsAlias.EXTX),work); }
    EXTStruct(T2 t2, int alias, Work<Syntax> work) {
      assert t2.is_ptr();
      _t2 = t2;
      _alias = alias;
      ALIASES.setX(alias,this);
      Root.add_ext_alias(alias,work);
    }
    @Override public String toString() { return "["+_alias+"]"+_t2; }
    @Override public T2 t2() { return (_t2 = _t2.find()); }
    @Override public int alias() { return _alias; }
    @Override public TypeMemPtr tmp() {
      Type t = _t2.as_flow(null,HM_FREEZE);
      // Can be Scalar if the T2 type is_err
      return t instanceof TypeMemPtr tmp ? tmp : t.oob(TypeMemPtr.ISUSED);
    }
    // Never fails, since made with a compatible T2 in the first place
    @Override public Type fld(String id, Syntax fld) {
      T2 tfld = t2().get("*").arg(id);
      if( tfld==null ) return null;
      Root.FREEZE_DEPS.add(fld); // Depends on HM_FREEZE
      return tfld.as_flow(fld,false);
    }
    @Override public Ary<Syntax> rflds() { return null; }
    @Override public Type meet() { return TypeNil. SCALAR; }
    @Override public Type join() { return TypeNil.XSCALAR; }
  }

  // External function: any function from outside of Root this program might get handed.
  static class EXTLambda implements Func {
    final int _fidx;
    final T2 _t2;
    EXTLambda(T2 t2, Work<Syntax> work) {
      assert t2.is_fun();
      _t2 = t2;
      _fidx = BitsFun.new_fidx(BitsFun.EXTX);
      Lambda.FUNS.put(_fidx,this);
      Root.add_ext_fidx(_fidx,work);
    }
    @Override public String toString() { return "ext lambda"; }
    @Override public T2 as_fun() { return _t2.find(); }
    @Override public int nargs() { return as_fun().nargs(); }
    @Override public T2 targ(int argn) { throw unimpl(); }
    @Override public void apply_push(Apply aply, Work<Syntax> work) {
      // all these args escape
      if( work!=null )
        for( Syntax syn : aply._args )
          ROOT.escapes(syn._flow,work);
    }
  }


  // Expand functions to full signatures, recursively.
  // Used by testing.
  private static final VBitSet ADD_SIG = new VBitSet();
  private static TypeMem ASIG_MEM;
  static Type sharpen(Type t) {
    ADD_SIG.clear();
    TypeStruct[] ts = new TypeStruct[ALIASES._len];
    ts[1] = TypeStruct.ISUSED;
    for( int i=2; i<ALIASES._len; i++ ) {
      Alloc a = ALIASES.at(i);
      if( a!= null ) ts[i] = a.tmp()._obj;
    }
    ASIG_MEM = TypeMem.make0(ts);
    return add_sig(t);
  }
  private static Type add_sig(Type t) {
    if( ADD_SIG.tset(t._uid) ) return t;
    if( t instanceof TypeMemPtr tmp )
      return tmp.is_str() ? t : ASIG_MEM.sharpen(tmp); // Special string hack
    if( t instanceof TypeFunPtr fun )
      return fun.make_from(fun.dsp(),add_sig(fun._ret));
    return t;
  }


  // Structure or Records.
  static class Struct extends Syntax implements Alloc {
    final int _alias;
    final String[]  _ids;
    final Syntax[] _flds;
    final Ary<Syntax> _rflds = new Ary<>(Syntax.class);
    Struct( boolean user, String[] ids, Syntax[] flds ) {
      // Sort fields by name.  They are otherwise unordered.
      TreeMap<String,Syntax> sort = new TreeMap<>();
      for( int i=0; i<ids.length; i++ ) sort.put(ids[i], flds[i]);
      int i=0; for( Map.Entry<String,Syntax> e : sort.entrySet() )
                 { ids[i]=e.getKey(); flds[i]=e.getValue(); i++; }
      _ids=ids;
      _flds=flds;
      // Make a TMP
      _alias = user ? BitsAlias.new_alias(BitsAlias.INTX) : -1;
      if( user ) ALIASES.setX(_alias,this);
    }
    @Override SB str(SB sb) {
      sb.p("@{");
      for( int i=0; i<_ids.length; i++ ) {
        sb.p(' ').p(_ids[i]).p(" = ");
        _flds[i].str(sb);
        if( i < _ids.length-1 ) sb.p(';');
      }
      return sb.p("}");
    }
    @Override SB p1(SB sb, VBitSet dups) { return sb.p("@{").p(_alias).p(" ... } "); }
    @Override SB p2(SB sb, VBitSet visit, VBitSet dups) {
      for( int i=0; i<_ids.length; i++ )
        _flds[i].p0(sb.i().p(_ids[i]).p(" = ").nl(),visit,dups);
      return sb;
    }
    @Override public T2 t2() { return find(); }
    @Override public int alias() { return _alias; }
    @Override public TypeMemPtr tmp() {
      Type[] ts = new Type[_flds.length];
      for( int i=0; i<_flds.length; i++ )
        ts[i] =_flds[i]._flow;
      return _tmp(_alias,_ids,ts);
    }
    @Override public Type fld(String id, Syntax fld) {
      int idx = Util.find(_ids,id);
      return idx==-1 ? null : _flds[idx]._flow;
    }
    @Override public Ary<Syntax> rflds() { return _rflds; }
    @Override boolean hm(Work<Syntax> work) {
      // Force result to be a struct with at least these fields.
      // Do not allocate a T2 unless we need to pick up fields.
      T2 ptr = find();
      T2 rec = ptr.arg("*");
      rec.push_update(this);

      // Unify existing fields.  Ignore extras on either side.
      boolean progress = false;
      for( int i=0; i<_ids.length; i++ ) {
        T2 fld = rec.arg(_ids[i]);
        if( fld!=null ) progress |= fld.unify(_flds[i].find(),work);
        if( work==null && progress ) return true;
      }

      return progress;
    }
    @Override void add_hm_work( @NotNull Work<Syntax> work) {
      work.add(_par);
      work.add(_flds);
    }
    @Override Type val(Work<Syntax> work) {
      return TypeMemPtr.make(_alias,TypeStruct.ISUSED);
    }
    @Override void add_val_work(Syntax child, @NotNull Work<Syntax> work) {
      work.addAll(_rflds);
      // Set a field in an escaped structure, need to re-compute escapes
      if( Root.ext_aliases().test(_alias) ) work.add(ROOT);
    }

    @Override public Type meet() {
      Type t = TypeNil.XSCALAR;
      for( Syntax syn : _flds )
        t = t.meet(syn._flow);
      return t;
    }
    @Override public Type join() {
      Type t = TypeNil.SCALAR;
      for( Syntax syn : _flds )
        t = t.join(syn._flow);
      return t;
    }

    @Override int prep_tree(Syntax par, VStack nongen, Work<Syntax> work) {
      T2 hmt = T2.make_open_struct(null,null);
      prep_tree_impl(par, nongen, work, T2.make_ptr(hmt));
      int cnt = 1;              // One for self
      if( _ids.length!=0 ) hmt._args = new NonBlockingHashMap<>();
      assert hmt._deps==null;
      for( int i=0; i<_ids.length; i++ ) { // Prep all sub-fields
        cnt += _flds[i].prep_tree(this,nongen,work);
        hmt._args.put(_ids[i],_flds[i].find());
      }
      assert  hmt.is_obj();
      return cnt;
    }

    @Override boolean more_work(Work<Syntax> work) {
      if( !more_work_impl(work) ) return false;
      for( Syntax fld : _flds )
        if( !fld.more_work(work) )
          return false;
      return true;
    }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      T rez = map.apply(this);
      for( Syntax fld : _flds )
        rez = reduce.apply(rez,fld.visit(map,reduce));
      return rez;
    }
  }

  // Field lookup in a Struct or Overload.
  // Does Overload field resolution on overloads.
  static class Field extends Syntax {
    private static final HashMap<String,Field> FIELDS = new HashMap<>();
    static void reset() { FIELDS.clear(); }
    
    String _id;
    final Syntax _ptr;
    Field( String id, Syntax str ) {
      _ptr = str;
      if( id==null ) FIELDS.put(id=("&"+_uid).intern(),this);
      _id=id; 
    }
    @Override SB str(SB sb) {   return  _ptr.str(sb).p(".").p(is_resolving() ? "_" : _id); }
    @Override SB p1(SB sb, VBitSet dups) { return sb.p(".").p(is_resolving() ? "_" : _id); }
    @Override SB p2(SB sb, VBitSet visit, VBitSet dups) { return _ptr.p0(sb,visit,dups); }
    static boolean is_resolving(String id) { return id.charAt(0)=='&'; }
    boolean is_resolving() { return is_resolving(_id); }
    @Override boolean hm(Work<Syntax> work) {
      T2 ptr = _ptr.find();
      if( work!=null ) ptr.push_update(this);

      // Get the pointed-at struct.
      // If not a ptr, make it one (which might trigger an error).
      T2 rec = ptr.arg("*");
      if( rec==null ) {
        if( ptr.is_base() )     // Short-cut to a nicer error
          return find().unify_miss_fld(_id,work);
        if( work==null ) return true;
        if( ptr._args ==null ) ptr._args = new NonBlockingHashMap<>();
        ptr._args.put("*", rec = T2.make_leaf());
        rec._deps = ptr._deps.deepCopy();
      }

      // Add struct-ness
      if( !rec.is_obj() ) {
        if( work==null ) return true;
        rec._open = true;
        rec._is_obj = true;
        if( rec._args==null ) rec._args = new NonBlockingHashMap<>();
      }
      assert rec.is_obj();

      // Attempt resolve
      boolean progress=false;
      if( is_resolving() && !rec.is_open() ) {
        progress = trial_resolve(find(), rec, rec, work);
        if( progress && work==null ) return true;
      }
      
      // Look up field
      T2 fld = rec.arg(_id);
      T2 self = find();
      if( fld!=null )           // Unify against a pre-existing field
        return (self.unify_errs(ptr._err,work) & fld.unify(self, work)) | progress;

      // If field is doing overload resolution, inject even if rec is closed
      if( is_resolving() ) {
        if( work==null ) return true;
        rec._args.put(_id,self);
        rec.push_update(this);
        rec.merge_deps(self,work);
        return true;
      }
      
      // If field must be there, and it is not, then it is missing
      if( !rec.is_open() )
        self.unify_miss_fld(_id,work);

      // Add the field
      return work==null || rec.add_fld(_id,self,work);
    }
    @Override void add_hm_work( @NotNull Work<Syntax> work) {
      work.add(_par);
      work.add(_ptr);
      _ptr.add_hm_work(work);
    }

    @Override Type val(Work<Syntax> work) {
      Type trec = _ptr._flow;
      if( trec==TypeNil.NIL ) return TypeNil.XSCALAR; // Field from nil
      if( !(trec instanceof TypeMemPtr tmp) ) return trec.oob(TypeNil.SCALAR);
      // GCP takes meet of aliased fields
      Type t=TypeNil.XSCALAR, afld=null;
      assert !tmp._aliases.test(BitsAlias.ALLX);
      for( int alias : tmp._aliases ) {
        if( alias==0 ) continue; // May be nil error
        Alloc alloc = ALIASES.at(alias);
        if( is_resolving() ) {  // Field is resolving an overload
          // Still resolving, use the join of fields.
          afld = HM_AMBI ? alloc.meet() : alloc.join();
        } else {
          // Get field to meet
          afld = alloc.fld(_id,this);
          // Field is missing in alias, could be for many reasons
          if( afld==null ) afld = missing_field(alloc);
        }
        t = t.meet(afld);
        if( work!=null ) {
          Ary<Syntax> rflds = alloc.rflds();
          if( rflds != null ) rflds.push(this);
        }
      }
      return t;
    }

    // Handler for missing field
    private Type missing_field(Alloc alloc) {
      T2 t2rec = alloc.t2().get("*");
      T2 t2fld = t2rec.arg(_id);
      // Field from wrong alias (ignore/XSCALAR should not affect GCP field type),
      if( t2fld==null ) {
        if( !HM_FREEZE ) Root.FREEZE_DEPS.add(this); // Revisit when HM_FREEZE flips
        return TypeNil.SCALAR.oob(!HM_FREEZE);
      }
      // HMT tells us the field is missing
      assert t2fld.is_err();
      return TypeNil.SCALAR;
    }

    @Override void add_val_work(Syntax child, @NotNull Work<Syntax> work) { work.add(this); }
    @Override int prep_tree(Syntax par, VStack nongen, Work<Syntax> work) {
      prep_tree_impl(par, nongen, work, T2.make_leaf());
      return _ptr.prep_tree(this,nongen,work)+1;
    }
    // Attempt to resolve all unresolved labels in a struct
    static boolean trial_resolve_all(T2 obj, Work<Syntax> work) {
      if( obj._args==null || !obj.is_obj() ) return false;
    
      // If already resolved, just update-in-place
      boolean progress = false;
      for( String key : obj._args.keySet() ) {
        if( !is_resolving(key) ) continue;
        Field fld = FIELDS.get(key);
        if( fld.is_resolving() ) {
          if( !obj.is_open() ) // More fields possible, so trial_resolve cannot be tried
            progress |= trial_resolve(key,obj.arg(key),obj,obj,work); // Attempt resolve
        } else {
          // key is resolving, but Field is already resolved
          if( work==null ) continue; // Make no changes, but do not declare progress: this is a lazy update
          T2 old = obj._args.remove(key); // Remove resolving key
          T2 t2 = obj.arg(fld._id);       // Get resolved label, if any
          if( t2==null ) obj._args.put(fld._id,old); // Insert resolved-label, even if obj is open, since this is a label replacement
          else progress |= old.find().unify(t2,work); // Unify into existing (fold labels together)
        }
      }
      
      return progress;
    }
    
    // Attempts resolve a field; if so updates 'obj' accordingly.
    static boolean trial_resolve(String key, T2 pat, T2 lhs, T2 rhs, Work<Syntax> work) { return FIELDS.get(key).trial_resolve(pat,lhs, rhs, work); }
    boolean trial_resolve(T2 pat, T2 lhs, T2 rhs, Work<Syntax> work) {
      assert lhs.is_obj() && rhs.is_obj() && !rhs.is_open() && is_resolving();

      // Not yet resolved.  See if there is exactly 1 choice.
      String lab = null;
      for( String id : rhs._args.keySet() ) {
        if( is_resolving(id) ) continue;
        if( pat.trial_unify_ok(rhs.arg(id),false) ) {
          if( lab==null ) lab=id;   // No choices yet, so take this one
          else {                    // Ambiguous (yet)
            pat.push_update(this);  // Revisit if changes
            pat.merge_deps(rhs,work);
            // Either cannot resolve (yet), or too late and will never resolve
            return false;
          }
        }
      }
      if( lab==null ) return false; // No match, so error and never resolves
      // Field can be resolved
      if( work==null ) return true; // Singleton match
      boolean old = lhs._args.remove(_id)!=null;   // Remove old label
      T2 prior = lhs.arg(lab);      // Get prior matching lhs label, if any
      if( prior==null ) {
        if( !old ) throw unimpl(); // No old unresolved label, no old resolved label
        lhs._args.put(lab,pat);
      } else prior.unify(pat,work); // Merge pattern and prior label in LHS
      _id=lab;                  // Change field label
      work.add(this);           // On worklist, GCP at least can update
      return true;              // Progress
    }
    
    @Override boolean more_work(Work<Syntax> work) {
      if( !more_work_impl(work) ) return false;
      return _ptr.more_work(work);
    }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      T rez = map.apply(this);
      return reduce.apply(rez, _ptr.visit(map,reduce));
    }
  }

  abstract static class PrimSyn extends Lambda {
    static T2  BOOL (){ return T2.make_base(TypeInt.BOOL); }
    static T2  INT64(){ return T2.make_base(TypeInt.INT64); }
    static T2  STRP (){ return T2.make_str (TypeMemPtr.STRPTR); }
    static T2  FLT64(){ return T2.make_base(TypeFlt.FLT64); }
    abstract String name();
    static final String[][] IDS = new String[][] {
      {},
      {"x"},
      {"x","y"},
      {"x","y","z"},
    };
    PrimSyn(String[] ids, T2 ...t2s) {
      super(null, ids);
      T2 fun = T2.make_fun(t2s);
      fun.arg(RET).push_update(this); // Return has a dep on Lambda to support spreading _is_copy      
      for( int i=0; i<_targs.length; i++ )
        _targs[i] = fun.arg(Lambda.ARGNAMES[i]).push_update(this);        
      _hmt = fun;
    }
    abstract PrimSyn make();
    @Override int prep_tree(Syntax par, VStack nongen, Work<Syntax> work) {
      prep_tree_impl(par,nongen,work, _hmt);
      return 1;
    }
    @Override boolean hm(Work<Syntax> work) {
      // For most primitives, they do math on the inputs.  Hence, if the input
      // is an error, so is the output.  Primitives like Pair and Triple carry
      // their inputs directly through, and thus can represent partial errors
      // in the result.  The If primitive can ignore some (error) inputs.
      boolean progress = false;
      for( int i=0; i<_targs.length; i++ ) {
        progress |= find().unify_errs(targ(i)._err,work);
        if( targ(i).is_err2() ) progress |= find().union(targ(i),work);
        if( work==null && progress ) return true;
      }
      return progress;
    }

    @Override void add_hm_work( @NotNull Work<Syntax> work) {
      work.add(_par);
    }
    @Override Type val(Work<Syntax> work) {
      assert _body==null;
      Type ret = apply(_types);
      return TypeFunPtr.makex(false,BitsFun.make0(_fidx),_args.length+DSP_IDX,Type.ANY,ret);
    }

    @Override boolean more_work(Work<Syntax> work) { return more_work_impl(work); }
    @Override SB str(SB sb){ return sb.p(name()); }

    @Override SB p1(SB sb, VBitSet dups) {
      if( _args.length==0 ) return sb.p(name());
      sb.p(name()).p("={ ").nl().i().p("  ");
      for( int i=0; i<_args.length; i++ ) {
        sb.p(_args[i]);
        if( DO_HM  ) _targs[i].str(sb.p(", HMT=" ),new VBitSet(),dups,true);
        if( DO_GCP ) sb.p(", GCP=").p(_types[i]);
        sb.nl().i().p("  ");
      }
      return sb.unchar(2).p("} ");
    }

    @Override SB p2(SB sb, VBitSet visit, VBitSet dups) { return sb; }
  }

  // Pair
  static class Pair extends PrimSyn implements Alloc {
    static final private String[] FLDS = new String[]{"0","1"};
    final int _alias;
    final Ary<Syntax> _rflds = new Ary<>(Syntax.class);
    @Override String name() { return "pair"; }
    static private T2 var1,var2;
    public Pair() {
      super(FLDS,
            var1=T2.make_leaf(),
            var2=T2.make_leaf(),
            T2.make_ptr(T2.make_open_struct(FLDS,new T2[]{var1,var2})));
      _alias = BitsAlias.new_alias(BitsAlias.INTX);
      ALIASES.setX(_alias,this);
    }
    @Override public T2 t2() { return find().get(RET); }
    @Override public int alias() { return _alias; }
    @Override public TypeMemPtr tmp() { return _tmp(_alias,FLDS,_types); }
    @Override public Type fld(String id, Syntax fld) {
      int idx = Util.find(FLDS,id);
      return idx==-1 ? null : _types[idx];
    }
    @Override public Ary<Syntax> rflds() { return _rflds; }
    @Override public Type meet() {
      Type t = TypeNil.XSCALAR;
      for( Type t2 : _types ) t = t.meet(t2);
      return t;
    }
    @Override public Type join() {
      Type t = TypeNil.SCALAR;
      for( Type t2 : _types ) t = t.join(t2);
      return t;
    }
    
    @Override PrimSyn make() { return new Pair(); }
    @Override boolean hm(Work<Syntax> work) { return false; }
    @Override Type apply(Type[] flows) { return TypeMemPtr.make(_alias,TypeStruct.ISUSED); }
  }

  // Triple
  static class Triple extends PrimSyn implements Alloc {
    static final private String[] FLDS = new String[]{"0","1","2"};
    final int _alias;
    final Ary<Syntax> _rflds = new Ary<>(Syntax.class);
    @Override String name() { return "triple"; }
    static private T2 var1,var2,var3;
    public Triple() {
      super(FLDS,
            var1=T2.make_leaf(),
            var2=T2.make_leaf(),
            var3=T2.make_leaf(),
            T2.make_ptr(T2.make_open_struct(FLDS,new T2[]{var1,var2,var3})));
      _alias = BitsAlias.new_alias(BitsAlias.INTX);
      ALIASES.setX(_alias,this);
    }
    @Override public T2 t2() { return find().get(RET); }
    @Override public int alias() { return _alias; }
    @Override public TypeMemPtr tmp() { return _tmp(_alias,FLDS,_types); }
    @Override public Type fld(String id, Syntax fld) {
      int idx = Util.find(FLDS,id);
      return idx==-1 ? null : _types[idx];
    }
    @Override public Ary<Syntax> rflds() { return _rflds; }
    @Override public Type meet() {
      Type t = TypeNil.XSCALAR;
      for( Type t2 : _types ) t = t.meet(t2);
      return t;
    }
    @Override public Type join() {
      Type t = TypeNil.SCALAR;
      for( Type t2 : _types ) t = t.join(t2);
      return t;
    }
    @Override PrimSyn make() { return new Triple(); }
    @Override boolean hm(Work<Syntax> work) { return false; }
    @Override Type apply(Type[] flows) { return TypeMemPtr.make(_alias,TypeStruct.ISUSED);  }
  }

  // Special form of a Lambda body for IF, which changes the H-M rules.
  // None-executing paths do not unify args.
  static class If extends PrimSyn {
    @Override String name() { return "if"; }
    public If() {
      super(IDS[3],T2.make_leaf(),T2.make_leaf(),T2.make_leaf(),T2.make_leaf());
    }
    @Override PrimSyn make() { return new If(); }
    @Override boolean hm(Work<Syntax> work) {
      T2 rez = find().arg(RET);
      // GCP helps HM: do not unify dead control paths
      if( DO_GCP ) {            // Doing GCP during HM
        Type pred = _types[0];
        if( pred instanceof TypeNil tn ) {
          if( tn._nil ) return !tn._sub && rez.unify(targ(2), work);
          if( tn._sub ) return rez.unify(targ(1),work);
        } else if( pred.above_center() ) return false;
      }
      // Unify both sides with the result.
      return
        rez       .unify(targ(1),work) |
        rez.find().unify(targ(2),work);
    }
    @Override Type apply( Type[] flows) {
      Type pred= flows[0];
      Type t1  = flows[1];
      Type t2  = flows[2];
      // Conditional Constant Propagation: only prop types from executable sides
      if( !(pred instanceof TypeNil tn) ) return pred.oob(TypeNil.SCALAR);
      if( tn._nil ) return tn._sub ? TypeNil.XSCALAR : t2; // OR, YES
      else          return tn._sub ? t1              : t1.meet(t2); // NO, AND
    }
  }

  // EQ
  static class EQ extends PrimSyn {
    @Override String name() { return "eq"; }
    static private T2 var1;
    public EQ() {
      super(IDS[2],var1=T2.make_leaf(),var1,BOOL());
      _hmt.arg(RET).clr_cp();
    }
    @Override PrimSyn make() { return new EQ(); }
    @Override Type apply( Type[] flows) {
      Type x0 = flows[0];
      Type x1 = flows[1];
      if( x0.above_center() || x1.above_center() ) return TypeInt.BOOL.dual();
      if( x0.is_con() && x1.is_con() && x0==x1 )
        return TypeInt.TRUE;
      // TODO: Can also know about nil/not-nil
      return TypeInt.BOOL;
    }
  }

  // EQ0
  static class EQ0 extends PrimSyn {
    @Override String name() { return "eq0"; }
    public EQ0() {
      super(IDS[1],INT64(),BOOL());
      _hmt.arg(RET).clr_cp();
    }
    @Override PrimSyn make() { return new EQ0(); }
    @Override Type apply( Type[] flows) {
      Type pred = flows[0];
      if( !(pred instanceof TypeNil tn) ) return pred.oob();
      if( tn._nil ) return tn._sub ? TypeInt.XSCALAR : TypeInt.TRUE; // OR, YES
      else          return tn._sub ? TypeNil.XNIL    : TypeInt.BOOL; // NO, AND
    }
  }

  static class IsEmpty extends PrimSyn {
    @Override String name() { return "isempty"; }
    public IsEmpty() {
      super(IDS[1],STRP(),BOOL());
      _hmt.arg(RET).clr_cp();
    }
    @Override PrimSyn make() { return new IsEmpty(); }
    @Override Type apply( Type[] flows) {
      Type pred = flows[0];
      if( pred.above_center() ) return TypeNil.XSCALAR;
      if( pred instanceof TypeMemPtr tmp && tmp.is_str() ) {
        Type chr = tmp._obj.at(0);
        return chr==TypeInt.ZERO ? TypeInt.TRUE : TypeNil.XNIL;
      }
      return TypeInt.BOOL;
    }
  }

  // Remove a nil from a struct after a guarding if-test
  static class NotNil extends PrimSyn {
    @Override String name() { return " notnil"; }
    public NotNil() { super(IDS[1],T2.make_leaf(),T2.make_leaf()); }
    @Override PrimSyn make() { throw unimpl(); /*return new NotNil(); */}
    @Override boolean hm(Work<Syntax> work) {
      T2 arg = targ(0);
      T2 fun = find(); assert fun.is_fun();
      T2 ret = fun.arg(RET);
      // If the arg is already nil-checked, can be a nilable of a nilable.
      if( arg==ret ) return false;
      // Already an expanded nilable
      if( arg.is_nil() && arg.arg("?") == ret ) return false;
      // Already an expanded nilable with base
      if( arg.is_base() && ret.is_base() ) {
        assert !arg.is_open() && !ret.is_open();
        assert arg._tflow == ret._tflow.meet(TypeNil.XNIL);
        return false;
      }
      // Already an expanded nilable with ptr
      if( arg.is_ptr() && ret.is_ptr() )
        return arg.arg("*").unify(ret.arg("*"),work);
      if( work==null ) return true;
      // If the arg is already nil-checked, can be a nilable of a nilable.
      if( arg.is_nil() && ret.is_nil() )
        return arg.unify(ret,work);
      // Unify with arg with a nilable version of the ret.
      return T2.make_nil(ret).find().unify(arg,work);
    }
    @Override Type apply( Type[] flows) {
      Type val = flows[0];
      if( val==TypeNil.NIL ) return TypeNil.XSCALAR; // Weird case of not-nil nil
      return val.join(TypeNil.NSCALR);
    }
  }

  // multiply
  static class IMul extends PrimSyn {
    @Override String name() { return "i*"; }
    public IMul() {
      super(IDS[2],INT64(),INT64(),INT64());
      _hmt.arg(RET).clr_cp();
    }
    @Override PrimSyn make() { return new IMul(); }
    @Override Type apply( Type[] flows) {
      Type t0 = flows[0];
      Type t1 = flows[1];
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
  static class FMul extends PrimSyn {
    @Override String name() { return "f*"; }
    public FMul() {
      super(IDS[2],FLT64(),FLT64(),FLT64());
      _hmt.arg(RET).clr_cp();
    }
    @Override PrimSyn make() { return new FMul(); }
    @Override Type apply( Type[] flows) {
      Type t0 = flows[0];
      Type t1 = flows[1];
      if( t0.above_center() || t1.above_center() )
        return TypeFlt.FLT64.dual();
      if( t0 instanceof TypeFlt && t1 instanceof TypeFlt ) {
        if( t0.is_con() && t0.getd()==0 ) return TypeNil.XNIL;
        if( t1.is_con() && t1.getd()==0 ) return TypeNil.XNIL;
        if( t0.is_con() && t1.is_con() )
          return TypeFlt.con(t0.getd()*t1.getd());
      }
      return TypeFlt.FLT64;
    }
  }
  static class I2F extends PrimSyn {
    @Override String name() { return "i2f"; }
    public I2F() {
      super(IDS[1],INT64(),FLT64());
      _hmt.arg(RET).clr_cp();
    }
    @Override PrimSyn make() { return new I2F(); }
    @Override Type apply( Type[] flows) {
      Type t0 = flows[0];
      if( t0.above_center() )
        return TypeFlt.FLT64.dual();
      if( t0 instanceof TypeInt ) {
        if( t0.is_con() && t0.getl()==0 ) return TypeNil.XNIL;
        if( t0.is_con() )
          return TypeFlt.con((double)t0.getl());
      }
      return TypeFlt.FLT64;
    }
  }

  // add integers
  static class Add extends PrimSyn {
    @Override String name() { return "+"; }
    public Add() {
      super(IDS[2],INT64(),INT64(),INT64());
      _hmt.arg(RET).clr_cp();
    }
    @Override PrimSyn make() { return new Add(); }
    @Override Type apply( Type[] flows) {
      Type t0 = flows[0];
      Type t1 = flows[1];
      if( t0.above_center() || t1.above_center() )
        return TypeInt.INT64.dual();
      if( t0 instanceof TypeInt && t1 instanceof TypeInt ) {
        if( t0.is_con() && t1.is_con() )
          return TypeInt.con(t0.getl()+t1.getl());
      }
      return TypeInt.INT64;
    }
  }

  // decrement
  static class Dec extends PrimSyn {
    @Override String name() { return "dec"; }
    public Dec() {
      super(IDS[1],INT64(),INT64());
      _hmt.arg(RET).clr_cp();
    }
    @Override PrimSyn make() { return new Dec(); }
    @Override Type apply( Type[] flows) {
      Type t0 = flows[0];
      if( t0.above_center() ) return TypeInt.INT64.dual();
      if( t0 instanceof TypeInt && t0.is_con() )
        return TypeInt.con(t0.getl()-1);
      return TypeInt.INT64;
    }
  }
  static class IRand extends PrimSyn {
    @Override String name() { return "rand"; }
    public IRand() {
      super(IDS[1],INT64(),INT64());
      _hmt.arg(RET).clr_cp();
    }
    @Override PrimSyn make() { return new IRand(); }
    @Override Type apply( Type[] flows) {  return TypeInt.INT64;  }
  }

  // int->str
  static class Str extends PrimSyn {
    @Override String name() { return "str"; }
    public Str() {
      super(IDS[1],INT64(),STRP());
      _hmt.arg(RET).clr_cp();
    }
    @Override PrimSyn make() { return new Str(); }
    @Override Type apply( Type[] flows) {
      Type i = flows[0];
      if( i.above_center() ) return TypeMemPtr.STRPTR.dual();
      if( i instanceof TypeInt && i.is_con() )
        return TypeMemPtr.make_str(String.valueOf(i.getl()).intern());
      return TypeMemPtr.STRPTR;
    }
  }


  // flt->(factor flt flt)
  static class Factor extends PrimSyn {
    @Override String name() { return "factor"; }
    public Factor() {
      super(IDS[1],FLT64(),FLT64());
      _hmt.arg(RET).clr_cp();
    }
    @Override PrimSyn make() { return new Factor(); }
    @Override Type apply( Type[] flows) {
      Type flt = flows[0];
      if( flt.above_center() ) return TypeFlt.FLT64.dual();
      return TypeFlt.FLT64;
    }
  }


  interface Alloc {
    // Return a is_ptr T2
    T2 t2();
    int alias();
    // Make a rich / deep pointer from this Alloc.
    // Used in sharpen() in result reporting.
    TypeMemPtr tmp();
    // Assemble a rich / deep pointer from parts
    default TypeMemPtr _tmp(int alias, String[] ids, Type[] ts) {
      TypeFld[] tfs = TypeFlds.make(TypeFld.NO_DISP); // Display
      for( int i=0; i<ts.length; i++ )                // Insert and alpha sort 
        tfs = TypeFlds.add(tfs,TypeFld.make(ids[i],ts[i]));
      return TypeMemPtr.make(alias,TypeStruct.make("", Type.ALL,TypeFlds.hash_cons(tfs)));
    }
    // Get a flow type from a field id
    Type fld(String id, Syntax foo);
    // Referring field labels
    Ary<Syntax> rflds();
    // Meet and join over all fields
    Type meet();
    Type join();

  }

  interface Func {
    // Return a is_fun T2
    T2 as_fun();
    // Number of args
    int nargs();
    // Type of an argument
    T2 targ(int argn);
    // Push Apply onto Applys list
    void apply_push(Apply apl, Work<Syntax> work);
  }

  // ---------------------------------------------------------------------
  // T2 types form a Lattice, with 'unify' same as 'meet'.  T2's form a DAG
  // (cycles if I allow recursive unification) with sharing.  Each Syntax has a
  // T2, and the forest of T2s can share.  Leaves of a T2 can be either a
  // simple concrete base type, or a sharable leaf.  Unify is structural, and
  // where not unifyable the union is replaced with an Error.
  static class T2 {
    private static int CNT=1;
    final int _uid=CNT++;

    // Structural parts to unify with, or null.
    // If Leaf   , then null and _tflow is null.
    // If Base   , then null and _tflow is set.
    // If unified, contains the single key ">>" and all other fields are null.
    // If Nil    , contains the single key "?"  and all other fields are null.
    // If Ptr    , contains the single key "*"  and all other fields are null.
    // If Lambda , contains keys " x"," y"," z" for args or " ret" for return.
    // If Struct , contains keys for the field labels.  No display & not-null.
    // If Overload,contains keys for ad-hoc polymorphic functions, all "&n"
    // If Error  , _eflow may contain a 2nd flow type; also blends keys from all takers
    NonBlockingHashMap<String,T2> _args;

    // Any/all of Base,Lambda,Struct may appear at once.
    // If more than one appears, then we have a "Cannot unify" error.
    // Nil is NOT allowed to appear with others, but it can fold into all of them.

    // Contains a Bases flow-type, or null if not a Base.
    Type _tflow;
    Type _eflow;                // Error flow; incompatible with _flow

    // Can be nil
    boolean _may_nil;

    // True for any primitive which might widen its result or
    // root args.  Otherwise, in cases like:
    //       "f0 = { f -> (if (rand) 1 (f (f0 f) 2))}; f0"
    // f's inputs and outputs gets bound to a '1': f = { 1 2 -> 1 }
    //
    // If _is_copy is true, then HMT bases are allowed to preserve their exact
    // constant values, so e.g. '(id "abc")' remains "abc" instead of 'str'.
    boolean _is_copy = true;

    // Contains the set of aliased Structs, or null if not a Struct.
    // If set, then keys for field names may appear.
    boolean _is_obj;
    // Structs allow more fields.  Not quite the same as TypeStruct._open field.
    boolean _open;

    // Null for no-error, or else a single-T2 error
    String _err = null;

    // Dependent (non-local) tvars to revisit
    Ary<Syntax> _deps;

    // The only Constructor
    private T2(NonBlockingHashMap<String,T2> args) { _args = args; }

    T2 copy() {
      // Shallow clone of args
      T2 t = new T2(_args==null ? null : (NonBlockingHashMap<String,T2>)_args.clone());
      t._tflow = _tflow;
      t._eflow = _eflow;
      t._may_nil = _may_nil;
      t._is_obj = _is_obj;
      t._open = _open;
      t._is_copy = _is_copy;
      t._err = _err;
      t._deps = _deps==null ? null : _deps.deepCopy();
      return t;
    }

    boolean is_leaf() { return _args==null && _tflow ==null && !_is_obj; }
    boolean unified() { return get(">>")!=null; }
    boolean is_nil () { return get("?" )!=null; }
    boolean is_ptr () { return get("*" )!=null; }
    boolean is_base() { return _tflow != null; }
    boolean is_fun () { return get(RET)!=null; }
    boolean is_obj () { return _is_obj; }
    boolean is_open() { return _open; }           // Struct-specific
    boolean is_err () { return _err!=null || is_err2(); }
    boolean is_err2() { return
        (is_base()      ? 1 : 0) +                 // Any 2 or more of base,ptr,fun,obj, or eflow
        (_eflow  !=null ? 1 : 0) +
        (is_ptr()       ? 1 : 0) +
        (is_fun()       ? 1 : 0) +
        (is_obj()       ? 1 : 0)
        >= 2;                   // Two or more unrelated types is an error
    }
    int size() { return _args==null ? 0 : _args.size(); }
    // A faster debug not-UF lookup
    private T2 get( String key) { return _args==null ? null : _args.get(key); }
    // U-F find on the args collection
    T2 arg( String key) {
      T2 u = get(key);
      if( u==null ) return null;
      T2 uu = u.find();
      if( u!=uu ) _args.put(key,uu);
      return uu;
    }

    // Constructor factories.
    static T2 make_leaf() { return new T2(null); }
    static T2 make_nil (T2 leaf) {
      T2 t2 = new T2(new NonBlockingHashMap<>(){{put("?",leaf);}});
      t2._may_nil = true;
      return t2;
    }
    static T2 make_base(Type flow) {
      assert !(flow instanceof TypeStruct) && !(flow instanceof TypeFunPtr) && !(flow instanceof TypeMemPtr) && !(flow instanceof TypeFld);
      T2 t2 = new T2(null);
      t2._tflow =flow;
      assert t2.is_base();
      return t2;
    }
    static T2 make_fun( T2... t2s ) {
      NonBlockingHashMap<String,T2> args = new NonBlockingHashMap<>();
      for( int i=0; i<t2s.length-1; i++ )
        args.put(Lambda.ARGNAMES[i], t2s[i]);
      T2 last = t2s[t2s.length-1];
      args.put(RET,last);
      T2 t2 = new T2(args);
      t2._may_nil = false;
      assert t2.is_fun();
      return t2;
    }
    // A struct with fields
    static T2 make_open_struct( String[] ids, T2[] flds ) {
      NonBlockingHashMap<String,T2> args = ids==null ? null : new NonBlockingHashMap<>();
      if( ids!=null )
        for( int i=0; i<ids.length; i++ )
          args.put(ids[i],flds[i]);
      T2 t2 = new T2(args);
      t2._is_obj = true;
      t2._may_nil = false;
      t2._open = false;
      assert t2.is_obj();
      return t2;
    }

    static T2 make_ptr(T2 obj) {
      NonBlockingHashMap<String,T2> args = new NonBlockingHashMap<>(){{put("*",obj);}};
      T2 t2 = new T2(args);
      assert t2.is_ptr();
      return t2;
    }
    static T2 make_str(TypeMemPtr flow) {
      assert flow.is_str();
      T2 t2str = make_open_struct(new String[]{"str:","0"},new T2[]{make_leaf(),make_base(flow._obj.get("0")._t)});
      return make_ptr(t2str);
    }

    void free() {
      if( _args!=null ) _args.clear();
      _tflow = _eflow = null;
      _is_obj = _may_nil =_open = false;
      _is_copy = true;
      _err  = null;
      _deps = null;
    }

    T2 debug_find() {// Find, without the roll-up
      if( !unified() ) return this; // Shortcut
      if( _args==null ) return this;
      T2 u = _args.get(">>");
      if( !u.unified() ) return u;  // Shortcut
      // U-F search, no fixup
      while( u.unified() ) u = u._args.get(">>");
      return u;
    }

    T2 find() {
      T2 u0 = _find0();
      T2 u1 = u0.is_nil () ? u0._find_nil () : u0;
      return u1;
    }
    // U-F find
    private T2 _find0() {
      T2 u = debug_find();
      if( u==this ) return u;
      if( u==_args.get(">>") ) return u;
      // UF fixup
      T2 v = this, v2;
      while( (v2=v._args.get(">>"))!=u ) { v._args.put(">>",u); v = v2; }
      return u;
    }
    // Nilable fixup.  nil-of-leaf is OK.  nil-of-anything-else folds into a
    // nilable version of the anything-else.
    private T2 _find_nil() {
      T2 n = arg("?");
      if( n.is_leaf() ) return this;
      _args.remove("?");  // No longer have the "?" key, not a nilable anymore
      if( n._is_copy ) _args.put("??",n);  // For hm_apply_lift, keep around the prior mapping
      // Nested nilable-and-not-leaf, need to fixup the nilable
      if( n.is_base() ) {
        _may_nil=false;
        _tflow = n._tflow.meet(TypeNil.XNIL);
        if( n._eflow!=null ) _eflow = n._eflow.meet(TypeNil.XNIL);
        if( !n._is_copy ) clr_cp();
      }
      if( n.is_ptr() ) {
        if( _args==null ) _args = new NonBlockingHashMap<>();
        _args.put("*",n.get("*"));
      }
      if( n.is_fun() ) {
        if( !n._is_copy ) clr_cp();
        throw unimpl();
      }
      if( n.is_obj() ) throw unimpl();
      if( n.is_nil() )          // Peel nested is_nil
        _args.put("?",n.arg("?"));
      n.merge_deps(this,null);
      return this;
    }
    
    private long dbl_uid(T2 t) { return dbl_uid(t._uid); }
    private long dbl_uid(long uid) { return ((long)_uid<<32)|uid; }

    // True if any portion allows for nil
    boolean has_nil() {
      if( _tflow instanceof TypeNil tn && tn.must_nil() ) return true;
      if( _eflow instanceof TypeNil tn && tn.must_nil() ) return true;
      if( _may_nil                                      ) return true;
      return false;
    }
    // Add nil
    void add_nil() {
      if( _tflow!=null ) _tflow = _tflow.meet(TypeNil.XNIL);
      if( _eflow!=null ) _eflow = _eflow.meet(TypeNil.XNIL);
      _may_nil = true;
    }
    // Strip off nil
    T2 strip_nil() {
      if( _tflow!=null ) _tflow = _tflow.join(TypeNil.NSCALR);
      if( _eflow!=null ) _eflow = _eflow.join(TypeNil.NSCALR);
      _may_nil = false;
      return this;
    }

    // Varies as unification happens; not suitable for a HashMap/HashSet unless
    // unchanging (e.g. defensive clone)
    @Override public int hashCode() {
      int hash = 0;
      if( _tflow!=null ) hash+= _tflow._hash;
      if( _eflow!=null ) hash+= _eflow._hash;
      if( _may_nil) hash = (hash+13)*23;
      if( _is_obj ) hash = (hash+23)*29;
      if( _args!=null )
        for( String key : _args.keySet() )
          hash += key.hashCode();
      return hash;
    }
    // CANNOT override equals: require REFERENCE EQUALITY not CYCLE_EQUALS
    //@Override public boolean equals(Object o) {
    //  if( o instanceof T2 t2 ) return cycle_equals(t2);
    //  return false;
    //}
    int nargs() {
      assert is_fun();
      for( int i=Lambda.ARGNAMES.length-1; i>=0; i-- )
        if( arg(Lambda.ARGNAMES[i])!=null )
          return i+1;
      throw unimpl();
    }

    // -----------------
    // Worse-case arguments that the Root/Universe can call with.  Must be
    // compatible with HM type.  Called once shallow when HM_FREEZE is set.
    // Called once deep to make a final report
    static final NonBlockingHashMapLong<Type> ADUPS = new NonBlockingHashMapLong<>();
    Type as_flow(Syntax syn, boolean deep) {
      assert ADUPS.isEmpty();
      Type t = _as_flow(syn,deep);
      ADUPS.clear();
      return t;
    }
    Type _as_flow(Syntax syn, boolean deep) {
      assert !unified();
      if( is_err() ) return TypeNil.SCALAR;
      if( is_leaf() ) return TypeNil.SCALAR.oob(!HM_FREEZE);
      if( is_base() ) return _tflow;
      if( is_ptr() ) {
        if( !deep ) Root.EXT_DEPS.add(syn); // Result depends on escapes
        // all escaping aliases that are compatible
        BitsAlias aliases = Root.matching_escaped_aliases(this);
        TypeStruct tstr = deep ? (TypeStruct)arg("*")._as_flow(syn,deep) : TypeStruct.ISUSED;
        return TypeMemPtr.make(false,_may_nil,aliases,tstr);
      }
      if( is_nil() )
        return arg("?")._as_flow(syn,deep).meet(TypeNil.AND_XSCALAR);
      if( is_fun() ) {
        if( !deep ) Root.EXT_DEPS.add(syn); // Result depends on escapes
        // all escaping fidxs that are compatible
        BitsFun fidxs = Root.matching_escaped_fidxs(this);
        if( _may_nil ) fidxs = fidxs.set(0);
        Type tfun = ADUPS.get(_uid);
        if( tfun != null ) return tfun;  // TODO: Returning recursive flow-type functions
        ADUPS.put(_uid, TypeNil.XSCALAR);
        Type rez = arg(RET)._as_flow(syn,deep);
        return TypeFunPtr.makex(false,fidxs,size()-1+DSP_IDX,Type.ANY,rez);
      }
      if( is_obj() ) {
        TypeStruct tstr = (TypeStruct)ADUPS.get(_uid);
        if( tstr==null ) {
          // Returning a high version of struct
          Type.RECURSIVE_MEET++;
          tstr = TypeStruct.malloc("",is_open() ? Type.ANY : Type.ALL,TypeFlds.get(0));
          if( _args!=null ) {
            for( String fld : _args.keySet() )
              if( fld.endsWith(":") ) tstr._clz = fld; // Move a nomative tag into the clz field
              else tstr.add_fld(TypeFld.malloc(fld));
            ADUPS.put(_uid,tstr); // Stop cycles
            for( String id : _args.keySet() )
              if( !Util.eq(id,tstr._clz) )
                tstr.get(id).setX(arg(id)._as_flow(syn,deep)); // Recursive
          }
          // update root args of an open HM struct, needs a type-flow type
          // that allows fields to be added
          if( --Type.RECURSIVE_MEET == 0 )
            // Shrink / remove cycle dups.  Might make new (smaller)
            // TypeStructs, so keep RECURSIVE_MEET enabled.
            tstr = Cyclic.install(tstr);
        }
        return tstr;
      }

      throw unimpl();
    }

    // -----------------
    // U-F union; this becomes that; returns 'that'.
    // No change if only testing, and reports progress.
    boolean union(T2 that, Work<Syntax> work) {
      assert !unified() && !that.unified(); // Cannot union twice
      if( this==that ) return false;
      if( work==null ) return true; // Report progress without changing

      // Merge all the hard bits
      that._may_nil  |= _may_nil ;
      if( _is_obj ) {
        that._open = that._is_obj ? (that._open & _open) : _open;
        that._is_obj = true;
      }
      unify_base(that, work);
      if( _args!=null ) {
        if( that._args==null ) { that._args = _args; _args=null; }
        else that._args.putAll(_args);
      }
      that.unify_errs(_err,work);

      // Work all the deps
      that.add_deps_work(work);
      this.add_deps_work(work);      // Any progress, revisit deps
      // Hard union this into that, no more testing.
      return _union(that,work);
    }

    // Hard unify this into that, no testing for progress.
    private boolean _union( T2 that, Work<Syntax> work ) {
      assert !unified() && !that.unified(); // Cannot union twice
      // Work<Syntax>: put updates on the worklist for revisiting
      merge_deps(that,work);    // Merge update lists, for future unions
      // Kill extra information, to prevent accidentally using it
      _args = new NonBlockingHashMap<>() {{put(">>", that);}};
      _tflow = _eflow = null;
      _is_obj = _may_nil = _open = false;
      _is_copy = true;
      _err  = null;
      _deps = null;
      assert unified();
      return true;
    }

    // Propagate error from left to right (if work).
    // Remove dups.
    boolean unify_errs(String err, Work<Syntax> work) {
      assert !unified();
      if( err==null || err.equals(_err) ) return false;
      if( _err!=null ) return false; // TODO: Combine single errors, right now 1st one wins
      if( work==null ) return true;  // Would be progress
      _err = err;                    // Propagate errors
      add_deps_work(work);
      return true;
    }
    boolean unify_miss_fld(String id, Work<Syntax> work) { return unify_errs(miss_fld(id),work); }


    // Unify this._flow into that._flow.  Flow is limited to only one of
    // {int,flt,ptr} and a 2nd unrelated flow type is kept as an error in
    // that._eflow.  Basically a pick the max 2 of 4 values, and each value is
    // range 0-3.  Returns progress.
    boolean unify_base(T2 that, Work<Syntax> work) {
      boolean progress = false;
      if( that._is_copy && !_is_copy )  { // Progress if setting is_copy
        if( work==null ) return true;
        progress = true;
        that.clr_cp(work);
      }
      Type sf = _tflow, hf = that._tflow;     // Flow of self and that.
      Type se = _eflow, he = that._eflow;     // Error flow of self and that.
      Type of = that._tflow, oe = that._eflow; // Old versions, to check for progress
      if( sf==null && hf==null ) return progress;// Fast cutout
      int cmp =  _fpriority(sf) - _fpriority(hf);
      if( cmp == 0 ) { that._tflow = sf.meet(hf); sf = se; hf = he; } // Tied; meet; advance both
      if( cmp  > 0 ) { that._tflow = sf;          sf = se;          } // Pick winner, advance
      if( cmp  < 0 ) {                            hf = he;          } // Pick winner, advance
      if( !(sf==null && hf==null) ) {                                 // If there is an error flow
        int cmp2 =  _fpriority(sf) - _fpriority(hf); // In a triple-error, pick best two
        if( cmp2 == 0 ) that._eflow = sf.meet(hf);
        if( cmp2  > 0 ) that._eflow = sf;
        if( cmp2  < 0 ) that._eflow = hf;
      }
      if( !that._is_copy ) {    // Widen non-copy bases
        if( that._tflow!=null ) that._tflow = that._tflow.widen();
        if( that._eflow!=null ) that._eflow = that._eflow.widen();
      }
      progress |= of!=that._tflow || oe!=that._eflow; // Progress check
      if( work==null && progress ) { that._tflow =of; that._eflow=oe; } // Unwind if just testing
      return progress;
    }
    // Sort flow types; int >> flt >> ptr >> null
    private static int _fpriority( Type t0 ) {
      if( t0 instanceof TypeInt ) return 3;
      if( t0 instanceof TypeFlt ) return 2;
      if( t0 instanceof TypeMemPtr ) return 1;
      assert t0==null;
      return 0;
    }


    // U-F union; that is nilable and this becomes that.
    // No change if only testing, and reports progress.
    boolean unify_nil(T2 that, Work<Syntax> work) {
      assert !is_nil() && that.is_nil();
      if( work==null ) return true; // Will make progress;
      T2 leaf = that.arg("?");  assert leaf.is_leaf();
      leaf.add_deps_work(work);
      T2 copy = copy().strip_nil();
      return leaf.union(copy,work) | _union(that,work);
    }
    // U-F union; that is nilable and a fresh copy of this becomes that.  No
    // change if only testing, and reports progress.  Handle cycles in the
    // fresh side.
    boolean unify_nil(T2 that, Work<Syntax> work, VStack nongen) {
      assert !is_nil() && that.is_nil();
      if( work==null ) return true; // Will make progress;
      T2 leaf = that.arg("?");  assert leaf.is_leaf();
      // A shallow copy and fresh-unify fails if 'this' is cyclic, because the
      // shallow copy peels one part of the loop.
      T2 copy = _fresh(nongen).strip_nil();
      copy._unify(leaf,work);
      return vput(that,true);
    }

    // -----------------
    // Structural unification.
    // Returns false if no-change, true for change.
    // If work is null, does not actually change anything, just reports progress.
    // If work and change, unifies 'this' into 'that' (changing both), and
    // updates the worklist.
    static private final HashMap<Long,T2> DUPS = new HashMap<>();
    boolean unify( T2 that, Work<Syntax> work ) {
      if( this==that ) return false;
      assert DUPS.isEmpty();
      boolean progress = _unify(that,work);
      DUPS.clear();
      return progress;
    }

    // Structural unification, 'this' into 'that'.  No change if just testing
    // (work is null) and returns a progress flag.  If updating, both 'this'
    // and 'that' are the same afterwards.
    private boolean _unify(T2 that, Work<Syntax> work) {
      assert !unified() && !that.unified();
      if( this==that ) return false;

      // Any leaf immediately unifies with any non-leaf
      if( this.is_leaf() && that.is_leaf() && _uid<that._uid )
        return that.union(this,work); // Two leafs sort by _uid
      if( this.is_leaf() ) return this.union(that,work);
      if( that.is_leaf() ) return that.union(this,work);

      // Two bases unify by smaller uid
      if( is_base() && that.is_base() )
        return _uid<that._uid ? that.union(this,work) : this.union(that,work);

      // Special case for nilable union something
      if( this.is_nil() && !that.is_nil() ) return that.unify_nil(this,work);
      if( that.is_nil() && !this.is_nil() ) return this.unify_nil(that,work);

      // Two unrelated overloads not allowed.  To equal overloads unify normally.
      boolean progress=false;

      // Cycle check
      long luid = dbl_uid(that);    // long-unique-id formed from this and that
      T2 rez = DUPS.get(luid);
      assert rez==null || rez==that;
      if( rez!=null ) return progress; // Been there, done that
      DUPS.put(luid,that);          // Close cycles

      if( work==null ) return true; // Here we definitely make progress; bail out early if just testing

      // Structural recursion unification.
      if( (is_obj() && that.is_obj()) ||
          (is_fun() && that.is_fun()) ||
          (is_nil() && that.is_nil()) ||
          (is_ptr() && that.is_ptr()) )
        unify_flds(this,that,work);
      // Union the top-level part
      return find().union(that.find(),work);
    }

    // Structural recursion unification.  Always progress.
    static void unify_flds( T2 thsi, T2 that, Work<Syntax> work ) {
      if( thsi._args==that._args ) return;  // Already equal (and probably both nil)
      if( Field.trial_resolve_all(thsi,null) ) thsi=thsi.find();
      assert !Field.trial_resolve_all(that,null); // TODO: need a test case
      
      for( String key : thsi._args.keySet() ) {
        T2 fthis = thsi.arg(key); // Field of this
        T2 fthat = that.arg(key); // Field of that
        if( fthat==null ) {       // Missing field in that
          if( Field.is_resolving(key) ) continue; // Do not add or remove until resolved
          if( that.is_open() ) that.add_fld(key,fthis,work); // Add to RHS
          else                 thsi.del_fld(key, work); // Remove from LHS
        } else fthis._unify(fthat, work);
        // Progress may require another find()
        thsi=thsi.find();
        that=that.find();
      }
      // Fields on the RHS are aligned with the LHS also
      if( that._args!=null )
        for( String key : that._args.keySet() ) {
          if( thsi.arg(key)==null ) { // Missing field in this
            if( Field.is_resolving(key) ) continue; // Do not add or remove until resolved
            if( thsi.is_open() )  thsi.add_fld(key,that.arg(key),work); // Add to LHS
            else                  that.del_fld(key, work);              // Drop from RHS
          }
        }
      assert !that.unified(); // Missing a find
    }

    // Insert a new field
    private boolean add_fld(String id, T2 fld, Work<Syntax> work) {
      if( _args==null ) _args = new NonBlockingHashMap<>();
      fld.push_update(_deps);
      _args.put(id,fld);
      add_deps_work(work);
      return true;
    }
    // Delete a field
    private boolean del_fld( String id, Work<Syntax> work) {
      if( Util.eq("*",id) || // Do not break ptr-ness, instead keep field and will be an error
          Util.eq("ret",id) ||  // Do not break function-ness
          id.charAt(0)==' ' )   // Also leave function args
        return false;
      add_deps_work(work);
      _args.remove(id);
      if( _args.size()==0 ) _args=null;
      return true;
    }

    // -----------------
    // Make a (lazy) fresh copy of 'this' and unify it with 'that'.  This is
    // the same as calling 'fresh' then 'unify', without the clone of 'this'.
    // Returns progress.
    // If work is null, we are testing only and make no changes.
    static private final IdentityHashMap<T2,T2> VARS = new IdentityHashMap<>();
    // Outer version, wraps a VARS check around other work
    boolean fresh_unify(T2 that, VStack nongen, Work<Syntax> work) {
      assert VARS.isEmpty() && DUPS.isEmpty();
      int old = CNT;
      boolean progress = _fresh_unify(that,nongen,work);
      VARS.clear();  DUPS.clear();
      if( work==null && old!=CNT )
        throw unimpl("busted, made T2s but just testing");
      return progress;
    }

    // Inner version, self-recursive and uses VARS and DUPS for cycles.
    private boolean _fresh_unify(T2 that, VStack nongen, Work<Syntax> work) {
      assert !unified() && !that.unified();

      // Check for cycles
      T2 prior = VARS.get(this);
      if( prior!=null )                        // Been there, done that
        return prior.find()._unify(that,work); // Also, 'prior' needs unification with 'that'
      // Check for equals
      if( cycle_equals(that) ) return vput(that,false);

      // Famous 'occurs-check': In the non-generative set, so do a hard unify,
      // not a fresh-unify.
      if( nongen_in(nongen) ) return vput(that,_unify(that,work));

      // LHS leaf, RHS is unchanged but goes in the VARS
      if( this.is_leaf() ) return vput(that,false);
      if( that.is_leaf() )  // RHS is a tvar; union with a deep copy of LHS
        return work==null || vput(that,that.union(_fresh(nongen),work));

      // Special handling for nilable
      if( this.is_nil() && !that.is_nil() )
        return vput(that,that.unify_nil_this(work));
      // That is nilable and this is not
      if( that.is_nil() && !this.is_nil() )
        return unify_nil(that,work,nongen);

      // Two unrelated overloads not allowed.  To equal overloads unify normally.
      boolean progress = false;

      // Progress on the parts
      if( _tflow !=null ) progress = unify_base(that, work);

      // Check for mismatched LHS and RHS
      if( work==null ) {
        if( _may_nil && !that._may_nil ) return true;
        if( is_ptr() && !that.is_ptr() ) return true;
        if( is_fun() && !that.is_fun() ) return true;
        if( is_obj() && !that.is_obj() ) return true;
        if( _err!=null && !Util.eq(_err,that._err) ) return true;
      } else {
        if( _may_nil && !that._may_nil ) { progress = that._may_nil = true; }
        if( is_ptr() && !that.is_ptr() ) // Error, fresh_unify a ptr into a non-ptr non-leaf
          { return that._unify(_fresh(nongen),work); }
        if( is_fun() && !that.is_fun() ) // Error, fresh_unify a fun into a non-fun non-leaf
          { return that._unify(_fresh(nongen),work); }
        if( is_obj() && !that.is_obj() ) // Error, fresh_unify a struct into a non-struct non-leaf
          { that._is_obj=true; return that._unify(_fresh(nongen),work); }
        if( _err!=null && !Util.eq(_err,that._err) ) {
          if( that._err!=null ) throw unimpl(); // TODO: Combine single error messages
          else { // Error, fresh_unify an error into a non-leaf non-error
            progress = true;
            that._err = _err;
          }
        }
      }

      vput(that,progress);      // Early set, to stop cycles
      // Both same (probably both nil)
      if( _args==that._args ) return progress;

      // Structural recursion unification, lazy on LHS
      return fresh_unify_flds(this,that,nongen,work,progress);
    }
    private boolean vput(T2 that, boolean progress) { VARS.put(this,that); return progress; }

    private static boolean fresh_unify_flds(T2 thsi, T2 that, VStack nongen, Work<Syntax> work, boolean progress) {
      assert !thsi.unified() && !that.unified();
      // Attempt resolve and unresolved fields
      while( Field.trial_resolve_all(thsi,work) || Field.trial_resolve_all(that,work) ) {
        progress=true;
        thsi = thsi.find();
        that = that.find();
      }
      
      boolean missing = thsi.size()!= that.size();
      if( thsi._args != null )
        for( String key : thsi._args.keySet() ) {
          T2 lhs = thsi.arg(key);
          T2 rhs = that.arg(key);
          // Attempt a fresh cross-T2 resolve
          if( rhs==null && Field.is_resolving(key) ) {
            if( that.is_open() ) continue;  // Open RHS allows more fields which might add choices
            Field fld = Field.FIELDS.get(key);
            if( !fld.trial_resolve(lhs,thsi,that,work) ) continue;
            if( work==null ) return true;
            progress = true;
            // Updated LHS args and RHS key
            key=fld._id;
            lhs = thsi.arg(key);
            rhs = that.arg(key);
          }

          if( rhs==null ) {         // No RHS to unify against
            missing = true;         // Might be missing RHS
            thsi.merge_deps(that,work);
            if( thsi.is_open() || that.is_open() || lhs.is_err() || (thsi.is_fun() && that.is_fun()) ) {
              if( work==null ) return true; // Will definitely make progress
              T2 nrhs = lhs._fresh(nongen); // New RHS value
              if( !that.is_open() ) {
                nrhs._err = miss_fld(key); // TODO: merge errors
                thsi.add_deps_work(work);
              }
              progress |= that.add_fld(key,nrhs,work);
            } // Else neither side is open, field is not needed in RHS
          } else {
            progress |= lhs._fresh_unify(rhs,nongen,work);
          }
          thsi=thsi.find();
          that=that.find();
          if( progress && work==null ) return true;
        }
      // Fields in RHS and not the LHS are also merged; if the LHS is open we'd
      // just copy the missing fields into it, then unify the structs (shortcut:
      // just skip the copy).  If the LHS is closed, then the extra RHS fields
      // are removed.
      if( missing && thsi.is_obj() && !thsi.is_open() && that._args!=null )
        for( String key : that._args.keySet() ) { // For all fields in RHS
          if( Field.is_resolving(key) ) continue;
          if( thsi.arg(key)==null && !that.arg(key).is_err()) {   // Missing in LHS
            if( work == null ) return true;    // Will definitely make progress
            progress |= that.del_fld(key,work);
          }
        }
      // If LHS is closed, close RHS
      if( thsi.is_obj() && that._open && !thsi._open) { progress = true; that._open = false; }
      if( progress && work!=null ) that.add_deps_work(work);
      return progress;
    }

    private boolean unify_nil_this( Work<Syntax> work ) {
      if( work==null ) return unify_nil_this_test();
      boolean progress = false;
      Type tmt = meet_nil(_tflow); if( progress |= (tmt!=_tflow) ) _tflow = tmt;
      Type emt = meet_nil(_eflow); if( progress |= (emt!=_eflow) ) _eflow = emt;
      if( !_may_nil && !is_base() ) { progress = _may_nil = true; }
      if( progress ) add_deps_work(work);
      return progress;
    }
    private boolean unify_nil_this_test( ) {
      if( meet_nil(_tflow)!=_tflow ) return true;
      if( meet_nil(_eflow)!=_eflow ) return true;
      if( !_may_nil && !is_base() ) return true;
      return vput(this,false);
    }
    private static Type meet_nil(Type t) { return t==null ? null : t.meet(TypeNil.XNIL); }

    // Return a fresh copy of 'this'
    T2 fresh() {
      assert VARS.isEmpty();
      T2 rez = _fresh(null);
      VARS.clear();
      return rez;
    }
    private T2 _fresh(VStack nongen) {
      assert !unified();
      T2 rez = VARS.get(this);
      if( rez!=null ) return rez.find(); // Been there, done that
      // Unlike the original algorithm, to handle cycles here we stop making a
      // copy if it appears at this level in the nongen set.  Otherwise, we'd
      // clone it down to the leaves - and keep all the nongen leaves.
      // Stopping here preserves the cyclic structure instead of unrolling it.
      if( nongen_in(nongen) ) {
        VARS.put(this,this);
        return this;
      }

      // Structure is deep-replicated
      T2 t = copy();
      VARS.put(this,t);         // Stop cyclic structure looping
      if( _args!=null )
        for( String key : _args.keySet() )
          t._args.put(key, arg(key)._fresh(nongen));
      assert !t.unified();
      return t;
    }

    // Do a trial unification between this and that.  Report back if any error
    // happens.  No change to either side, this is a trial only.
    private static final NonBlockingHashMapLong<T2> TDUPS = new NonBlockingHashMapLong<>();
    private boolean trial_unify_ok(T2 that, boolean extras) {
      TDUPS.clear();
      return _trial_unify_ok(that, extras);
    }
    private boolean _trial_unify_ok(T2 that, boolean extras) {
      assert !unified() && !that.unified();
      long duid = dbl_uid(that._uid);
      if( TDUPS.putIfAbsent(duid,this)!=null )
        return true;                    // Visit only once, and assume will resolve
      if( this==that )     return true; // No error
      if( this.is_leaf() ) return true; // No error
      if( that.is_leaf() ) return true; // No error
      if( this.is_base() && that.is_base() ) // Bases must match
        return _tflow.getClass()==that._tflow.getClass();

      // Same basic tvar class checks children
      if( is_fun() != that.is_fun() ||
          is_ptr() != that.is_ptr() ||
          is_obj() != that.is_obj() ||
          is_nil() != that.is_nil() ||
          is_base()!= that.is_base() )
        return false;            // Unrelated tvar class is a fail

      // Check children
      if( _args!=null )
        for( String id : _args.keySet() ) {
          if( Util.eq(id,RET) ) continue; // Do not unify based on return types
          T2 lhs = this.arg(id);
          T2 rhs = that.arg(id);
          if( rhs!=null && !lhs._trial_unify_ok(rhs,extras) ) return false;
          if( id.endsWith(":") && (lhs==null || rhs==null) ) return false; // Class tags are not 'extra fields', must match exactly
        }

      // Allow unification with extra fields.  The normal unification path
      // will not declare an error, it will just remove the extra fields.
      return  (extras || this.mismatched_child(that)) && (that.mismatched_child(this));
    }

    // True if 'this' has extra children and 'that' does not allow extras
    private boolean mismatched_child( T2 that ) {
      if( !that.is_open() && _args!=null )   // If RHS is closed
        for( String id : _args.keySet() )
          if( that.arg(id)==null ) // And missing key in RHS
            return false;          // Trial unification failed
      return true;
    }

    // -----------------
    private static final VBitSet ODUPS = new VBitSet();

    boolean nongen_in(VStack vs) {
      if( vs==null ) return false;
      ODUPS.clear();
      for( T2 t2 : vs )
        if( _occurs_in_type(t2) )
          return true;
      return false;
    }

    boolean _occurs_in_type(T2 x) {
      assert !unified() && !x.unified();
      if( x==this ) return true;
      if( ODUPS.tset(x._uid) ) return false; // Been there, done that
      if( x._args!=null )
        for( String key : x._args.keySet() )
          if( _occurs_in_type(x.arg(key)) )
            return true;
      return false;
    }

    // -----------------
    // Test for structural equivalence, including cycles
    static private final NonBlockingHashMapLong<T2> CDUPS = new NonBlockingHashMapLong<>();
    boolean cycle_equals(T2 t) {
      assert CDUPS.isEmpty();
      boolean rez = _cycle_equals(t);
      CDUPS.clear();
      return rez;
    }
    boolean _cycle_equals(T2 t) {
      assert !unified() && !t.unified();
      if( this==t ) return true;
      if( _tflow   !=t._tflow   ) return false; // Base-cases have to be completely identical
      if( _eflow   !=t._eflow   ) return false;
      if( _may_nil !=t._may_nil ) return false; // Base-cases have to be completely identical
      if( _is_obj  !=t._is_obj  ) return false; // Base-cases have to be completely identical
      if( _is_copy != t._is_copy) return false; // Base-cases have to be completely identical
      if( _err!=null && !_err.equals(t._err) ) return false; // Base-cases have to be completely identical
      if( is_leaf() ) return false;               // Two leaves must be the same leaf, already checked for above
      if( size() != t.size() ) return false;      // Mismatched sizes
      if( _args==t._args ) return true;           // Same arrays (generally both null)
      // Cycles stall the equal/unequal decision until we see a difference.
      T2 tc = CDUPS.get(_uid);
      if( tc!=null )  return tc==t; // Cycle check; true if both cycling the same
      CDUPS.put(_uid,t);
      for( String key : _args.keySet() ) {
        T2 arg = t.arg(key);
        if( arg==null || !arg(key)._cycle_equals(arg) )
          return false;
      }
      return true;
    }

    // -----------------
    // T2MAP allows cycle_equals, not identity equals
    static private final IdentityHashMap<T2,Type> T2MAP = new IdentityHashMap<>();
    static private final Ary<T2> T2_MAY_NEW_LEAF = new Ary<T2>(T2.class);
    static final NonBlockingHashMapLong<Type> WDUPS = new NonBlockingHashMapLong<>();

    // Lift the flow of an Apply, according to its inputs.  This is to
    // help preserve flow precision across polymorphic calls, where the input
    // flow types all meet - but HM understands how the T2s split back apart
    // after the Apply.  During this work, every T2 is mapped one-to-one to a
    // flow Type, and the mapping is made recursively.

    // Walk a T2 and a matching flow-type, and build a map from T2 to flow-types.
    // Stop if either side loses corresponding structure.  This operation must be
    // monotonic because the result is JOINd with GCP types.
    void walk_types_in( Type t ) {
      assert !unified();
      if( is_err() ) return;
      if( _is_copy && !is_obj() ) {
        long duid = dbl_uid(t._uid);
        if( WDUPS.putIfAbsent(duid,TypeStruct.ISUSED)!=null ) return;
        T2MAP.merge(this, t, Type::meet);
      }

      // Free variables keep the input flow type.
      if( is_leaf() ) T2_MAY_NEW_LEAF.add(this);   // Might expand to a new leaf later

      // Pointers recurse on their object
      if( is_ptr() ) {
        arg("*").walk_types_in(t instanceof TypeMemPtr tmp ? tmp._obj : t);
        T2 nptr = arg("??");
        if( nptr != null ) // Also map the not-nilable version
          T2MAP.merge(nptr,t.join(TypeNil.NSCALR),Type::meet);
      }

      // Nilable, recurse on the not-nil
      if( is_nil() && !t.isa(TypeNil.XNIL) ) {
        Type tn = t.join(TypeNil.NSCALR);
        arg("?").walk_types_in(tn);
        T2 nptr = arg("??");
        if( nptr != null ) // Also map the not-nilable version
          T2MAP.merge(nptr,tn,Type::meet);
      }

      // Walk return not arguments
      if( is_fun() )
        arg(RET).walk_types_in(t instanceof TypeFunPtr tfp ? tfp._ret : t.oob(TypeNil.SCALAR));
      // Objects walk all fields
      if( is_obj() && _args != null ) {
        for( String id : _args.keySet() )
          if( !id.endsWith(":") ) // No lifting from class args
            arg(id).walk_types_in(at_fld(t, id));
        if( is_open() ) T2_MAY_NEW_LEAF.add(this); // Can add a new leaf later
      }
    }

    private static Type at_fld(Type t, String id) { // TODO: FAILURE TO SHARPEN
      if( !(t instanceof TypeStruct ts) || ts.is_str() ) return t.oob(TypeNil.SCALAR);
      TypeFld fld = ts.get(id);
      return fld==null ? ts.oob(TypeNil.SCALAR) : fld._t;
    }

    // Walk an Apply output flow type, and attempt to replace parts of it with
    // stronger flow types from the matching input types.
    Type walk_types_out( Type t, Apply apply, boolean test ) {
      assert !unified();
      // Fast-path cutout
      if( t==TypeNil.XSCALAR ) return TypeNil.XSCALAR; // No lift, do not bother
      if( this.is_err() )      return t; // Do not lift errors

      // Check for some future leaf appearing with XSCALAR in the T2MAP.  Means
      // we saw an input leaf, which might later expand into new leafs (since
      // no HM_FREEZE) and new leafs can lift (since !HM_NEW_LEAF).
      if( !HM_NEW_LEAF && !T2.T2_MAY_NEW_LEAF.isEmpty()) {
        for( T2 t2 : T2.T2_MAY_NEW_LEAF )
          t2.push_update(apply);
        Root.NEW_LEAF_DEPS.add(apply);
        return TypeNil.XSCALAR;  // Future arg leaf can expand into anything, and lift result
      }
    
      // Check for a direct hit
      Type tmap = T2MAP.get(this);
      if( tmap!=null ) {
        assert _is_copy;
        push_update(apply);   // If is_copy falls, then widen applies and needs a revisit
        return tmap;          // While a copy, can return the direct hit
      }

      // Until we freeze, check for "may unify in the future".  For all successful      
      // trials, join all results since we might unify with any of them.
      if( !HM_FREEZE && _is_copy ) {
        // Join against everything in the arg input map that might unify
        Type tj = Type.ALL;
        for( T2 t2 : T2.T2MAP.keySet() ) {
          // Test unification.  Specifically allow extra fields, and these can
          // be removed over time, which will later allow a unification.
          // E.g. unify @{ a=V123; nope=V456 } and @{ a=V789 } would otherwise
          // fail because 'nope' is not in RHS and RHS is not open.  But 'nope'
          // might later be removed (e.g. by normal unifying these two types)
          // so allow for it now.          
          if( t2.trial_unify_ok(this,true) )
            tj = tj.join(T2.T2MAP.get(t2));
          t2.push_update(apply); // If t2 loses is_copy, need to recheck here
        }
        if( tj != Type.ALL ) // Some trial succeeds, use this result "as if" we got a direct hit
          return tj.join(t); // Return join, so the old_lift keeps lifting
        // No trial succeeds, fall into the recursive walk to lift internal parts
      }

      
      if( is_leaf() )
        return t;

      // Recursive breakdown
      if( is_base() ) return _tflow;

      if( is_ptr() ) {
        if( t==TypeNil.NIL || t==TypeNil.XNIL ) return t; // Keep a nil
        if( !(t instanceof TypeMemPtr tmp) )
          return t==TypeNil.XNSCALR ? t : t.oob(as_flow(null,true));
        TypeStruct obj = (TypeStruct)arg("*").walk_types_out(tmp._obj,apply,test);
        if( tmp._aliases.is_empty() )
          return tmp.make_from(obj);
        return TypeMemPtr.make(_may_nil&&tmp.must_nil(),tmp._aliases,obj);
      }
      if( is_obj() ) return t; // expect ptrs to be simple, so t is ISUSED

      if( is_nil() ) // The wrapped leaf gets lifted, then nil is added
        return arg("?").walk_types_out(t.join(TypeNil.NSCALR),apply, test);

      if( is_fun() ) {          // Walk returns not arguments
        Type tret = t instanceof TypeFunPtr tfp ? tfp._ret  : t.oob(TypeNil.SCALAR);
        if( WDUPS.get(_uid)!=null ) return t;
        WDUPS.put(_uid,t);
        Type trlift = arg(RET).walk_types_out(tret, apply, test);
        WDUPS.remove(_uid);
        return t instanceof TypeFunPtr tfp
          ? tfp.make_from(Type.ANY,trlift)
          : TypeFunPtr.makex(t.above_center(),(t.above_center() ? BitsFun.EMPTY : BitsFun.NALL),size()-1+DSP_IDX, Type.ANY, trlift);
      }

      throw unimpl();
    }

    // -----------------
    // Recursively clear _is_copy, through cyclic types
    static final VBitSet UPDATE_VISIT  = new VBitSet();
    void clr_cp(                 ) { UPDATE_VISIT.clear(); _clr_cp(null);}
    void clr_cp(Work<Syntax> work) { UPDATE_VISIT.clear(); _clr_cp(work);}
    private void _clr_cp( Work<Syntax> work  ) {
      if( !_is_copy || UPDATE_VISIT.tset(_uid) ) return;
      _is_copy = false;
      if( _tflow!=null ) _tflow = _tflow.widen();
      if( _eflow!=null ) _eflow = _eflow.widen();
      if( _deps!=null ) {
        T2 ret;
        for( Syntax syn : _deps ) {
          if( syn instanceof Apply apply && work!=null ) work.add(apply); // Apply-lift widens
          if( syn instanceof Lambda lam && lam.find().arg(RET)==this )
            for( Apply apply : lam._applys )
              if( (ret=apply._fun.find().arg(RET))!=null )
                ret._clr_cp(work);
        }
      }
      if( _args != null )
        for( T2 t2 : _args.values() )
          t2._clr_cp(work);
    }

    // -----------------
    // This is a T2 function that is the target of 'fresh', i.e., this function
    // might be fresh-unified with some other function.  Push the application
    // down the function parts; if any changes the fresh-application may make
    // progress.
    void push_update( Ary<Syntax> as ) { if( as != null ) for( Syntax a : as ) push_update(a); }
    T2 push_update( Syntax a) { UPDATE_VISIT.clear(); push_update_impl(a); return this; }
    private void push_update_impl(Syntax a) {
      assert !unified();
      if( UPDATE_VISIT.tset(_uid) ) return;
      if( _deps==null ) _deps = new Ary<>(Syntax.class);
      if( _deps.find(a)==-1 ) _deps.push(a);
      if( _args != null )
        for( T2 t2 : _args.values() )
          t2.debug_find().push_update_impl(a);
    }

    // Recursively add-deps to worklist
    void add_deps_work( Work<Syntax> work ) { UPDATE_VISIT.clear(); add_deps_work_impl(work); }
    private void add_deps_work_impl( Work<Syntax> work ) {
      work.addAll(_deps);
      if( _deps!=null )
        for( Syntax syn : _deps )
          if( syn._par instanceof Lambda lam )
            work.addAll(lam._applys);
      if( UPDATE_VISIT.tset(_uid) ) return;
      if( _args != null )
        for( T2 t2 : _args.values() )
          t2.add_deps_work_impl(work);
    }

    // Merge this._deps into that
    void merge_deps( T2 that, Work<Syntax> work ) {
      assert !that.unified();
      if( _deps != null ) {
        that.push_update(_deps);
        if( !that._is_copy && _is_copy && work!=null )
          for( Syntax dep : _deps )
            if( dep instanceof Lambda lam )
              work.addAll(lam._applys);
      }
    }


    // -----------------
    // Glorious Printing

    // Look for dups, in a tree or even a forest (which Syntax.p() does)
    public VBitSet get_dups() { return _get_dups(new VBitSet(),new VBitSet()); }
    public VBitSet _get_dups(VBitSet visit, VBitSet dups) {
      if( visit.tset(_uid) ) {
        dups.set(debug_find()._uid);
      } else {
        if( _args!=null )
          for( String key : _args.keySet() )
            if( !key.equals("??") )
              _args.get(key)._get_dups(visit,dups);
      }
      return dups;
    }

    @Override public String toString() { return str(new SB(), new VBitSet(), get_dups(), true ).toString(); }
    public String p() { VCNT=0; VNAMES.clear(); return str(new SB(), new VBitSet(), get_dups(), false ).toString(); }
    private static int VCNT;
    private static final NonBlockingHashMapLong<String> VNAMES = new NonBlockingHashMapLong<>();


    // Fancy print for Debuggers - includes explicit U-F re-direction.
    // Does NOT roll-up U-F, has no side-effects.
    SB str(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
      boolean dup = dups.get(_uid);
      if( !debug && unified() ) return find().str(sb,visit,dups,false);
      if( unified() || (is_leaf() && _err==null) ) {
        vname(sb,debug);
        return unified() ? _args.get(">>").str(sb.p(">>"), visit, dups, debug) : sb;
      }

      // Dup printing for all but bases (which are short, just repeat them)
      if( dup && (debug || !is_base() || is_err()) ) {
        vname(sb,debug);        // Leading V123
        if( visit.tset(_uid) ) return sb; // V123 and nothing else
        sb.p(':');              // V123:followed_by_type_descr
      }
      if( !_is_copy ) sb.p('%');

      // Special printing for errors
      if( is_err() ) {
        if( _err!=null ) sb.p(_err); // Error message, if any
        if( is_err2() ) {
          sb.p("[Cannot unify ");
          if( is_fun () ) str_fun(sb,visit,dups,debug).p(" and ");
          if( is_base() ) str_base(sb)                 .p(" and ");
          if( _eflow!=null) sb.p(_eflow)               .p(" and ");
          if( is_ptr () ) str_ptr(sb,visit,dups,debug, _tflow).p(" and ");
          if( is_obj () ) str_obj(sb,visit,dups,debug).p(" and ");
          return sb.unchar(5).p("]");
        }
        if( !is_leaf() ) sb.p(": "); // Separate error from self msg
      }

      if( is_base() ) return str_base(sb);
      if( is_ptr () ) return str_ptr(sb,visit,dups,debug, _tflow);
      if( is_fun () ) return str_fun(sb,visit,dups,debug);
      if( is_obj () ) return str_obj(sb,visit,dups,debug);
      if( is_nil () ) return str0(sb,visit,_args.get("?"),dups,debug).p('?');

      // Generic structural T2
      if( _err!=null ) return sb;
      sb.p("( ");
      if( _args!=null )
        for( String s : _args.keySet() )
          str0(sb.p(s).p(':'),visit,_args.get(s),dups,debug).p(" ");
      return sb.unchar().p(")");
    }
    static private SB str0(SB sb, VBitSet visit, T2 t, VBitSet dups, boolean debug) { return t==null ? sb.p("_") : t.str(sb,visit,dups,debug); }
    private SB str_base(SB sb) { return sb.p(_tflow); }
    private SB str_ptr(SB sb, VBitSet visit, VBitSet dups, boolean debug, Type flow) {
      T2 obj = _args==null ? null : _args.get("*");
      str0(sb.p('*'),visit,obj,dups,debug);
      if( _may_nil ) sb.p('?');
      return sb;
    }
    private SB str_fun(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
      sb.p("{ ");
      for( int i=0; i<Lambda.ARGNAMES.length; i++ ) {
        T2 arg = _args.get(Lambda.ARGNAMES[i]);
        if( arg!=null )
          str0(sb,visit,arg,dups,debug).p(' ');
      }
      return str0(sb.p("-> "),visit,_args.get(RET),dups,debug).p(" }").p(_may_nil ? "?" : "");
    }

    private SB str_obj(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
      if( is_prim() ) return sb.p("@{PRIMS}");
      String is_clz = null;
      if( _args!=null )
        for( String fld : _args.keySet() )
          if( fld.endsWith(":") ) // A nomative tag becomes the clazz
            sb.p(is_clz = fld);
      final boolean is_tup = is_tup(); // Distinguish tuple from struct during printing
      sb.p(is_tup ? "(" : "@{");
      boolean sep=false;
      if( _args==null ) sb.p(" ");
      else {
        for( String fld : sorted_flds() ) {
          // Skip fields from functions
          if( fld.charAt(0)==' ' ) continue; // Function arg names, happens if unifying fcns and structs
          if( Util.eq(fld,RET) ) continue;   // Function return   , happens if unifying fcns and structs
          if( Util.eq(fld,is_clz)) continue; // Clazz marker name, not currently used
          // Skip field names in a tuple
          str0(is_tup && !Field.is_resolving(fld) ? sb.p(' ') : sb.p(' ').p(fld).p(" = "),visit,get(fld),dups,debug).p(is_tup ? ',' : ';');
          sep=true;
        }
      }
      if( is_open() ) sb.p(" ...,");
      if( sep ) sb.unchar();
      sb.p(!is_tup ? "}" : ")");
      if( _may_nil ) sb.p("?");
      return sb;
    }

    // Pick a nice tvar name.  Generally: "A" or "B" or "V123" for leafs,
    // "X123" for unified but not collapsed tvars.
    private void vname( SB sb, boolean debug) {
      final boolean vuid = debug && (unified()||is_leaf());
      sb.p(VNAMES.computeIfAbsent((long) _uid,
                                  (k -> (vuid ? ((is_leaf() ? "V" : "X") + k) : ((++VCNT) - 1 + 'A' < 'V' ? ("" + (char) ('A' + VCNT - 1)) : ("V" + VCNT))))));
    }
    private boolean is_tup() { return _args==null || _args.isEmpty() || _args.containsKey("0"); }
    private Collection<String> sorted_flds() { return new TreeMap<>(_args).keySet(); }
    boolean is_prim() { return is_obj() && _args!=null && _args.containsKey("!"); }

    // Debugging tool
    T2 find(int uid) { return _find(uid,new VBitSet()); }
    private T2 _find(int uid, VBitSet visit) {
      if( visit.tset(_uid) ) return null;
      if( _uid==uid ) return this;
      if( _args==null ) return null;
      for( T2 arg : _args.values() )
        if( (arg=arg._find(uid,visit)) != null )
          return arg;
      return null;
    }
    static void reset() { CNT=0; DUPS.clear(); VARS.clear(); ODUPS.clear(); CDUPS.clear(); ADUPS.clear(); UPDATE_VISIT.clear(); }
  }
}
