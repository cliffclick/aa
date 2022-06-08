package com.cliffc.aa.HM;

import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;
import org.jetbrains.annotations.NotNull;

import java.util.*;

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

// Extend to records.

public class HM7 {
  static final HashMap<String,T2> PRIMS = new HashMap<>();
  static boolean DEBUG_LEAKS=false;

  public static T2 hm( String sprog ) {
    Worklist work = new Worklist();

    // Simple types
    T2 bool  = T2.make_base(TypeInt.BOOL);
    T2 int64 = T2.make_base(TypeInt.INT64);
    T2 flt64 = T2.make_base(TypeFlt.FLT64);
    T2 strp  = null; //T2.make_base(TypeMemPtr.STRPTR);

    // Primitives
    PRIMS.put("nil",T2.make_nil());

    T2 var1 = T2.make_leaf();
    T2 var2 = T2.make_leaf();
    T2 var3 = T2.make_leaf();

    PRIMS.put("pair1",T2.make_fun(var1, T2.make_fun(var2, T2.prim("pair",var1,var2) ))); // curried
    PRIMS.put("pair",T2.make_fun(var1, var2, T2.prim("pair",var1,var2) ));
    PRIMS.put("triple",T2.make_fun(var1, var2, var3, T2.prim("triple",var1,var2,var3) ));

    PRIMS.put("if",T2.make_fun(var2,var1,var1,var1));

    PRIMS.put("dec",T2.make_fun(int64,int64));
    PRIMS.put("*"  ,T2.make_fun(int64,int64,int64));
    PRIMS.put("?0",T2.make_fun(T2.make_leaf(),bool));
    PRIMS.put("isempty",T2.make_fun(strp,bool));

    // Print a string; int->str
    PRIMS.put("str",T2.make_fun(int64,strp));
    // Factor; FP div/mod-like operation
    PRIMS.put("factor",T2.make_fun(flt64,T2.prim("divmod",flt64,flt64)));

    // Parse
    Syntax prog = parse( sprog );

    // Prep for SSA: pre-gather all the (unique) ids
    int DEBUG_CNT=-1;
    int cnt_syns = prog.prep_tree(null,null,work);
    int init_T2s = T2.CNT;

    while( work.len()>0 ) {     // While work
      int oldcnt = T2.CNT;      // Used for cost-check when no-progress
      Syntax syn = work.pop();  // Get work
      T2 old = syn._t;          // Old value for progress assert
      if( work._cnt==DEBUG_CNT )
        System.out.println("break here");
      if( syn.hm(work) ) {      // Compute a new HM type and check for progress
        assert !syn.debug_find().unify(old.find(),null);// monotonic: unifying with the result is no-progress
        syn.add_kids(work);     // Push children on worklist
        syn.add_occurs(work);   // Push occurs-check ids on worklist
        if( syn._par !=null ) work.push(syn._par); // Parent updates
      } else {
        assert !DEBUG_LEAKS || oldcnt==T2.CNT;  // No-progress consumes no-new-T2s
      }
      // VERY EXPENSIVE ASSERT: O(n^2).  Every Syntax that makes progress is on the worklist
      //assert prog.more_work(work);
    }
    assert prog.more_work(work);

    //System.out.println("Initial T2s: "+init_T2s+", Prog size: "+cnt_syns+", worklist iters: "+work._cnt+", T2s: "+T2.CNT);
    return prog._t;
  }
  static void reset() { PRIMS.clear(); T2.reset(); }

  // ---------------------------------------------------------------------
  // Program text for parsing
  private static int X;
  private static byte[] BUF;
  @Override public String toString() { return new String(BUF,X,BUF.length-X); }
  static Syntax parse( String s ) {
    X = 0;
    BUF = s.getBytes();
    Syntax prog = term();
    if( skipWS() != -1 ) throw unimpl("Junk at end of program: "+new String(BUF,X,BUF.length-X));
    return prog;
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
      return new Apply(fun,require(')',ARGS.asAry()));
    }
    if( BUF[X]=='{' ) {         // Lambda of 1 or 2 args
      X++;                      // Skip paren
      Ary<String> args = new Ary<>(new String[1],0);
      while( skipWS()!='-' ) args.push(id());
      require("->");
      Syntax body = require('}',term());
      return new Lambda(body,args.asAry());
    }
    // Let or Id
    if( isAlpha0(BUF[X]) ) {
      String id = id();
      if( skipWS()!='=' )  return new Ident(id);
      // Let expression; "id = term(); term..."
      X++;                      // Skip '='
      Syntax def = require(';',term());
      return new Let(id,def,term());
    }

    // Structure
    if( BUF[X]=='@' ) {
      X++;
      require('{',null);
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
      return require('}',new Struct(ids.asAry(),flds.asAry()));
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
    int sum=0;
    while( X<BUF.length && isDigit(BUF[X]) )
      sum = sum*10+BUF[X++]-'0';
    if( X>= BUF.length || BUF[X]!='.' ) return new Con(TypeInt.con(sum));
    X++;
    float f = (float)sum;
    f = f + (BUF[X++]-'0')/10.0f;
    return new Con(TypeFlt.con(f));
  }
  private static Syntax string() {
    int start = ++X;
    while( X<BUF.length && BUF[X]!='"' ) X++;
    //return require('"', new Con(TypeStr.con(new String(BUF,start,X-start).intern())));
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
  private static <T> T require(char c, T t) { if( skipWS()!=c ) throw unimpl("Missing '"+c+"'"); X++; return t; }
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
    public void push(Syntax s) { if( !_work.contains(s) ) _work.add(_ary.push(s)); }
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
    Syntax _par;
    VStack _nongen;             //
    T2 _t;                      // Current HM type
    T2 find() {                 // U-F find
      T2 t = _t.find();
      return t==_t ? t : (_t=t);
    }
    T2 debug_find() { return _t.find(); } // Find, without the roll-up

    // Compute and set a new HM type.
    // If no change, return false.
    // If a change, return always true, however:
    // - If 'work' is null do not change/set anything.
    // - If 'work' is available, set a new HM in '_t' and update the worklist.
    abstract boolean hm(Worklist work);

    abstract int prep_tree(Syntax par, VStack nongen, Worklist work);
    final void prep_tree_impl( Syntax par, VStack nongen, Worklist work, T2 t ) { _par=par; _t=t; _nongen = nongen; work.push(this); }
    abstract void prep_lookup_deps(Ident id);

    abstract T2 lookup(String name); // Lookup name in scope & return type; TODO: pre-cache this.

    abstract void add_kids(Worklist work); // Add children to worklist
    void add_occurs(Worklist work){}

    // Giant Assert: True if OK; all Syntaxs off worklist do not make progress
    abstract boolean more_work(Worklist work);
    final boolean more_work_impl(Worklist work) {
      boolean no_more_work = work.has(this) || !hm(null); // Either on worklist, or no-progress
      return no_more_work;
    }
    // Print for debugger
    @Override final public String toString() { return str(new SB()).toString(); }
    abstract SB str(SB sb);
    // Line-by-line print with more detail
    public String p() { return p0(new SB(), new VBitSet()).toString(); }
    final SB p0(SB sb, VBitSet dups) {
      _t.get_dups(dups);
      _t.str(p1(sb.i()).p(" "), new VBitSet(),dups).nl();
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
    @Override T2 lookup(String name) { throw unimpl("should not reach here"); }
    @Override void add_kids(Worklist work) { }
    @Override int prep_tree( Syntax par, VStack nongen, Worklist work ) { prep_tree_impl(par, nongen, work, _con==TypeNil.NIL ? T2.make_nil() : T2.make_base(_con)); return 1; }
    @Override void prep_lookup_deps(Ident id) { throw unimpl("should not reach here"); }
    @Override boolean more_work(Worklist work) { return more_work_impl(work); }
  }

  static class Ident extends Syntax {
    final String _name;
    Ident(String name) { _name=name; }
    @Override SB str(SB sb) { return p1(sb); }
    @Override SB p1(SB sb) { return sb.p(_name); }
    @Override SB p2(SB sb, VBitSet dups) { return sb; }
    @Override boolean hm(Worklist work) {
      // A boolean if name is from a Let._body (or PRIM) vs Let._def (or
      // Lambda).  Not helpful, as its only useful at the top-layer.
      // Structural unification requires the 'occurs check' at each internal
      // layer, which can differ from the top-layer.
      //boolean occurs_fresh = _par==null /*from prims*/ || _par.is_fresh(_name,this);
      T2 t = _par==null ? null : _par.lookup(_name); // Lookup in current env
      if( t==null ) t = PRIMS.get(_name);            // Lookup in prims
      if( t==null )
        throw new RuntimeException("Parse error, "+_name+" is undefined");
      return t.find().fresh_unify(find(),_nongen,work);
    }
    @Override T2 lookup(String name) { throw unimpl("should not reach here"); }
    @Override void add_kids(Worklist work) { }
    @Override void add_occurs(Worklist work) {
      T2 t = _par==null ? null : _par.lookup(_name); // Lookup in current env
      if( t==null ) t = PRIMS.get(_name);            // Lookup in prims
      t = t.find();
      if( t.occurs_in(_par) )                        // Got captured in some parent?
        t.add_deps_work(work);                       // Need to revisit dependent ids
    }
    @Override int prep_tree( Syntax par, VStack nongen, Worklist work ) {
      prep_tree_impl(par,nongen,work,T2.make_leaf());
      for( Syntax syn = _par; syn!=null; syn = syn._par )
        syn.prep_lookup_deps(this);
      return 1;
    }
    @Override void prep_lookup_deps(Ident id) { throw unimpl("should not reach here"); }
    @Override boolean more_work(Worklist work) { return more_work_impl(work); }
  }

  static class Lambda extends Syntax {
    final String[] _args;
    final Syntax _body;
    T2[] _targs;
    Lambda(Syntax body, String... args) {
      _args=args;
      _body=body;
      _targs = new T2[args.length];
      for( int i=0; i<args.length; i++ ) _targs[i] = T2.make_leaf();
    }
    @Override SB str(SB sb) {
      sb.p("{ ");
      for( String arg : _args ) sb.p(arg).p(' ');
      return _body.str(sb.p("-> ")).p(" }");
    }
    @Override SB p1(SB sb) {
      sb.p("{ ");
      for( String arg : _args ) sb.p(arg).p(' ');
      return sb.p(" -> ... } ");
    }
    @Override SB p2(SB sb, VBitSet dups) { return _body.p0(sb,dups); }
    T2 targ(int i) { T2 targ = _targs[i].find(); return targ==_targs[i] ? targ : (_targs[i]=targ); }
    @Override boolean hm(Worklist work) {
      // The normal lambda work
      boolean progress = false;
      T2 old = find();
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
    @Override T2 lookup(String name) {
      for( int i=0; i<_args.length; i++ )
        if( Util.eq(_args[i],name) ) return targ(i);
      return _par==null ? null : _par.lookup(name);
    }
    @Override void add_kids(Worklist work) { work.push(_body); }
    @Override void add_occurs(Worklist work) {
      for( int i=0; i<_targs.length; i++ )
        if( targ(i).occurs_in_type(find()) ) work.addAll(_targs[i]._deps);
    }
    @Override int prep_tree( Syntax par, VStack nongen, Worklist work ) {
      prep_tree_impl(par,nongen,work,T2.make_leaf());
      VStack vs = nongen;
      for( int i=0; i<_targs.length; i++ )
        vs = new VStack(vs,_targs[i]);
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
    @Override SB p2(SB sb, VBitSet dups) { _body.p0(sb,dups); return _def.p0(sb,dups); }
    T2 targ() { T2 targ = _targ.find(); return targ==_targ ? targ : (_targ=targ); }
    @Override boolean hm(Worklist work) {
      return targ().unify(_def.find(),work);
    }
    @Override T2 lookup(String name) {
      if( Util.eq(_arg0,name) ) return targ();
      return _par==null ? null : _par.lookup(name);
    }
    @Override void add_kids(Worklist work) { work.push(_body); work.push(_def); }
    @Override void add_occurs(Worklist work) {
      if( targ().occurs_in_type(_def.find()) ) work.addAll(_targ._deps);
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

    @Override boolean hm(Worklist work) {
      // Unifiying these: make_fun(this.arg0 this.arg1 -> new     )
      //                      _fun{_fun.arg0 _fun.arg1 -> _fun.rez}

      // Discover not-nil in the trivial case of directly using the 'if'
      // primitive against a T2.is_struct().  Will not work if 'if' is some
      // more hidden or complex function (e.q. '&&' or '||') or the predicate
      // implies not-null on some other struct.
      boolean progress = false;
      T2 str = is_if_nil();
      if( str!=null && str.is_struct() && str._con==null ) {
        if( work==null ) return true;
        progress = true;
        str._con = TypeNil.NIL;    // Add nil to a struct
        work.addAll(str._deps);
      }

      // Progress if:
      //   _fun is not a function
      //   any arg-pair-unifies make progress
      //   this-unify-_fun.return makes progress
      T2 tfun = _fun.find();
      if( !tfun.is_fun() ) {
        if( work==null ) return true; // Will-progress & just-testing
        T2[] targs = new T2[_args.length+1];
        for( int i=0; i<_args.length; i++ )
          targs[i] = _args[i].find();
        targs[_args.length] = find(); // Return
        T2 nfun = T2.make_fun(targs);
        return tfun.unify(nfun,work);
      }

      if( tfun._args.length != _args.length+1 )
        throw new RuntimeException("Mismatched argument lengths");
      // Check for progress amongst arg pairs
      for( int i=0; i<_args.length; i++ ) {
        progress |= tfun.args(i).unify(_args[i].find(),work);
        if( progress && work==null )
          return true;          // Will-progress & just-testing early exit
      }
      progress |= tfun.args(_args.length).unify(find(),work);
      return progress;
    }
    @Override T2 lookup(String name) { return _par==null ? null : _par.lookup(name); }
    @Override void add_kids(Worklist work) { for( Syntax arg : _args ) work.push(arg); }
    @Override int prep_tree(Syntax par, VStack nongen, Worklist work) {
      prep_tree_impl(par,nongen,work,T2.make_leaf());
      int cnt = 1+_fun.prep_tree(this,nongen,work);
      for( Syntax arg : _args ) cnt += arg.prep_tree(this,nongen,work);
      T2 str = is_if_nil();
      if( str!=null ) str.push_update(this);
      return cnt;
    }
    @Override void prep_lookup_deps(Ident id) { }
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

  // Structure or Records.
  static class Struct extends Syntax {
    final String[]  _ids;
    final Syntax[] _flds;
    Struct( String[] ids, Syntax[] flds ) { _ids=ids; _flds=flds; }
    @Override SB str(SB sb) {
      sb.p("@{");
      for( int i=0; i<_ids.length; i++ ) {
        sb.p(' ').p(_ids[i]).p(" = ");
        _flds[i].str(sb);
        if( i < _ids.length-1 ) sb.p(',');
      }
      return sb.p("}");
    }
    @Override SB p1(SB sb) { return sb.p("@{ ... } "); }
    @Override SB p2(SB sb, VBitSet dups) {
      for( int i=0; i<_ids.length; i++ )
        _flds[i].p0(sb.p(_ids[i]).p(" = "),dups);
      return sb;
    }
    @Override boolean hm(Worklist work) {
      // Check for progress before making new
      T2 old = find();
      if( old.is_struct() ) {  // Already a struct?  Compare-by-parts
        for( int i=0; i<_ids.length; i++ ) {
          int idx = Util.find(old._ids,_ids[i]);
          if( idx== -1 || old.args(idx).unify(_flds[i].find(),work) ) { old=null; break; }
        }
        if( old!=null ) return false; // Shortcut: no progress, no allocation
      }

      // Make a new T2 for progress
      T2[] t2s = new T2[_ids.length];
      for( int i=0; i<_ids.length; i++ )
        t2s[i] = _flds[i].find();
      T2 tstruct = T2.make_struct(_ids,t2s);
      return tstruct.unify(find(),work);
    }
    @Override T2 lookup(String name) { return _par==null ? null : _par.lookup(name); }
    @Override void add_kids(Worklist work) { for( Syntax fld : _flds ) work.push(fld); }
    @Override int prep_tree(Syntax par, VStack nongen, Worklist work) {
      T2[] t2s = new T2[_ids.length];
      prep_tree_impl(par, nongen, work, T2.make_struct(_ids,t2s));
      int cnt = 1;              // One for self
      for( int i=0; i<_flds.length; i++ ) { // Prep all sub-fields
        cnt += _flds[i].prep_tree(this,nongen,work);
        t2s[i] = _flds[i].find();
      }
      return cnt;
    }
    @Override void prep_lookup_deps(Ident id) { }
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
    final Syntax _str;
    Field( String id, Syntax str ) { _id=id; _str=str; }
    @Override SB str(SB sb) { return _str.str(sb.p(".").p(_id).p(' ')); }
    @Override SB p1 (SB sb) { return sb.p(".").p(_id); }
    @Override SB p2(SB sb, VBitSet dups) { return _str.p0(sb,dups); }
    @Override boolean hm(Worklist work) {
      T2 str = _str.find();
      int idx = str._ids==null ? -1 : Util.find(str._ids,_id);
      if( idx==-1 )             // Not a struct or no field, force it to be one
        return work==null || T2.make_struct(new String[]{_id}, new T2[]{find().push_update(str._deps)}).unify(str, work);

      // Unify the field
      return str.args(idx).unify(find(),work);
    }
    @Override T2 lookup(String name) { return _par==null ? null : _par.lookup(name); }
    @Override void add_kids(Worklist work) { work.push(_str); }
    @Override void add_occurs(Worklist work) { _str.add_occurs(work); }
    @Override int prep_tree(Syntax par, VStack nongen, Worklist work) {
      prep_tree_impl(par, nongen, work, T2.make_leaf());
      return _str.prep_tree(this,nongen,work)+1;
    }
    @Override void prep_lookup_deps(Ident id) { }
    @Override boolean more_work(Worklist work) {
      if( !more_work_impl(work) ) return false;
      return _str.more_work(work);
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

    // Base types carry a concrete Type
    Type _con;

    // Structs have field names
    @NotNull String[] _ids;

    // Dependent (non-local) tvars to revisit
    Ary<Syntax> _deps;


    static T2 make_fun(T2... args) { return new T2("->",null,null,args); }
    static T2 make_leaf() { return new T2("V"+CNT,null,null,new T2[1]); }
    static T2 make_base(Type con) { return new T2("Base",con,null); }
    static T2 make_nil() { return new T2("Nil",null,null); }
    static T2 make_struct( String[] ids, T2[] flds ) { return new T2("@{}", null,ids,flds); }
    static T2 prim(String name, T2... args) { return new T2(name,null,null,args); }
    T2 copy() { return new T2(_name,_con,_ids,new T2[_args.length]); }

    private T2(@NotNull String name, Type con, String[] ids, T2 @NotNull ... args) {
      _uid = CNT++;
      _name= name;
      _con = con;
      _ids = ids;
      _args= args;
    }

    // A type var, not a concrete leaf.  Might be U-Fd or not.
    boolean is_leaf() { return _name.charAt(0)=='V' || (isa("Base") && _con==null); }
    boolean no_uf() { return !is_leaf() || _args[0]==null; }
    boolean isa(String name) { return Util.eq(_name,name); }
    boolean is_base() { return isa("Base") && _con!=null; }
    boolean is_nil()  { return isa("Nil"); }
    boolean is_fun () { return isa("->"); }
    boolean is_struct() { return isa("@{}"); }

    // U-F find
    T2 find() {
      if( !is_leaf() ) return this; // Shortcut
      T2 u = _args[0];
      if( u==null ) return this; // Shortcut
      if( u.no_uf() ) return u;  // Shortcut
      // U-F fixup
      while( u.is_leaf() && u._args[0]!=null ) u = u._args[0];
      T2 v = this, v2;
      while( !v.is_leaf() && (v2=v._args[0])!=u ) { v._args[0]=u; v = v2; }
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
      _args[0] = that;         // U-F update
      if( _name.charAt(0)!='V' ) _name = "V"+_uid; // Flag as a leaf & unified
      assert !no_uf();
      return true;
    }

    // Unify a struct with nil
    boolean or0(T2 that, Worklist work) {
      assert is_nil() && that.is_struct();
      if( work==null ) return that._con==null; // Progress if moving from not-nil to nilable
      if( that._con == TypeNil.NIL ) return false;// Already nilable
      _args = new T2[1];                       // Room for U-F
      that._con=TypeNil.NIL;
      return union(that,work);
    }

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

      // two leafs union in either order, so keep lower uid
      if( is_leaf() && that.is_leaf() && _uid<that._uid ) return that.union(this,work);
      if(      is_leaf() ) return      union(that,work);
      if( that.is_leaf() ) return that.union(this,work);
      if( is_base() && that.is_base() ) return unify_base(that,work);
      // Unify struct with nil
      if( is_nil() && that.is_struct() ) return or0(that,work);
      if( that.is_nil() && is_struct() ) return that.or0(this,work);

      if( !Util.eq(_name,that._name) )
        throw new RuntimeException("Cannot unify "+this+" and "+that);
      assert _args!=that._args; // Not expecting to share _args and not 'this'
      if( !is_struct() && _args.length != that._args.length )
        throw new RuntimeException("Cannot unify "+this+" and "+that);

      // Cycle check
      long luid = dbl_uid(that);
      T2 rez = DUPS.get(luid);
      assert rez==null || rez==that;
      if( rez!=null ) return false; // Been there, done that
      DUPS.put(luid,that);          // Close cycles

      if( work==null ) return true; // Here we definitely make progress; bail out early if just testing

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
        if( _con!=null && that._con==null ) that._con=TypeNil.NIL;
        if( this==that ) return true; // Might have unioned this-into-that recursively, exit now with progress
      } else {
        for( int i=0; i<_args.length; i++ ) // For all fields in LHS
          args(i)._unify(that.args(i),work);
      }
      return union(that,work);
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
      Type con = _con.meet(that._con);
      if( con==that._con ) return false; // No progress
      if( work==null ) return true;
      that._con = con;          // Yes progress, but no update if null work
      _args = new T2[1];        // Room for a forwarding pointer
      _con=null;                // Flip from 'Base' to 'Leaf'
      return union(that,work);
    }
    private boolean fresh_base(T2 that, Worklist work) {
      Type con = _con.meet(that._con);
      if( con==that._con ) return false; // No progress
      if( work==null ) return true;
      that._con = con;          // Yes progress, but no update if null work
      return true;
    }

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

      // Attempting to pre-compute occurs_in, by computing 'is_fresh' in the
      // Ident.hm() call does NOT work.  The 'is_fresh' is for the top-layer
      // only, not the internal layers.  As soon as we structural recurse down
      // a layer, 'is_fresh' does not correlate with an occurs_in check.
      if( nongen_in(nongen) ) return vput(that,_unify(that,work)); // Famous 'occurs-check', switch to normal unify
      if( this.is_leaf() ) return vput(that,false); // Lazy map LHS tvar to RHS
      if( that.is_leaf() )             // RHS is a tvar; union with a deep copy of LHS
        return work==null || vput(that,that.union(_fresh(nongen),work));
      // Bases MEET cons in RHS
      if( is_base() && that.is_base() ) return vput(that,fresh_base(that,work));
      // Unify struct with nil
      if( is_nil() && that.is_struct() ) return vput(that,or0(that,work));
      if( that.is_nil() && is_struct() )
        return work==null || vput(that,that.or0(_fresh(nongen),work));

      if( !Util.eq(_name,that._name) ||
          (!is_struct() && _args.length != that._args.length) )
        throw new RuntimeException("Cannot unify "+this+" and "+that);

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
      if( _con!=null && that._con==null ) {
        if( work==null ) return true; // Will progress
        that._con = TypeNil.NIL;         // Allow nil
      }
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
        T2 t = nongen_in(nongen) ? this : T2.make_leaf();
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

    private static final VBitSet ODUPS = new VBitSet();
    boolean occurs_in(Syntax syn) {
      if( syn==null ) return false;
      if( is_base() ) return false;
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
      if( is_base() && t.is_base() )
        return _con==t._con;    // Base-cases have to be completely identical
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
      if( _con != t._con ) return false;
      for( int i=0; i<_args.length; i++ ) {
        int idx = Util.find(t._ids,_ids[i]);
        if( idx==-1 || !args(i)._cycle_equals(t.args(idx)) )
          return false;
      }
      return true;
    }

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
      if( visit.tset(_uid) && no_uf() ) dups.set(_uid);
      else
        for( T2 t : _args )
          if( t!=null )
            t._get_dups(visit,dups);
      return dups;
    }

    // Fancy print for Debuggers - includes explicit U-F re-direction.
    // Does NOT roll-up U-F, has no side-effects.
    @Override public String toString() { return str(new SB(), new VBitSet(), get_dups(new VBitSet()) ).toString(); }
    SB str(SB sb, VBitSet visit, VBitSet dups) {
      if( is_leaf() || is_base() ) {
        if( is_base() ) sb.p(_con instanceof TypeMemPtr ? "str" : _con.toString()); else sb.p(_name);
        return _args.length==0 || _args[0]==null ? sb : _args[0].str(sb.p(">>"), visit, dups);
      }
      boolean dup = dups.get(_uid);
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
        if( _con==TypeNil.NIL ) sb.p('?');
        return sb;
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
      if( is_base() ) return sb.p(_con instanceof TypeMemPtr ? "str" : _con.toString() );
      if( is_leaf() || dups.get(_uid) ) { // Leafs or Duplicates?  Take some effort to pretty-print cycles
        Integer ii = VNAMES.get(this);
        if( ii==null )  VNAMES.put(this,ii=VCNT++);
        // 2nd and later visits use the short form
        boolean later = !is_leaf() && visit.tset(_uid);
        if( later ) sb.p('$');
        char c = (char)('A'+ii);
        if( c<'V' ) sb.p(c); else sb.p("V"+ii);
        if( is_leaf() || later ) return sb;
        // First visit prints the V._uid and the type
        sb.p(':');
      }

      // Special printing for functions: { arg -> body }
      if( is_fun() ) {
        sb.p("{ ");
        for( int i=0; i<_args.length-1; i++ )
          args(i)._p(sb,visit,dups).p(" ");
        return args(_args.length-1)._p(sb.p("-> "),visit,dups).p(" }");
      }

      // Special printing for structures: @{ fld0 = body, fld1 = body, ... }
      if( is_struct() ) {
        sb.p("@{");
        for( int i=0; i<_ids.length; i++ )
          args(i)._p(sb.p(' ').p(_ids[i]).p(" = "),visit,dups).p(',');
        sb.unchar().p("}");
        if( _con==TypeNil.NIL ) sb.p('?');
        return sb;
      }

      // Generic structural T2: (fun arg0 arg1...)
      sb.p("(").p(_name).p(" ");
      for( int i=0; i<_args.length; i++ ) args(i)._p(sb,visit,dups).p(" ");
      return sb.unchar().p(")");
    }

    static void reset() { CNT=0; DUPS.clear(); VARS.clear(); ODUPS.clear(); CDUPS.clear(); UPDATE_VISIT.clear(); }
  }

}
