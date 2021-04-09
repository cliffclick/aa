package com.cliffc.aa;

import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;
import org.jetbrains.annotations.NotNull;

import java.util.HashMap;
import java.util.HashSet;

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

// Lazily computes 'Fresh' copies instead of eagerly.


public class HM {
  static final HashMap<String,T2> PRIMS = new HashMap<>();
  static boolean DEBUG_LEAKS=false;

  public static T2 hm( Syntax prog) {
    Object dummy = TypeStruct.DISPLAY;

    Worklist work = new Worklist();

    // Simple types
    T2 bool  = T2.make_base(TypeInt.BOOL);
    T2 int64 = T2.make_base(TypeInt.INT64);
    T2 flt64 = T2.make_base(TypeFlt.FLT64);
    T2 strp  = T2.make_base(TypeMemPtr.STRPTR);

    // Primitives
    T2 var1 = T2.make_leaf();
    T2 var2 = T2.make_leaf();

    PRIMS.put("pair1",T2.make_fun(var1, T2.make_fun(var2, T2.prim("pair",var1,var2) )));
    PRIMS.put("pair",T2.make_fun(var1, var2, T2.prim("pair",var1,var2) ));

    PRIMS.put("if/else",T2.make_fun(bool,var1,var1,var1));

    PRIMS.put("dec",T2.make_fun(int64,int64));
    PRIMS.put("*"  ,T2.make_fun(int64,int64,int64));
    PRIMS.put("==0",T2.make_fun(int64,bool));
    PRIMS.put("isempty",T2.make_fun(strp,bool));

    // Print a string; int->str
    PRIMS.put("str",T2.make_fun(int64,strp));
    // Factor; FP div/mod-like operation
    PRIMS.put("factor",T2.make_fun(flt64,T2.prim("divmod",flt64,flt64)));

    // Prep for SSA: pre-gather all the (unique) ids
    prog.prep_tree(null,work);

    while( work.len()>0 ) {     // While work
      int oldcnt = T2.CNT;      // Used for cost-check when no-progress
      Syntax syn = work.pop();  // Get work
      T2 old = syn._t;          // Old value for progress assert
      T2 t = syn.hm(work);      // Get work results
      if( t!=null ) {           // Progress?
        assert !t.progress(old.find());// monotonic: unifying with the result is no-progress
        syn._t=t;               // Progress!
        syn.add_kids(work);     // Push children on worklist
        syn.add_occurs(work);   // Push occurs-check ids on worklist
        if( syn._par !=null ) work.push(syn._par); // Parent updates
      } else {
        assert !DEBUG_LEAKS || oldcnt==T2.CNT;  // No-progress consumes no-new-T2s
      }
      // VERY EXPENSIVE ASSERT: O(n^2).  Every Syntax that makes progress is on the worklist
      assert prog.more_work(work);
    }
    assert prog.more_work(work);
    return prog._t;
  }
  static void reset() { PRIMS.clear(); T2.reset(); }

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


  public static abstract class Syntax {
    Syntax _par;
    T2 _t;                      // Current HM type
    T2 find() {                 // U-F find
      T2 t = _t.find();
      return t==_t ? t : (_t=t);
    }

    // Compute a new HM type.  If no modifications are needed, return null.  If
    // 'work' is null, then instead return '_t' without making modifications to
    // anything.  If 'work' is available, return a modified result (might not be
    // equal to '_t') and update the worklist.
    abstract T2 hm(Worklist work);

    abstract void prep_tree(Syntax par, Worklist work);
    final void prep_tree_impl( Syntax par, T2 t, Worklist work ) { _par=par; _t=t; work.push(this); }
    abstract boolean prep_lookup_deps(Ident id);

    abstract T2 lookup(String name); // Lookup name in scope & return type; TODO: pre-cache this.

    abstract void add_kids(Worklist work); // Add children to worklist
    void add_occurs(Worklist work){}

    // Giant Assert: True if OK; all Syntaxs off worklist do not make progress
    abstract boolean more_work(Worklist work);
    final boolean more_work_impl(Worklist work) {
      boolean foo = work.has(this) || hm(null)==null;
      return foo;
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

  public static class Con extends Syntax {
    final Type _con;
    Con(Type con) { super(); _con=con; }
    @Override SB str(SB sb) { return p1(sb); }
    @Override SB p1(SB sb) { return sb.p(_con instanceof TypeMemPtr ? "str" : _con.toString()); }
    @Override SB p2(SB sb, VBitSet dups) { return sb; }
    @Override T2 hm(Worklist work) { assert find().isa("Base"); return null; }
    @Override T2 lookup(String name) { throw unimpl("should not reach here"); }
    @Override void add_kids(Worklist work) { }
    @Override void prep_tree( Syntax par, Worklist work ) { prep_tree_impl(par, T2.make_base(_con), work); }
    @Override boolean prep_lookup_deps(Ident id) { throw unimpl("should not reach here"); }
    @Override boolean more_work(Worklist work) { return more_work_impl(work); }
  }

  public static class Ident extends Syntax {
    final String _name;
    Ident(String name) { _name=name; }
    @Override SB str(SB sb) { return p1(sb); }
    @Override SB p1(SB sb) { return sb.p(_name); }
    @Override SB p2(SB sb, VBitSet dups) { return sb; }
    @Override T2 hm(Worklist work) {
      T2 t = _par==null ? null : _par.lookup(_name); // Lookup in current env
      if( t==null ) t = PRIMS.get(_name);            // Lookup in prims
      if( t==null )
        throw new RuntimeException("Parse error, "+_name+" is undefined");
      return t.fresh_unify(find(),_par,work);
    }
    @Override T2 lookup(String name) { throw unimpl("should not reach here"); }
    @Override void add_kids(Worklist work) { }
    @Override void add_occurs(Worklist work) {
      T2 t = _par==null ? null : _par.lookup(_name); // Lookup in current env
      if( t==null ) t = PRIMS.get(_name);            // Lookup in prims
      if( t.occurs_in(_par) )                        // Got captured in some parent?
        t.add_deps_work(work);                       // Need to revisit dependent ids
    }
    @override void prep_tree( Syntax par, Worklist work ) {
      prep_tree_impl(par,T2.make_leaf(),work);
      Syntax syn = _par;
      while( syn!=null && !syn.prep_lookup_deps(this) )
        syn = syn._par;
    }
    @Override boolean prep_lookup_deps(Ident id) { throw unimpl("should not reach here"); }
    @Override boolean more_work(Worklist work) { return more_work_impl(work); }
  }

  public static class Lambda extends Syntax {
    final String _arg0;
    final Syntax _body;
    T2 _targ;
    Lambda(String arg0, Syntax body) { _arg0=arg0; _body=body; _targ = T2.make_leaf(); }
    @Override SB str(SB sb) { return _body.str(sb.p("{ ").p(_arg0).p(" -> ")).p(" }"); }
    @Override SB p1(SB sb) { return sb.p("{ ").p(_arg0).p(" -> ... } "); }
    @Override SB p2(SB sb, VBitSet dups) { return _body.p0(sb,dups); }
    T2 targ() { T2 targ = _targ.find(); return targ==_targ ? targ : (_targ=targ); }
    @Override T2 hm(Worklist work) {
      // The normal lambda work
      T2 fun = T2.make_fun(targ(),_body.find());
      return find().unify(fun,work);
    }
    @Override T2 lookup(String name) {
      if( Util.eq(_arg0,name) ) return targ();
      return _par==null ? null : _par.lookup(name);
    }
    @Override void add_kids(Worklist work) { work.push(_body); }
    @Override void add_occurs(Worklist work) {
      if( targ().occurs_in_type(_t) ) work.addAll(_targ._deps);
    }
    @Override void prep_tree( Syntax par, Worklist work ) {
      prep_tree_impl(par,T2.make_leaf(),work);
      _body.prep_tree(this,work);
    }
    @Override boolean prep_lookup_deps(Ident id) {
      return Util.eq(id._name,_arg0) && _targ.push_update(id);
    }
    @Override boolean more_work(Worklist work) {
      if( !more_work_impl(work) ) return false;
      return _body.more_work(work);
    }
  }

  public static class Lambda2 extends Syntax {
    final String _arg0, _arg1;
    final Syntax _body;
    T2 _targ0;
    T2 _targ1;
    Lambda2(String arg0, String arg1, Syntax body) { _arg0=arg0; _arg1 = arg1; _body=body; _targ0 = T2.make_leaf(); _targ1 = T2.make_leaf(); }
    @Override SB str(SB sb) { return _body.str(sb.p("{ ").p(_arg0).p(" ").p(_arg1).p(" -> ")).p(" }"); }
    @Override SB p1(SB sb) { return sb.p("{ ").p(_arg0).p(" ").p(_arg1).p(" -> ... } "); }
    @Override SB p2(SB sb, VBitSet dups) { return _body.p0(sb,dups); }
    T2 targ0() { T2 targ = _targ0.find(); return targ==_targ0 ? targ : (_targ0=targ); }
    T2 targ1() { T2 targ = _targ1.find(); return targ==_targ1 ? targ : (_targ1=targ); }
    @Override T2 hm(Worklist work) {
      // The normal lambda work
      T2 fun = T2.make_fun(targ0(),targ1(),_body.find());
      return find().unify(fun,work);
    }
    @Override T2 lookup(String name) {
      if( Util.eq(_arg0,name) ) return targ0();
      if( Util.eq(_arg1,name) ) return targ1();
      return _par==null ? null : _par.lookup(name);
    }
    @Override void add_kids(Worklist work) { work.push(_body); }
    @Override void add_occurs(Worklist work) {
      if( targ0().occurs_in_type(_t) ) work.addAll(_targ0._deps);
      if( targ1().occurs_in_type(_t) ) work.addAll(_targ1._deps);
    }
    @Override void prep_tree( Syntax par, Worklist work ) {
      prep_tree_impl(par,T2.make_leaf(),work);
      _body.prep_tree(this,work);
    }
    @Override boolean prep_lookup_deps(Ident id) {
      return (Util.eq(id._name,_arg0) && _targ0.push_update(id))
        ||   (Util.eq(id._name,_arg1) && _targ1.push_update(id));
    }
    @Override boolean more_work(Worklist work) {
      if( !more_work_impl(work) ) return false;
      return _body.more_work(work);
    }
  }

  public static class Let extends Syntax {
    final String _arg0;
    final Syntax _def, _body;
    T2 _targ;
    Let(String arg0, Syntax def, Syntax body) { _arg0=arg0; _body=body; _def=def; _targ=T2.make_leaf(); }
    @Override SB str(SB sb) { return _body.str(_def.str(sb.p("let ").p(_arg0).p(" = ")).p(" in ")); }
    @Override SB p1(SB sb) { return sb.p("let ").p(_arg0).p(" = ... in ..."); }
    @Override SB p2(SB sb, VBitSet dups) { _body.p0(sb,dups); return _def.p0(sb,dups); }
    T2 targ() { T2 targ = _targ.find(); return targ==_targ ? targ : (_targ=targ); }
    @Override T2 hm(Worklist work) {
      boolean progress = targ().unify(_def.find(),work) != null;
      return progress ? _body.find() : null;
    }
    @Override T2 lookup(String name) {
      if( Util.eq(_arg0,name) ) return targ();
      return _par==null ? null : _par.lookup(name);
    }
    @Override void add_kids(Worklist work) { work.push(_body); work.push(_def); }
    @Override void add_occurs(Worklist work) {
      if( targ().occurs_in_type(_t) ) work.addAll(_targ._deps);
    }
    @Override void prep_tree( Syntax par, Worklist work ) {
      prep_tree_impl(par,_body._t,work);
      _body.prep_tree(this,work);
      _def .prep_tree(this,work);
      _t = _body._t;
    }
    @Override boolean prep_lookup_deps(Ident id) {
      return Util.eq(id._name,_arg0) && _targ.push_update(id);
    }
    @Override boolean more_work(Worklist work) {
      if( !more_work_impl(work) ) return false;
      return _body.more_work(work) && _def.more_work(work);
    }
  }

  public static class Apply extends Syntax {
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

    @Override T2 hm(Worklist work) {
      // Unifiying these: make_fun(this.arg0 this.arg1 -> new     )
      //                      _fun{_fun.arg0 _fun.arg1 -> _fun.rez}
      // Progress if:
      //   _fun is not a function
      //   any arg-pair-unifies make progress
      //   this-unify-_fun.return makes progress

      T2 tfun = _fun.find();
      if( !tfun.is_fun() ) {
        if( work==null )
          //return this; // Will-progress & testing
          throw unimpl("untested");
        T2[] targs = new T2[_args.length+1];
        for( int i=0; i<_args.length; i++ )
          targs[i] = _args[i].find();
        targs[_args.length] = find(); // Return
        T2 nfun = T2.make_fun(targs);
        T2 ufun = tfun.unify(nfun,work);
        // Return is last element
        return ufun.args(_args.length);
      }

      if( tfun._args.length != _args.length+1 )
        throw new RuntimeException("Mismatched argument lengths");
      // Check for progress amongst arg pairs
      boolean progress = false;
      for( int i=0; i<_args.length; i++ ) {
        T2 arg = tfun.args(i).unify(_args[i].find(),work);
        if( arg!=null ) progress = true;
        if( progress && work==null )
          //return this;          // Will-progress & testing
          throw unimpl("untested");
      }
      T2 arg = tfun.args(_args.length).unify(find(),work);
      if( arg!=null ) progress = true;
      if( progress && work==null )
        //return this;          // Will-progress & testing
        throw unimpl("untested");
      if( !progress ) return null;
      return arg==null ? find() : arg;
    }
    @Override T2 lookup(String name) { return _par==null ? null : _par.lookup(name); }
    @Override void add_kids(Worklist work) { for( Syntax arg : _args ) work.push(arg); }
    @Override void prep_tree(Syntax par,Worklist work) {
      prep_tree_impl(par,T2.make_leaf(),work);
      _fun.prep_tree(this,work);
      for( Syntax arg : _args ) arg.prep_tree(this,work);
    }
    @Override boolean prep_lookup_deps(Ident id) { return false; }
    @Override boolean more_work(Worklist work) {
      if( !more_work_impl(work) ) return false;
      if( !_fun.more_work(work) ) return false;
      for( Syntax arg : _args ) if( !arg.more_work(work) ) return false;
      return true;
    }
  }

  // ---------------------------------------------------------------------
  // T2 types form a Lattice, with 'unify' same as 'meet'.  T2's form a DAG
  // (cycles if i allow recursive unification) with sharing.  Each Syntax has a
  // T2, and the forest of T2s can share.  Leaves of a T2 can be either a
  // simple concrete base type, or a sharable leaf.  Unify is structural, and
  // where not unifyable the union is replaced with an Error.
  public static class T2 {
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

    // Dependent (non-local) tvars to revisit
    Ary<Syntax> _deps;


    static T2 make_fun(T2... args) { return new T2("->",null,args); }
    static T2 make_leaf() { return new T2("V"+CNT,null,new T2[1]); }
    static T2 make_base(Type con) { return new T2("Base",con); }
    static T2 prim(String name, T2... args) { return new T2(name,null,args); }
    T2 copy() { return new T2(_name,_con,new T2[_args.length]); }

    private T2(@NotNull String name, Type con, T2 @NotNull ... args) {
      _uid = CNT++;
      _name= name;
      _con = con;
      _args= args;
    }

    // A type var, not a concrete leaf.  Might be U-Fd or not.
    boolean is_leaf() { return _name.charAt(0)=='V'; }
    boolean no_uf() { return !is_leaf() || _args[0]==null; }
    boolean isa(String name) { return Util.eq(_name,name); }
    boolean is_base() { return isa("Base"); }
    boolean is_fun () { return isa("->"); }

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
    @NotNull T2 union(T2 that, Worklist work) {
      assert is_leaf() && no_uf(); // Cannot union twice
      if( this==that ) return that;
      if( work==null ) return that.progress();
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
      return that.progress();
    }

    // Structural unification progress test
    boolean progress(T2 t) { return unify(t,null)!=null; }
    // Short-cut to set progress
    @NotNull T2 progress() { PROGRESS=1; return this; }

    // Structural unification.  Returns null if no-change.  If work is null,
    // makes no change but returns 'this' instead of a change.  If change and
    // work, returns a new T2 which may (or may not) be equal to either side.
    static private int PROGRESS;
    static private final HashMap<Long,T2> DUPS = new HashMap<>();
    T2 unify( T2 t, Worklist work ) {
      if( this==t ) return null;
      assert DUPS.isEmpty() && PROGRESS==0;
      PROGRESS = -1;
      T2 rez = _unify(t,work);
      DUPS.clear();
      if( PROGRESS<0 ) rez = null; // Return null if no-progress
      PROGRESS=0;               // Reset
      return rez;
    }

    // Structural unification, 'this' into 't'.  No change if just testing
    // (work is null) and returns 't' if progress.  If updating, both 'this'
    // and 't' are the same afterwards.  Sets PROGRESS.
    private @NotNull T2 _unify(T2 t, Worklist work) {
      assert no_uf() && t.no_uf();
      if( this==t ) return this;
      if( PROGRESS>0 && work==null ) return t; // Progress early-exit

      // two leafs union in either order, so keep lower uid
      if( is_leaf() && t.is_leaf() && _uid<t._uid ) return t.union(this,work);
      if(   is_leaf() ) return   union(t   ,work);
      if( t.is_leaf() ) return t.union(this,work);
      if( is_base() && t.is_base() ) return unify_base(t,work);

      if( !Util.eq(_name,t._name) )
        throw new RuntimeException("Cannot unify "+this+" and "+t);
      if( _args==t._args ) return this; // Names are equal, args are equal
      if( _args.length != t._args.length )
        throw new RuntimeException("Cannot unify "+this+" and "+t);

      // Cycle check
      long luid = dbl_uid(t);
      T2 rez = DUPS.get(luid);
      assert rez==null || rez==t;
      if( rez!=null ) return rez; // Been there, done that
      DUPS.put(luid,t);           // Close cycles

      // Structural recursion unification.
      for( int i=0; i<_args.length; i++ )
        t._args[i] = args(i)._unify(t.args(i),work);
      return t;
    }

    long dbl_uid(T2 t) { return ((long)_uid<<32)|t._uid; }

    private T2 unify_base(T2 t, Worklist work) {
      fresh_base(t,work);
      _name = "V"+_uid;         // Flip from 'Base' to 'Leaf'
      _args = new T2[1];        // Room for a forwarding pointer
      _con=null;
      return union(t,work);
    }
    private @NotNull T2 fresh_base(T2 t, Worklist work) {
      Type con = _con.meet(t._con);
      if( con==t._con ) return t;    // No progress
      if( work!=null ) t._con = con; // Yes progress, but no update if null work
      return t.progress();
    }

    // Make a (lazy) fresh copy of 'this', and unify it with 't'.  This is NOT
    // the same as calling 'fresh' then 'unify', as a 'fresh' always makes new
    // T2s which always look like progress during the unify step.  The Syntax
    // is used when making the 'fresh' copy for the occurs_check.  If work is
    // null, we are testing only, make no changes, and always return 't' if
    // PROGRESS.  If PROGRESS and not testing we return the unified value.
    static private final HashMap<T2,T2> VARS = new HashMap<>();
    T2 fresh_unify(T2 t, Syntax syn, Worklist work) {
      assert VARS.isEmpty() && DUPS.isEmpty() && PROGRESS==0;
      PROGRESS = -1;
      int old = CNT;
      T2 rez = _fresh_unify(t,syn,work);
      VARS.clear();  DUPS.clear();
      if( work==null && old!=CNT && DEBUG_LEAKS )
        throw unimpl("busted, made T2s but just testing");
      if( PROGRESS==-1 ) rez = null;
      PROGRESS=0;               // Reset
      return rez;
    }

    // Outer recursive version, wraps a VARS check around other work
    @NotNull T2 _fresh_unify(T2 t, Syntax syn, Worklist work) {
      assert no_uf() && t.no_uf();
      if( PROGRESS>0 && work==null ) return t; // Progress early-exit
      T2 prior = VARS.get(this);
      if( prior!=null )         // Been there, done that
        return prior.find()._unify(t,work);  // Also 'prior' needs unification with 't'
      if( cycle_equals(t) ) return t;
      T2 rez = _fresh_unify_impl(t,syn,work);
      VARS.put(this,rez);
      return rez;
    }

    // Recursive version; VARS check already done
    @NotNull T2 _fresh_unify_impl(T2 t, Syntax syn, Worklist work) {
      if( occurs_in(syn) ) return _unify(t,work); // Famous 'occurs-check', switch to normal unify
      if(   is_leaf() ) return t;  // Lazy map LHS tvar to RHS
      if( t.is_leaf() ) {
        T2 rez = t.union(_fresh(syn),work);
        if( work==null && PROGRESS>0 ) return t; // If progress and testing, always return 't'
        return rez; // RHS is a tvar; union with a deep copy of LHS
      }
      // Bases MEET cons in RHS
      if( is_base() && t.is_base() ) return fresh_base(t,work);

      if( !Util.eq(_name,t._name) ||
          _args.length != t._args.length )
        throw new RuntimeException("Cannot unify "+this+" and "+t);

      // Structural recursion unification, lazy on LHS
      VARS.put(this,t);         // Close cycles
      for( int i=0; i<_args.length; i++ )
        t._args[i] = args(i)._fresh_unify(t.args(i),syn,work);
      return t;
    }

    // Make a "fresh" copy: preserves all sharing structure (including cycles);
    // preserves pre-existing type-vars (in the "par" Syntax scope), but otherwise
    // uses new type-vars at the leaves.
    T2 fresh(Syntax par) {
      assert VARS.isEmpty();
      T2 rez = _fresh(par);
      VARS.clear();
      return rez;
    }
    T2 _fresh(Syntax par) {
      assert no_uf();
      T2 rez = VARS.get(this);
      if( rez!=null ) return rez; // Been there, done that

      if( is_leaf() ) {
        // If occurs_in lexical scope, keep same variable, else make a new leaf
        T2 t = occurs_in(par) ? this : T2.make_leaf();
        VARS.put(this,t);
        return t;
      } else {                  // Structure is deep-replicated
        T2 t = copy();
        VARS.put(this,t);       // Stop cyclic structure looping
        boolean change=false;
        for( int i=0; i<_args.length; i++ ) {
          T2 arg = args(i)._fresh(par);
          if( arg!=_args[i] )
            { t._args[i] = arg; change=true; }
        }
        if( DEBUG_LEAKS && !change )
          throw unimpl("can share here");
        return t;
      }
    }

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
      if( _occurs_in_type(syn.find()) ) return true;
      return syn._par != null && _occurs_in(syn._par);
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
      for( int i=0; i<_args.length; i++ )
        if( !args(i)._cycle_equals(t.args(i)) )
          return false;
      return true;
    }

    // This is a T2 function that is the target of 'fresh', i.e., this function
    // might be fresh-unified with some other function.  Push the application
    // down the function parts; if any changes the fresh-application may make
    // progress.
    static final VBitSet UPDATE_VISIT  = new VBitSet();
    boolean push_update(Syntax a) { assert UPDATE_VISIT.isEmpty(); push_update_impl(a); UPDATE_VISIT.clear(); return true; }
    private void push_update_impl(Syntax a) {
      assert no_uf();
      if( is_leaf() || _args.length==0 ) {
        if( _deps==null ) _deps = new Ary<>(Syntax.class);
        if( _deps.find(a)==-1 ) _deps.push(a);
      } else {
        if( UPDATE_VISIT.tset(_uid) ) return;
        for( int i=0; i<_args.length; i++ )
          args(i).push_update_impl(a);
      }
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
      if( dup ) sb.p('$').p(_uid);
      if( visit.tset(_uid) && dup ) return sb;
      if( dup ) sb.p(':');

      if( is_fun() ) {
        sb.p("{ ");
        for( int i=0; i<_args.length-1; i++ )
          str(sb,visit,_args[i],dups).p(" ");
        return str(sb.p("-> "),visit,_args[_args.length-1],dups).p(" }");
      }
      // Generic structural T2
      sb.p("(").p(_name).p(" ");
      for( T2 t : _args ) str(sb,visit,t,dups).p(" ");
      return sb.unchar().p(")");
    }
    static private SB str(SB sb, VBitSet visit, T2 t, VBitSet dups) { return t==null ? sb.p("_") : t.str(sb,visit,dups); }

    // Same as toString but calls find().  Can thus side-effect & roll-up U-Fs, so not a toString
    public String p() { return p(get_dups(new VBitSet())); }
    String p(VBitSet dups) { return find()._p(new SB(), new VBitSet(), dups).toString(); }
    private SB _p(SB sb, VBitSet visit, VBitSet dups) {
      assert no_uf();
      if( is_base() ) return sb.p(_con instanceof TypeMemPtr ? "str" : _con.toString() );
      if( is_leaf() ) return sb.p(_name);
      boolean dup = dups.get(_uid);
      if( dup ) sb.p('$').p(_uid);
      if( visit.tset(_uid) && dup ) return sb;
      if( dup ) sb.p(':');
      if( is_fun() ) {
        sb.p("{ ");
        for( int i=0; i<_args.length-1; i++ )
          args(i)._p(sb,visit,dups).p(" ");
        return args(_args.length-1)._p(sb.p("-> "),visit,dups).p(" }");
      }
      // Generic structural T2
      sb.p("(").p(_name).p(" ");
      for( int i=0; i<_args.length; i++ ) args(i)._p(sb,visit,dups).p(" ");
      return sb.unchar().p(")");
    }

    static void reset() { CNT=0; PROGRESS=0; DUPS.clear(); VARS.clear(); ODUPS.clear(); CDUPS.clear(); UPDATE_VISIT.clear(); }
  }

}
