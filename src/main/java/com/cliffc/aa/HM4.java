package com.cliffc.aa;

import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;
import org.jetbrains.annotations.NotNull;

import java.util.HashMap;

// Hindley-Milner typing.  Complete stand-alone, for research.  MEETs base
// types, instead of declaring type error.  Requires SSA renumbering; looks
// 'up' the Syntax tree for variables instead of building a 'nongen' set.
//
// T2 types form a Lattice, with 'unify' same as 'meet'.  T2's form a DAG
// (cycles if i allow recursive unification) with sharing.  Each Syntax has a
// T2, and the forest of T2s can share.  Leaves of a T2 can be either a simple
// concrete base type, or a sharable leaf.  Unify is structural, and where not
// unifyable the union is replaced with an Error.

public class HM4 {
  static final HashMap<String,T2> PRIMS = new HashMap<>();

  public static T2 hm( Syntax prog) {
    Object dummy = TypeStruct.DISPLAY;

    Ary<Syntax> work = new Ary<>(Syntax.class);

    // Simple types
    T2 bool  = T2.base(TypeInt.BOOL);
    T2 int64 = T2.base(TypeInt.INT64);
    T2 flt64 = T2.base(TypeFlt.FLT64);
    T2 strp  = T2.base(TypeMemPtr.STRPTR);

    // Primitives
    T2 var1 = T2.tnew();
    T2 var2 = T2.tnew();

    PRIMS.put("pair" ,T2.fresh("TOP",T2.fun(var1, T2.fun(var2, T2.prim("pair" ,var1,var2)))));
    PRIMS.put("pair2",T2.fresh("TOP",T2.fun(var1,        var2, T2.prim("pair2",var1,var2) )));

    //PRIMS.put("if/else" ,new HMT(T2.fun(bool,T2.fun(var1,T2.fun(var1,var1)))));
    PRIMS.put("if/else3",T2.fresh("TOP",T2.fun(bool,var1,var1,var1)));

    PRIMS.put("dec",T2.fresh("TOP",T2.fun(int64,int64)));
    PRIMS.put("*"  ,T2.fresh("TOP",T2.fun(int64,T2.fun(int64,int64))));
    PRIMS.put("*2" ,T2.fresh("TOP",T2.fun(int64,int64,int64)));
    PRIMS.put("==0",T2.fresh("TOP",T2.fun(int64,bool)));
    PRIMS.put("isempty",T2.fresh("TOP",T2.fun(strp,bool)));

    // Print a string; int->str
    PRIMS.put("str",T2.fresh("TOP",T2.fun(int64,strp)));
    // Factor; FP div/mod-like operation
    PRIMS.put("factor",T2.fresh("TOP",T2.fun(flt64,T2.prim("divmod",flt64,flt64))));

    // Prep for SSA: pre-gather all the (unique) ids
    prog.prep_tree(null,work);

    int cnt=0;
    while( !work.isEmpty() ) {  // While work
      Syntax syn = work.del(cnt%work._len);  // Get work
      T2 t = syn.hm(work);      // Get work results
      T2 tsyn = syn.find();
      if( t!=tsyn ) {             // Progress?
        assert !t.progress(tsyn); // monotonic: unifying with the result is no-progress
        syn._t=t;                 // Progress!
        if( syn._par !=null ) work.push(syn._par); // Parent updates
      }
      // VERY EXPENSIVE ASSERT: O(n^2).  Every Syntax that makes progress is on the worklist
      //assert prog.more_work(work);
      cnt++;
    }
    assert prog.more_work(work);
    return prog._t;
  }
  static void reset() { PRIMS.clear(); T2.reset(); }

  public static abstract class Syntax {
    Syntax _par;
    T2 _t;                      // Current HM type
    T2 find() {                 // U-F find
      T2 t = _t.find();
      return t==_t ? t : (_t=t);
    }

    // Compute a new HM type, without modification of any existing T2 in any Syntax
    abstract T2 hm(Ary<Syntax> work);

    abstract void prep_tree(Syntax par,Ary<Syntax> work);
    void prep_tree_impl( Syntax par, T2 t, Ary<Syntax> work ) { _par=par; _t=t; work.push(this); }
    T2 prep_tree_lookup(String name, Syntax prior) { return null; }

    // Giant Assert: True if OK; all Syntaxs off worklist do not make progress
    abstract boolean more_work(Ary<Syntax> work);
    final boolean more_work_impl(Ary<Syntax> work) {
      if( work.find(this)!=-1 ) return true; // On worklist, so ok
      // Check does not make progress
      int old = T2.CNT;  int olen = work._len;
      boolean more_work;
      try {
        T2 t = find();
        Type con = t._con;
        T2 hm = hm(null);       // Run H-M, with null work, looking for progress
        T2 un = find().unify(hm,null);
        more_work = t!=un || con!=un._con || work._len!=olen; // Something happened?
        assert !more_work;
      } catch( RuntimeException no_unify ) { more_work=true; } // Fail to unify assert is progress
      if( !more_work ) T2.CNT=old;  // Reset if no error; prevents assert from endlessly raising CNT
      return !more_work;
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
    abstract void live(IBitSet visit);
  }

  public static class Con extends Syntax {
    final Type _con;
    Con(Type con) { super(); _con=con; }
    @Override SB str(SB sb) { return p1(sb); }
    @Override SB p1(SB sb) { return sb.p(_con instanceof TypeMemPtr ? "str" : _con.toString()); }
    @Override SB p2(SB sb, VBitSet dups) { return sb; }
    @Override T2 hm(Ary<Syntax> work) { return find(); }
    @Override void prep_tree( Syntax par, Ary<Syntax> work ) { prep_tree_impl(par, T2.base(_con), work); }
    @Override boolean more_work(Ary<Syntax> work) { return more_work_impl(work); }
    @Override void live(IBitSet visit) {if( _t!=null ) _t.live(visit);}
  }

  public static class Ident extends Syntax {
    final String _name;
    Ident(String name) { _name=name; }
    @Override SB str(SB sb) { return p1(sb); }
    @Override SB p1(SB sb) { return sb.p(_name); }
    @Override SB p2(SB sb, VBitSet dups) { return sb; }
    @Override T2 hm(Ary<Syntax> work) { return find(); }
    @Override void prep_tree( Syntax par, Ary<Syntax> work ) {
      // Find Ident in some lexical scope.  Get a T2 for it.
      T2 t=null;
      for( Syntax syn = par, prior=this; syn!=null; prior=syn, syn=syn._par )
        if( (t = syn.prep_tree_lookup(_name,prior)) !=null )
          break;
      if( t==null ) t = PRIMS.get(_name);  // Check prims; always FRESH
      if( t==null ) throw new RuntimeException("Parse error, "+_name+" is undefined");
      prep_tree_impl(par,t,work);
    }
    @Override boolean more_work(Ary<Syntax> work) { return more_work_impl(work); }
    @Override void live(IBitSet visit) {if( _t!=null ) _t.live(visit);}
  }

  public static class Lambda extends Syntax {
    final String _arg0;
    final Syntax _body;
    T2 _targ;
    Lambda(String arg0, Syntax body) { _arg0=arg0; _body=body; _targ = T2.tnew(); }
    @Override SB str(SB sb) { return _body.str(sb.p("{ ").p(_arg0).p(" -> ")).p(" }"); }
    @Override SB p1(SB sb) { return sb.p("{ ").p(_arg0).p(" -> ... } "); }
    @Override SB p2(SB sb, VBitSet dups) { return _body.p0(sb,dups); }
    T2 targ() { T2 targ = _targ.find(); return targ==_targ ? targ : (_targ=targ); }
    @Override T2 hm(Ary<Syntax> work) {
      assert !targ().is_fresh();
      // The normal lambda work
      T2 fun = T2.fun(targ(),_body.find());
      // Force forwards progress; an Apply may already have lifted _t to
      // something better than just a plain fun wrapper.
      return find().unify(fun,work);
    }
    @Override void prep_tree( Syntax par, Ary<Syntax> work ) {
      prep_tree_impl(par,T2.tnew(),work);
      _body.prep_tree(this,work);
    }
    // If found name, inside a Lambda so NOT fresh
    @Override T2 prep_tree_lookup(String name, Syntax prior) { return Util.eq(_arg0,name) ? _targ : null; }
    @Override boolean more_work(Ary<Syntax> work) {
      if( !more_work_impl(work) ) return false;
      return _body.more_work(work);
    }
    @Override void live(IBitSet visit) {
      if( _t!=null ) _t.live(visit);
      _targ.live(visit);
      _body.live(visit);
    }
  }

  public static class Lambda2 extends Syntax {
    final String _arg0, _arg1;
    final Syntax _body;
    T2 _targ0;
    T2 _targ1;
    Lambda2(String arg0, String arg1, Syntax body) { _arg0=arg0; _arg1 = arg1; _body=body; _targ0 = T2.tnew(); _targ1 = T2.tnew(); }
    @Override SB str(SB sb) { return _body.str(sb.p("{ ").p(_arg0).p(" ").p(_arg1).p(" -> ")).p(" }"); }
    @Override SB p1(SB sb) { return sb.p("{ ").p(_arg0).p(" ").p(_arg1).p(" -> ... } "); }
    @Override SB p2(SB sb, VBitSet dups) { return _body.p0(sb,dups); }
    T2 targ0() { T2 targ = _targ0.find(); return targ==_targ0 ? targ : (_targ0=targ); }
    T2 targ1() { T2 targ = _targ1.find(); return targ==_targ1 ? targ : (_targ1=targ); }
    @Override T2 hm(Ary<Syntax> work) {
      // The normal lambda work
      T2 fun = T2.fun(targ0(),targ1(),_body.find());
      // Force forwards progress; an Apply may already have lifted _t to
      // something better than just a plain fun wrapper.
      return find().unify(fun,work);
    }
    @Override void prep_tree( Syntax par, Ary<Syntax> work ) {
      prep_tree_impl(par,T2.tnew(),work);
      _body.prep_tree(this,work);
    }
    // If found name, inside a Lambda so NOT fresh
    @Override T2 prep_tree_lookup(String name, Syntax prior) {
      if( Util.eq(_arg0,name) ) return _targ0;
      if( Util.eq(_arg1,name) ) return _targ1;
      return null;
    }
    @Override boolean more_work(Ary<Syntax> work) {
      if( !more_work_impl(work) ) return false;
      return _body.more_work(work);
    }
    @Override void live(IBitSet visit) {
      if( _t!=null ) _t.live(visit);
      _targ0.live(visit);
      _targ1.live(visit);
      _body .live(visit);
    }
  }

  public static class Let extends Syntax {
    final String _arg0;
    final Syntax _body, _use;
    T2 _targ;
    Let(String arg0, Syntax body, Syntax use) { _arg0=arg0; _body=body; _use=use; _targ=T2.tnew(); }
    @Override SB str(SB sb) { return _use.str(_body.str(sb.p("let ").p(_arg0).p(" = ")).p(" in ")); }
    @Override SB p1(SB sb) { return sb.p("let ").p(_arg0).p(" = ... in ..."); }
    @Override SB p2(SB sb, VBitSet dups) { _body.p0(sb,dups); return _use.p0(sb,dups); }
    T2 targ() { T2 targ = _targ.find(); return targ==_targ ? targ : (_targ=targ); }
    @Override T2 hm(Ary<Syntax> work) {
      _use.find().push_update(this);
      targ().unify(_body.find(),work);
      return _use.find();
    }
    @Override void prep_tree( Syntax par, Ary<Syntax> work ) {
      prep_tree_impl(par,T2.tnew(),work);
      _body.prep_tree(this,work);
      _use .prep_tree(this,work);
    }
    @Override T2 prep_tree_lookup(String name, Syntax prior) {
      return Util.eq(_arg0,name)
        // Let _body, NOT fresh; Let _use, YES fresh
        ? (prior==_use ? T2.fresh(name,_targ) : _targ)
        : null;                 // Missed on name
    }

    @Override boolean more_work(Ary<Syntax> work) {
      if( !more_work_impl(work) ) return false;
      return _body.more_work(work) && _use.more_work(work);
    }
    @Override void live(IBitSet visit) {
      if( _t!=null ) _t.live(visit);
      _targ.live(visit);
      _body.live(visit);
      _use .live(visit);
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

    @Override T2 hm(Ary<Syntax> work) {
      T2 tfun = _fun.find();
      if( tfun.is_fresh() )
        tfun.get_fresh().push_update(this);
      T2[] targs = new T2[_args.length+1];
      for( int i=0; i<_args.length; i++ )
        targs[i] = _args[i].find();
      // if testing, allow progress on the last new result tvar....
      targs[_args.length] = Util.eq(tfun._name,"->") && work==null ? tfun.find(tfun._args.length-1) : T2.tnew(); // Return is new unconstrained T2
      T2 nfun = T2.fun(targs);
      T2 ufun = tfun.unify(nfun,work);
      if( _fun.find()!=tfun && work!=null ) work.push(_fun);
      // Return last element
      T2 trez = ufun.find(_args.length);
      // Force forward progress
      return trez.unify(find(),work);
    }
    @Override void prep_tree(Syntax par,Ary<Syntax> work) {
      prep_tree_impl(par,T2.tnew(),work);
      _fun.prep_tree(this,work);
      for( Syntax arg : _args ) arg.prep_tree(this,work);
    }
    @Override boolean more_work(Ary<Syntax> work) {
      if( !more_work_impl(work) ) return false;
      if( !_fun.more_work(work) ) return false;
      for( Syntax arg : _args ) if( !arg.more_work(work) ) return false;
      return true;
    }
    @Override void live(IBitSet visit) {
      if( _t!=null ) _t.live(visit);
      for( Syntax arg : _args ) arg.live(visit);
    }
  }

  // ---------------------------------------------------------------------
  // T2 types form a Lattice, with 'unify' same as 'meet'.  T2's form a DAG
  // (cycles if i allow recursive unification) with sharing.  Each Syntax has a
  // T2, and the forest of T2s can share.  Leaves of a T2 can be either a
  // simple concrete base type, or a sharable leaf.  Unify is structural, and
  // where not unifyable the union is replaced with an Error.
  public static class T2 {
    static void reset() { CNT=0; }
    private static int CNT=0;

    // Base constants are same as structural but using BASE.
    // Other names are structural, eg "->" or "pair".
    @NotNull final String _name; // name, eq "->" or "pair", or unique string for TVar leaves
    T2 @NotNull [] _args;
    final int _uid;
    // If set, this is a 'fresh' T2, which means it lazily clones during
    // unification such that it imparts its structure on the RHS but does not
    // itself change.  The args are length 1 with the U-F in slot0.
    String _fresh;
    // Base types carry a concrete Type
    Type _con;
    // Part of the incrementalization: if a fresh fcn type changes, any Applys
    // using it might update.
    Ary<Syntax> _updates;

    static T2 fun(T2... args) { return new T2("->",args); }
    static T2 tnew() { return new T2("V"+CNT,new T2[1]); }
    static T2 base(Type con) { T2 t = tnew(); t._con=con; return t; }
    static T2 prim(String name, T2... args) { return new T2(name,args); }
    static T2 fresh(String name, T2 t) {
      assert !t.is_fresh();
      T2 t2 = new T2(name,t); // Points to non-fresh
      t2._fresh=name;
      assert t2.is_fresh();
      return t2;
    }

    private T2(@NotNull String name, T2 @NotNull ... args) { _name = name; _args= args; _uid=CNT++; }

    // A fresh-able type var; a simple wrapper over another type var.
    boolean is_fresh() { assert _fresh==null || (_args.length==1 && _args[0]!=null); return _fresh!=null; }
    // A type var, not a concrete leaf.  Might be U-Fd or not.
    boolean is_leaf () { return _name.charAt(0)=='V' && !is_base(); }
    // Concrete primitive base
    boolean is_base () { return _con!=null; }
    // Is a structural type variable, neither is_leaf nor is_base
    boolean is_tvar() { return _name.charAt(0)!='V' && _con==null; }
    T2 get_fresh() {
      assert is_fresh();
      T2 fun = find(0);
      assert Util.eq(fun._name,"->");
      return fun;
    }

    void live(IBitSet visit) {
      if( visit.set(_uid) ) return;
      for( T2 t : _args ) if( t!=null ) t.live(visit);
    }

    // U-F find
    T2 find() {
      if( is_tvar() ) return this; // Shortcut
      T2 u = _args[0];
      if( u==null ) return this; // Shortcut
      if( u.no_uf() ) return u;  // Shortcut
      // U-F fixup
      while( !u.is_tvar() && u._args[0]!=null ) u = u._args[0];
      T2 v = this, v2;
      while( !v.is_tvar() && (v2=v._args[0])!=u ) { v._args[0]=u; v = v2; }
      return u;
    }
    // U-F find on the args array
    T2 find(int i) {
      T2 u = _args[i];
      T2 uu = u.find();
      return u==uu ? uu : (_args[i]=uu);
    }
    boolean no_uf() { return is_tvar() || _args[0]==null; }

    // U-F union; this becomes that.  If 'this' was used in an Apply, re-check
    // the Apply.
    T2 union(T2 that, Ary<Syntax> work) {
      assert _args[0]==null;    // Cannot union twice
      if( this==that ) return this;
      // Worklist: put updates on the worklist for revisiting
      if( work!=null ) work.addAll(_updates); // Re-Apply
      // Merge update lists, for future unions
      if( _updates != null ) {
        if( that._updates==null ) that._updates = _updates;
        else throw com.cliffc.aa.AA.unimpl();
      }
      return (_args[0] = that);
    }

    // Structural unification.  Both 'this' and t' are the same afterwards and
    // returns the unified bit.  If 'this' is 'fresh', it is cloned during
    // unification and unchanged, only imparting its sharing structure on 't'.
    T2 unify( T2 t, Ary<Syntax> work ) {
      if( this==t ) return this;
      assert no_uf() && t.no_uf();
      assert !t.is_fresh();     // Only can lazy-clone LHS
      if( is_fresh() )          // Peel off fresh lazy & do a fresh-unify
        return get_fresh()._fresh_unify(new HashMap<>(),t,work);
      // Normal unification, with side-effects
      assert DUPS.isEmpty();
      T2 rez = _unify(t,work);
      DUPS.clear();
      return rez;
    }

    // Structural unification.  Both 'this' and t' are the same afterwards and
    // returns the unified bit.
    static private final HashMap<Long,T2> DUPS = new HashMap<>();
    private T2 _unify(T2 t, Ary<Syntax> work) {
      assert no_uf() && t.no_uf();
      if( this==t ) return this;
      if(   is_fresh() ) throw com.cliffc.aa.AA.unimpl(); // recursive fresh?
      if( t.is_fresh() ) throw com.cliffc.aa.AA.unimpl(); // RHS is fresh?

      if( is_base() && t.is_base() ) return unify_base(t,work);
      // two leafs union in either order, so keep lower uid
      if( is_leaf() && t.is_leaf() && _uid<t._uid ) return t.union(this,work);
      if(   is_leaf() ) return   union(t   ,work);
      if( t.is_leaf() ) return t.union(this,work);

      if( !Util.eq(_name,t._name) )
        throw new RuntimeException("Cannot unify "+this+" and "+t);
      if( _args==t._args ) return this; // Names are equal, args are equal
      if( _args.length != t._args.length )
        throw new RuntimeException("Cannot unify "+this+" and "+t);

      // Cycle check.
      long luid = ((long)_uid<<32)|t._uid;
      T2 rez = DUPS.get(luid), rez2;
      if( rez!=null ) return rez; // Been there, done that
      T2[] args = new T2[_args.length];
      rez = rez2 = new T2(_name,args);
      DUPS.put(luid,rez);       // Close cycles

      // Structural recursion unification.
      for( int i=0; i<_args.length; i++ )
        args[i] = find(i)._unify(t.find(i),work);

      // Check for being equal, cyclic-ly, and return a prior if possible.
      boolean eq0 = rez.cycle_equals(this);
      boolean eq1 = rez.cycle_equals(t   );
      if( eq0 ) rez2 = this;
      if( eq1 ) rez2 = t   ;
      if( eq0 && eq1 ) rez2 = _uid < t._uid ? this : t;
      if( rez!=rez2 ) DUPS.put(luid,rez2);
      // Return new unified T2
      return rez2;
    }

    private T2 fresh_base(T2 t) { t._con = _con.meet(t._con); return t; }
    private T2 unify_base(T2 t, Ary<Syntax> work) { return union(fresh_base(t),work); }

    // Apply 'this' structure on 't'; no modifications to 'this'.
    // 'vars' maps from the cloned LHS to the RHS replacement.
    private T2 _fresh_unify( HashMap<T2, T2> vars, T2 t, Ary<Syntax> work ) {
      assert no_uf() && t.no_uf();
      assert this!=t || is_base(); // No overlap between LHS and RHS.
      T2 prior = vars.get(this);
      if( prior!=null )         // Been there, done that?  Return prior mapping
        return prior.find().unify(t,work);
      assert !is_fresh();       // recursive fresh?
      T2 rez = _fresh_unify_impl( vars, t, work );
      vars.put(this,rez);
      return rez;
    }

    private T2 _fresh_unify_impl( HashMap<T2, T2> vars, T2 t, Ary<Syntax> work ) {
      // RHS is also a lazy clone, which if cloned, will not be part of any
      // other structure.  When unioned with the clone of the LHS, the result
      // is not part of anything direct... but the structures still have to
      // align for the returned T2.  Make a replica & unify (e.g. stop being lazy).
      if( t.is_fresh() ) t = t.get_fresh().repl(vars, new HashMap<>());

      if( is_base() && t.is_base() ) return fresh_base(t);
      if(   is_leaf() ) return t;   // Lazy map LHS tvar to RHS
      if( t.is_leaf() ) return t.union(repl(vars, new HashMap<>()),work); // RHS is a tvar; union with a copy of LHS

      if( !Util.eq(_name,t._name) )
        throw com.cliffc.aa.AA.unimpl(); // unification error
      if( _args.length != t._args.length )
        throw new RuntimeException("Cannot unify "+this+" and "+t);
      // Structural recursion unification, lazy on LHS
      T2[] args = new T2[_args.length];
      for( int i=0; i<_args.length; i++ )
        args[i] = find(i)._fresh_unify(vars,t.find(i),work);

      return new T2(_name,args);
    }

    // Replicate LHS, replacing vars as they appear
    T2 repl(HashMap<T2,T2> vars, HashMap<T2,T2> dups) {
      assert no_uf() && !is_fresh();
      T2 t = vars.get(this);
      if( t!=null ) return t;   // Been there, done that, return prior answer
      T2 rez = _repl(vars,dups);
      vars.put(this,rez);
      return rez;
    }
    T2 _repl(HashMap<T2,T2> vars, HashMap<T2,T2> dups) {
      if( is_leaf() ) return tnew(); // LHS is a leaf, make a new one for RHS

      // Must replicate base's, because they are not really immutable:
      // mismatched Types meet instead of error.
      if( is_base() ) return base(_con);
      T2[] args = new T2[_args.length];
      T2 rez = new T2(_name,args);
      vars.put(this,rez); // Insert in dups BEFORE structural recursion, to stop cycles
      // Structural recursion replicate
      for( int i=0; i<_args.length; i++ )
        args[i] = find(i).repl(vars,dups);
      return rez;
    }

    // Structural unification, except return true if ever LHS progress
    boolean progress(T2 t) {
      assert no_uf() && t.no_uf();
      if( this==t ) return false;
      if( t.is_leaf() ) return false; // will be equal after unify
      if( is_base() && t.is_base() && _con==t._con ) return false;
      if( is_fresh() ) return get_fresh().progress(t);
      if( !Util.eq(_name,t._name) || _args.length!=t._args.length )
        return true;            // Blatantly not-equal
      for( int i=0; i<_args.length; i++ )
        if( find(i).progress(t.find(i)) )
          return true;          // Recursive progress
      return false;
    }

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
      if( !is_tvar() || !t.is_tvar() ||    // Base-cases have to be completely identical
          !Util.eq(_name,t._name) ||       // Wrong type-var names
          _args.length != t._args.length ) // Mismatched sizes
        return false;
      if( _args==t._args ) return true;
      // Cycles stall the equal/unequal decision until we see a difference.
      T2 tc = CDUPS.get(this);
      if( tc!=null )
        return tc==t; // Cycle check; true if both cycling the same
      CDUPS.put(this,t);
      for( int i=0; i<_args.length; i++ )
        if( !find(i)._cycle_equals(t.find(i)) )
          return false;
      return true;
    }

    // This is a T2 function that is the target of 'fresh', i.e., this function
    // might be fresh-unified with some other function.  Push the application
    // down the function parts; if any changes the fresh-application may make
    // progress.
    static final VBitSet UPDATE_VISIT  = new VBitSet();
    void push_update(Syntax a) { UPDATE_VISIT.clear(); push_update_impl(a); }
    private void push_update_impl(Syntax a) {
      assert no_uf();
      if( is_leaf() ) {
        if( _updates==null ) _updates = new Ary<>(Syntax.class);
        if( _updates.find(a)==-1 ) _updates.push(a);
      } else if( is_tvar() ) {
        if( UPDATE_VISIT.tset(_uid) ) return;
        for( int i=0; i<_args.length; i++ )
          find(i).push_update_impl(a);
      } else assert is_base();
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
      if( is_fresh() ) return _args[0].str(sb.p('#'),visit,dups);
      if( is_leaf() || is_base() ) {
        if( is_base() ) sb.p(_con instanceof TypeMemPtr ? "str" : _con.toString()); else sb.p(_name);
        return _args[0]==null ? sb : _args[0].str(sb.p(">>"), visit, dups);
      }
      boolean dup = dups.get(_uid);
      if( dup ) sb.p('$').p(_uid);
      if( visit.tset(_uid) && dup ) return sb;
      if( dup ) sb.p(':');

      if( _name.equals("->") ) {
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
      if( is_fresh() ) return get_fresh()._p(sb.p('#'),visit,dups);
      if( is_base() ) return sb.p(_con instanceof TypeMemPtr ? "str" : _con.toString() );
      if( is_leaf() ) return sb.p(_name);
      boolean dup = dups.get(_uid);
      if( dup ) sb.p('$').p(_uid);
      if( visit.tset(_uid) && dup ) return sb;
      if( dup ) sb.p(':');
      if( _name.equals("->") ) {
        sb.p("{ ");
        for( int i=0; i<_args.length-1; i++ )
          find(i)._p(sb,visit,dups).p(" ");
        return find(_args.length-1)._p(sb.p("-> "),visit,dups).p(" }");
      }
      // Generic structural T2
      sb.p("(").p(_name).p(" ");
      for( int i=0; i<_args.length; i++ ) find(i)._p(sb,visit,dups).p(" ");
      return sb.unchar().p(")");
    }
  }

}
