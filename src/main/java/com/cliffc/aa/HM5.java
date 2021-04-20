package com.cliffc.aa;

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

// Lazily computes 'Fresh' copies instead of eagerly.

public class HM5 {
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
    int cnt_syns = prog.prep_tree(null,null,work);
    int init_T2s = T2.CNT;

    int cnt=0, DEBUG_CNT=-1;
    while( work.len()>0 ) {     // While work
      int oldcnt = T2.CNT;      // Used for cost-check when no-progress
      Syntax syn = work.pop();  // Get work
      T2 old = syn._t;          // Old value for progress assert
      if( cnt==DEBUG_CNT )
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
      cnt++;
    }
    assert prog.more_work(work);

    //System.out.println("Initial T2s: "+init_T2s+", Prog size: "+cnt_syns+", worklist iters: "+cnt+", T2s: "+T2.CNT);
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
    //public Syntax pop() { Syntax s = _ary.pop();_cnt++;            _work.remove(s); return s; }
    public Syntax pop() { Syntax s = _ary.del(  _cnt++%_ary._len); _work.remove(s); return s; }
    public boolean has(Syntax s) { return _work.contains(s); }
    public void addAll(Ary<? extends Syntax> ss) { if( ss != null ) for( Syntax s : ss ) push(s); }
    @Override public String toString() { return _ary.toString(); }
  }

  // Small classic tree of T2s, immutable, with sharing at the root parts.
  static class VStack implements Iterable<T2> {
    final VStack _par;
    final T2 _nongen;
    VStack( VStack par, T2 nongen ) { _par=par; _nongen=nongen; }
    @Override public String toString() { return str(new SB()).toString(); }
    SB str(SB sb) {
      _nongen.str(sb,new VBitSet(),new VBitSet());
      if( _par!=null ) _par.str(sb.p(" >> "));
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

  public static abstract class Syntax {
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
      return work.has(this) || !hm(null); // Either on worklist, or no-progress
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
    @Override boolean hm(Worklist work) { assert find().isa("Base"); return false; }
    @Override T2 lookup(String name) { throw unimpl("should not reach here"); }
    @Override void add_kids(Worklist work) { }
    @Override int prep_tree( Syntax par, VStack nongen, Worklist work ) { prep_tree_impl(par, nongen, work, T2.make_base(_con)); return 1; }
    @Override void prep_lookup_deps(Ident id) { throw unimpl("should not reach here"); }
    @Override boolean more_work(Worklist work) { return more_work_impl(work); }
  }

  public static class Ident extends Syntax {
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
      return t.fresh_unify(find(),_nongen,work);
    }
    @Override T2 lookup(String name) { throw unimpl("should not reach here"); }
    @Override void add_kids(Worklist work) { }
    @Override void add_occurs(Worklist work) {
      T2 t = _par==null ? null : _par.lookup(_name); // Lookup in current env
      if( t==null ) t = PRIMS.get(_name);            // Lookup in prims
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

  public static class Lambda extends Syntax {
    final String _arg0;
    final Syntax _body;
    T2 _targ;
    Lambda(String arg0, Syntax body) { _arg0=arg0; _body=body; _targ = T2.make_leaf(); }
    @Override SB str(SB sb) { return _body.str(sb.p("{ ").p(_arg0).p(" -> ")).p(" }"); }
    @Override SB p1(SB sb) { return sb.p("{ ").p(_arg0).p(" -> ... } "); }
    @Override SB p2(SB sb, VBitSet dups) { return _body.p0(sb,dups); }
    T2 targ() { T2 targ = _targ.find(); return targ==_targ ? targ : (_targ=targ); }
    @Override boolean hm(Worklist work) {
      // The normal lambda work
      T2 old = find();
      if( old.is_fun() &&       // Already a function?  Compare-by-parts
          !old.args(0).unify(targ()      ,work) &&
          !old.args(1).unify(_body.find(),work) )
        return false;
      // Make a new T2 for progress
      T2 fun = T2.make_fun(targ(),_body.find());
      return old.unify(fun,work);
    }
    @Override T2 lookup(String name) {
      if( Util.eq(_arg0,name) ) return targ();
      return _par==null ? null : _par.lookup(name);
    }
    @Override void add_kids(Worklist work) { work.push(_body); }
    @Override void add_occurs(Worklist work) {
      if( targ().occurs_in_type(find()) ) work.addAll(_targ._deps);
    }
    @Override int prep_tree( Syntax par, VStack nongen, Worklist work ) {
      prep_tree_impl(par,nongen,work,T2.make_leaf());
      return _body.prep_tree(this,new VStack(nongen,_targ),work) + 1;
    }
    @Override void prep_lookup_deps(Ident id) {
      if( Util.eq(id._name,_arg0) ) _targ.push_update(id);
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
    @Override boolean hm(Worklist work) {
      // The normal lambda work
      T2 old = find();
      if(  old.is_fun() &&      // Already a function?  Compare-by-parts
          !old.args(0).unify(targ0()     ,work) &&
          !old.args(1).unify(targ1()     ,work) &&
          !old.args(2).unify(_body.find(),work) )
        return false;
      // Make a new T2 for progress
      T2 fun = T2.make_fun(targ0(),targ1(),_body.find());
      return old.unify(fun,work);
    }
    @Override T2 lookup(String name) {
      if( Util.eq(_arg0,name) ) return targ0();
      if( Util.eq(_arg1,name) ) return targ1();
      return _par==null ? null : _par.lookup(name);
    }
    @Override void add_kids(Worklist work) { work.push(_body); }
    @Override void add_occurs(Worklist work) {
      if( targ0().occurs_in_type(find()) ) work.addAll(_targ0._deps);
      if( targ1().occurs_in_type(find()) ) work.addAll(_targ1._deps);
    }
    @Override int prep_tree( Syntax par, VStack nongen, Worklist work ) {
      prep_tree_impl(par,nongen,work,T2.make_leaf());
      VStack vs0 = new VStack(nongen,_targ0);
      VStack vs1 = new VStack(vs0   ,_targ1);
      return _body.prep_tree(this,vs1,work) + 1;
    }
    @Override void prep_lookup_deps(Ident id) {
      if( Util.eq(id._name,_arg0) ) _targ0.push_update(id);
      if( Util.eq(id._name,_arg1) ) _targ1.push_update(id);
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
    @Override boolean hm(Worklist work) {
      return targ().unify(_def.find(),work);
    }
    @Override T2 lookup(String name) {
      if( Util.eq(_arg0,name) ) return targ();
      return _par==null ? null : _par.lookup(name);
    }
    @Override void add_kids(Worklist work) { work.push(_body); work.push(_def); }
    @Override void add_occurs(Worklist work) {
      if( targ().occurs_in_type(find()) ) work.addAll(_targ._deps);
    }
    @Override int prep_tree( Syntax par, VStack nongen, Worklist work ) {
      prep_tree_impl(par,nongen,work,_body._t);
      int cnt = _body.prep_tree(this,           nongen       ,work) +
                _def .prep_tree(this,new VStack(nongen,_targ),work);
      _t = _body._t;            // Unify 'Let._t' with the '_body'
      return cnt;
    }
    @Override void prep_lookup_deps(Ident id) {
      if( Util.eq(id._name,_arg0) ) _targ.push_update(id);
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

    @Override boolean hm(Worklist work) {
      // Unifiying these: make_fun(this.arg0 this.arg1 -> new     )
      //                      _fun{_fun.arg0 _fun.arg1 -> _fun.rez}
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
        tfun.unify(nfun,work);
        return true;        // Always progress (since forcing tfun to be a fun)
      }

      if( tfun._args.length != _args.length+1 )
        throw new RuntimeException("Mismatched argument lengths");
      // Check for progress amongst arg pairs
      boolean progress = false;
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
      int cnt = _fun.prep_tree(this,nongen,work);
      for( Syntax arg : _args ) cnt += arg.prep_tree(this,nongen,work);
      return cnt;
    }
    @Override void prep_lookup_deps(Ident id) { }
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
    final @NotNull String _name; // name, e.g. "->" or "pair" or "V123" or "base"

    // Structural parts to unify with, or slot 0 is used during normal U-F
    T2 @NotNull [] _args;

    // Base types carry a concrete Type
    Type _con;

    // Dependent (non-local) tvars to revisit
    Ary<Ident> _deps;


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
    boolean is_leaf() { return _name.charAt(0)=='V' || (isa("Base") && _con==null); }
    boolean no_uf() { return !is_leaf() || _args[0]==null; }
    boolean isa(String name) { return Util.eq(_name,name); }
    boolean is_base() { return isa("Base") && _con!=null; }
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
    boolean union(T2 that, Worklist work) {
      assert is_leaf() && no_uf(); // Cannot union twice
      if( this==that ) return false;
      if( work==null ) return true; // Report progress without changing
      // Worklist: put updates on the worklist for revisiting
      if( _deps != null ) {
        work.addAll(_deps); // Re-Apply
        // Merge update lists, for future unions
        if( that._deps==null && that.is_leaf() ) that._deps = _deps;
        else
          for( Ident dep : _deps ) that.push_update(dep);
        _deps = null;
      }
      _args[0] = that;         // U-F update
      return true;
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
    // and 'that' are the same afterwards.  Sets PROGRESS.
    private boolean _unify(T2 that, Worklist work) {
      assert no_uf() && that.no_uf();
      if( this==that ) return false;

      // two leafs union in either order, so keep lower uid
      if( is_leaf() && that.is_leaf() && _uid<that._uid ) return that.union(this,work);
      if(      is_leaf() ) return      union(that,work);
      if( that.is_leaf() ) return that.union(this,work);
      if( is_base() && that.is_base() ) return unify_base(that,work);

      if( !Util.eq(_name,that._name) )
        throw new RuntimeException("Cannot unify "+this+" and "+that);
      assert _args!=that._args; // Not expecting to share _args and not 'this'
      if( _args.length != that._args.length )
        throw new RuntimeException("Cannot unify "+this+" and "+that);

      // Cycle check
      long luid = dbl_uid(that);
      T2 rez = DUPS.get(luid);
      assert rez==null || rez==that;
      if( rez!=null ) return false; // Been there, done that
      DUPS.put(luid,that);          // Close cycles

      // Structural recursion unification.
      boolean progress=false;
      for( int i=0; i<_args.length; i++ ) {
        progress |= args(i)._unify(that.args(i),work);
        if( progress && work!=null ) return true;
      }
      return progress;
    }

    private long dbl_uid(T2 t) { return ((long)_uid<<32)|t._uid; }

    private boolean unify_base(T2 that, Worklist work) {
      fresh_base(that,work);
      if( work==null ) return true;
      _args = new T2[1];        // Room for a forwarding pointer
      _con=null;                // Flip from 'Base' to 'Leaf'
      return union(that,work);
    }
    private boolean fresh_base(T2 that, Worklist work) {
      Type con = _con.meet(that._con);
      if( con==that._con ) return false; // No progress
      if( work!=null ) that._con = con;  // Yes progress, but no update if null work
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

      if( !Util.eq(_name,that._name) ||
          _args.length != that._args.length )
        throw new RuntimeException("Cannot unify "+this+" and "+that);

      // Structural recursion unification, lazy on LHS
      boolean progress = vput(that,false); // Early set, to stop cycles
      for( int i=0; i<_args.length; i++ ) {
        progress |= args(i)._fresh_unify(that.args(i),nongen,work);
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
    boolean push_update(Ident a) { assert UPDATE_VISIT.isEmpty(); push_update_impl(a); UPDATE_VISIT.clear(); return true; }
    private void push_update_impl(Ident a) {
      assert no_uf();
      if( is_leaf() || _args.length==0 ) {
        if( _deps==null ) _deps = new Ary<>(Ident.class);
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

    static void reset() { CNT=0; DUPS.clear(); VARS.clear(); ODUPS.clear(); CDUPS.clear(); UPDATE_VISIT.clear(); }
  }

}
