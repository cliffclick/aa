package com.cliffc.aa.HM;

import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;
import org.jetbrains.annotations.NotNull;

import java.util.*;

/**
 * Hindley-Milner typing.  Complete stand-alone, for research.  MEETs base
 * types, instead of declaring type error.  Requires SSA renumbering; uses a
 * global Env instead locally tracking.
 * Testing in this version changing out the AST tree-walk for a worklist based
 * approach, where unification happens in any order.  In particular, it means
 * that (unlike a tree-walk), function types will get used before the function
 * is typed.  This means that a "fresh" copy of a function type to be used to
 * unify against will not have all the contraints at first unification.
 * (0) Build the AST with parent pointers also, and declare the AST a "graph".
 * Break the HM() call into a "makes progress" test and a "do it".
 * (1) Find all ids (which are all unique ala SSA), and keep a stack of the
 * non-generative ones at each Ident.  Leaf AST on the worklist.  Check for
 * missing-name syntax.  Requires 1 tree pass.
 * (2) Put root on worklist.
 * (3) Pull from worklist until empty:
 * (4)   Call hm() to get a HMType or null.
 * (6)   If progress (not null)
 * (7)   Then set new HMType, and put graph neighbors on worklist
 * (8) Report HMTypes.
 */
public class HM3 {
  static final HashMap<String,HMType> ENV = new HashMap<>();

  public static HMType hm( Syntax prog) {
    // Simple types
    HMVar bool  = new HMVar(TypeInt.BOOL);
    HMVar int64 = new HMVar(TypeInt.INT64);
    HMVar flt64 = new HMVar(TypeFlt.FLT64);
    HMVar strp  = new HMVar(TypeMemPtr.STRPTR);

    // Primitives
    HMVar var1 = new HMVar();
    HMVar var2 = new HMVar();
    ENV.put("pair",Oper.fun(var1, Oper.fun(var2, new Oper("pair",var1,var2))));

    // { pred:bool lhs:var3 rhs:var3 -> var3 }
    HMVar var3 = new HMVar();
    ENV.put("if/else",Oper.fun(bool,Oper.fun(var3,Oper.fun(var3,var3))));

    ENV.put("dec",Oper.fun(int64,int64));
    ENV.put("*",Oper.fun(int64,Oper.fun(int64,int64)));
    ENV.put("==0",Oper.fun(int64,bool));

    // Print a string; int->str
    ENV.put("str",Oper.fun(int64,strp));
    // Factor
    ENV.put("factor",Oper.fun(flt64,new Oper("pair",flt64,flt64)));


    // Prep for SSA: pre-gather all the (unique) ids.  Store a linked-list of
    // non-generative IDs (those mid-definition in Lambda & Let, or in the old
    // "nongen" HashSet), for use by Ident.hm.
    final Worklist work = new Worklist();
    prog.get_ids(null,work);

    // Worklist:
    int cnt=0;
    while( work.len()>0 ) {     // While not empty
      Syntax s = work.pop();    // Get work
      HMType nnn = s.hm(work);
      if( nnn!=null ) {             // If progress
        s._hm = nnn;                // Move progress state
        s.add_neighbors(work);      // Neighbors get reinspected for progress
      }
      assert prog.check_progress(work); // Everything that can make progress is on the worklist
      cnt++;                            // Which iter count, for debug only
    }
    return prog._hm;
  }
  static void reset() { ENV.clear(); HMType.reset(); }

  // Small classic tree of HMVars, immutable, with sharing at the root parts.
  static class VStack implements Iterable<HMVar> {
    final VStack _par;
    final HMVar _nongen;
    VStack( VStack par, HMVar nongen ) { _par=par; _nongen=nongen; }
    @Override public String toString() { return str(new SB()).toString(); }
    SB str(SB sb) {
      _nongen._str(sb,new VBitSet(),false);
      if( _par!=null ) _par.str(sb.p(" >> "));
      return sb;
    }
    @NotNull @Override public Iterator<HMVar> iterator() { return new Iter(); }
    private class Iter implements Iterator<HMVar> {
      private VStack _vstk;
      Iter() { _vstk=VStack.this; }
      @Override public boolean hasNext() { return _vstk!=null; }
      @Override public HMVar next() { HMVar v = _vstk._nongen; _vstk = _vstk._par;  return v; }
    }
  }

  // Worklist of Syntax nodes
  private static class Worklist {
    private final Ary<Syntax> _ary = new Ary<>(Syntax.class); // For picking random element
    private final HashSet<Syntax> _work = new HashSet<>();    // For preventing dups
    public int len() { return _ary.len(); }
    public void push(Syntax s) { if( !_work.contains(s) ) _work.add(_ary.push(s)); }
    public Syntax pop() { Syntax s = _ary.pop(); _work.remove(s); return s; }
    public boolean has(Syntax s) { return _work.contains(s); }
    public void addAll(Ary<? extends Syntax> ss) { for( Syntax s : ss ) push(s); }
    @Override public String toString() { return _ary.toString(); }
  }

  // Program Abstract Syntax Tree
  static abstract class Syntax {
    Syntax _par;                // Parent in the AST.
    Syntax[] _kids;             // Children in the AST.
    HMType _hm;                 // The Hindley-Milner type
    // Find the H-M type for this node, strictly by looking at the children H-M
    // type and adding any constraints.
    abstract HMType hm(Worklist work); // Hindley-Milner effect for this AST node
    // Prep call: gather unique IDs and find/set the non-gen IDs for this AST
    // node and subtree.
    abstract void get_ids(VStack vstk, Worklist work);
    // Add self to the worklist, IFF kids have already computed an initial H-M type.
    protected final void add_work(Worklist work) {  if( all_kids_ready() ) work.push(this);  }
    // Add neighbors (kids, parent) and NOT self to the worklist.
    final void add_neighbors(Worklist work) {
      if( _par!=null ) _par.add_work(work);
      if( _kids!=null )
        for( Syntax kid : _kids )
          kid.add_work(work);
    }
    // Child classes inspect their kids
    final boolean all_kids_ready() {
      if( _kids==null ) return true;
      for( Syntax kid : _kids ) if( kid._hm==null ) return false;
      return true;
    }
    // Progress if _hm is not null, and a call to hm() either returns something
    // not 'eq' to _hm or unifies with anything.
    abstract boolean progress();
    // Check that every node which can make progress is on the worklist
    boolean check_progress(Worklist work) {
      if( all_kids_ready() ) // If kids are not ready, then cannot compute hm() so not on worklist
        if( _hm==null || progress() ) // Progress is possible
          if( !work.has(this) )       // Not on worklist?
            return false;             // Fails check
      if( _kids!=null )               // For all kids
        for( Syntax kid : _kids )
          if( !kid.check_progress(work) ) // Recursively check nodes that can make progress on worklist
            return false;
      return true;
    }
  }
  public static class Con extends Syntax {
    final Type _t;
    Con(Type t) { _t=t; }
    @Override public String toString() { return _t.toString(); }
    @Override HMType hm(Worklist work) { return _hm==null ? new HMVar(_t) : null; }
    @Override boolean progress() { return false; }
    @Override void get_ids(VStack vstk,Worklist work) { add_work(work); }
  }

  public static class Ident extends Syntax {
    final String _name;
    VStack _vstk;
    Ident(String name) { _name=name; }
    @Override public String toString() { return _name; }
    @Override HMType hm(Worklist work) {
      if( _hm!=null ) return null;
      HMType t = ENV.get(_name).find();
      return t.fresh(_vstk);
    }
    // Progress if named HMType unioned into, and thus both put on the worklist
    // and has its _hm field cleared to signal a need for a fresh() copy.
    @Override boolean progress() { return false; }
    @Override void get_ids(VStack vstk,Worklist work) {
      HMType t = ENV.get(_name);
      if( t==null )
        throw new RuntimeException("Parse error, "+_name+" is undefined");
      if( t._ids==null ) t._ids = new Ary<>(Ident.class);
      t._ids.push(this);
      _vstk=vstk;
      add_work(work);
    }
  }
  
  public static class Lambda extends Syntax {
    final String _arg0;
    Lambda(String arg0, Syntax body) { _kids=new Syntax[]{body}; body._par=this; _arg0=arg0; }
    private Syntax body() { return _kids[0]; }
    @Override public String toString() { return "{ "+_arg0+" -> "+body()+" }"; }
    @Override HMType hm(Worklist work) {
      if( _hm!=null && !progress() ) return null;
      HMType tnew = ENV.get(_arg0).find();
      HMType trez = body()._hm.find();
      return Oper.fun(tnew,trez);
    }
    @Override boolean progress() {
      HMType tnew = ENV.get(_arg0).find();
      HMType trez = body()._hm.find();
      // Progress if _hm is NOT a Oper.fun, OR
      // !_hm[0].eq(tnew) || _hm[1].eq(trez);
      if( !(_hm instanceof Oper) ) return true;
      if( !((Oper)_hm)._name.equals("->") ) return true;
      HMType fcn = ((Oper)_hm)._args[0].find();
      HMType rez = ((Oper)_hm)._args[1].find();
      return !fcn.eq(tnew) || !rez.eq(trez);
    }
    @Override void get_ids(VStack vstk,Worklist work) {
      HMVar var = new HMVar();
      ENV.put(_arg0, var);
      body().get_ids(new VStack(vstk,var),work);
    }
  }
  public static class Let extends Syntax {
    final String _arg0;
    Let(String arg0, Syntax body, Syntax use) { _arg0=arg0; _kids=new Syntax[]{body,use}; body._par=use._par=this; }
    private Syntax body() { return _kids[0]; }
    private Syntax use () { return _kids[1]; }
    @Override public String toString() { return "let "+_arg0+" = "+body()+" in "+use()+" }"; }
    @Override HMType hm(Worklist work) {
      if( _hm!=null && !progress() ) return null;
      HMType tbody = body()._hm.find();
      HMType trez  = use() ._hm.find();
      HMType tnew  = ENV.get(_arg0).find();
      tnew.union(tbody,work);
      if( _hm!=null ) _hm.union(trez,work);
      return trez;
    }
    @Override boolean progress() {
      HMType tbody = body()._hm.find();
      HMType trez  = use() ._hm.find();
      HMType tnew = ENV.get(_arg0).find();
      // Progress if tnew != tbody (they get unioned) OR
      // trez != _hm
      return !tnew.eq(tbody) || !_hm.find().eq(trez);
    }
    @Override void get_ids(VStack vstk,Worklist work) {
      HMVar var = new HMVar();
      ENV.put(_arg0, var);
      body().get_ids(new VStack(vstk,var),work);
      use() .get_ids(vstk,work);
    }
  }
  public static class Apply extends Syntax {
    Apply(Syntax fun, Syntax arg) { _kids=new Syntax[]{fun,arg}; fun._par=arg._par=this; }
    private Syntax fun() { return _kids[0]; }
    private Syntax arg() { return _kids[1]; }
    @Override public String toString() { return "("+fun()+" "+arg()+")"; }
    @Override HMType hm(Worklist work) {
      if( _hm!=null && !progress() ) return null;
      HMType tfun = fun()._hm.find();
      HMType targ = arg()._hm.find();
      HMType trez = new HMVar();
      HMType nfun = Oper.fun(targ,trez);
      nfun.union(tfun,work);
      if( _hm!=null ) _hm.union(trez.find(),work);
      return trez.find();
    }
    @Override boolean progress() {
      // Progress if tfun is not a Oper.fun, OR
      // tfun[0] != targ (they get unioned)
      HMType tfun = fun()._hm.find();
      HMType targ = arg()._hm.find();
      if( !(tfun instanceof Oper) ) return true;
      if( !((Oper)tfun)._name.equals("->") ) return true;
      HMType arg0 = ((Oper)tfun)._args[0].find();
      return !arg0.eq(targ);
    }
    @Override void get_ids(VStack vstk,Worklist work) { fun().get_ids(vstk,work); arg().get_ids(vstk,work); }
  }



  public static abstract class HMType {
    HMType _u;                  // U-F; always null for Oper
    final int _uid;
    private static int CNT;
    static void reset() { CNT=1; }
    HMType() { _uid=CNT++; }
    Ary<Ident> _ids;            // Progress for IDs when types change
    abstract HMType union(HMType t, Worklist work);
    abstract HMType find();
    @Override public final String toString() { return _str(new SB(),new VBitSet(),true).toString(); }
    public String str() { return _str(new SB(),new VBitSet(),false).toString(); }
    abstract SB _str(SB sb, VBitSet vbs, boolean debug);
    boolean is_top() { return _u==null; }
    static final HashMap<HMVar,HMVar> EQS = new HashMap<>();
    final boolean eq( HMType v ) { EQS.clear(); return find()._eq(v, new BitSetSparse()); }
    abstract boolean _eq( HMType v, BitSetSparse dups );

    HMType fresh(VStack vstk) {
      HashMap<HMVar,HMVar> vars = new HashMap<>();
      HashMap<Oper,Oper> opers = new HashMap<>();
      return find()._fresh(vstk,vars,opers);
    }
    abstract HMType _fresh(VStack vstk, HashMap<HMVar,HMVar> vars, HashMap<Oper,Oper> opers);

    boolean occurs_in(VStack vstk, VBitSet dups) {
      if( vstk==null ) return false;
      for( HMVar x : vstk ) if( occurs_in_type(x,dups) ) return true;
      return false;
    }
    boolean occurs_in(HMType[] args, VBitSet dups) {
      for( HMType x : args ) if( occurs_in_type(x,dups) ) return true;
      return false;
    }
    boolean occurs_in_type(HMType v, VBitSet dups) {
      assert is_top();
      if( dups.tset(v._uid) )
        return false;           // Been there, done that
      HMType y = v.find();      // Find top
      if( y==this )             // Occurs in type?
        return true;            // Yup, occurs in type right here
      if( y instanceof Oper )   // Structural recursive test
        return occurs_in(((Oper)y)._args,dups);
      return false;
    }
  }

  static class HMVar extends HMType {
    private Type _t;
    HMVar() { this(Type.ANY); }
    HMVar(Type t) { _t=t; }
    public Type type() { assert is_top(); return _t; }
    @Override public SB _str(SB sb, VBitSet dups, boolean debug) {
      if( _u!=null && !debug ) return _u._str(sb,dups,debug); // Clean print; skip to U-F root & print
      sb.p("v").p(_uid);
      if( dups.tset(_uid) ) return sb.p("$");  // Stop infinite print loops
      if( _t!=Type.ANY ) _t.str(sb.p(":"),dups,null,false);
      if( _u!=null ) _u._str(sb.p(">>"),dups,debug);
      return sb;
     }

    @Override HMType find() {
      HMType u = _u;
      if( u==null ) return this; // Top of union tree
      if( u._u==null ) return u; // One-step from top
      // Classic U-F rollup
      while( u._u!=null ) u = u._u; // Find the top
      HMType x = this;              // Collapse all to top
      while( x._u!=u ) { HMType tmp = x._u; x._u=u; x=tmp;}
      return u;
    }
    @Override HMType union(HMType that, Worklist work) {
      if( _u!=null ) return find().union(that,work);
      if( that instanceof HMVar ) that = that.find();
      if( this==that ) return this; // Do nothing
      if( occurs_in_type(that, new VBitSet()) )
        //throw new RuntimeException("recursive unification");
        System.out.println("recursive unification");

      if( that instanceof HMVar ) {
        HMVar v2 = (HMVar)that;
        // Order, so keep smaller _uids by default
        if( _uid < v2._uid ) return that.union(this,work);
        v2._t = _t.meet(v2._t); // Lattice MEET instead of unification failure
      }
      else if( _t!=Type.ANY )   // Else this var is un-MEETd with any Con
        throw new RuntimeException("Cannot unify "+this+" and "+that);
      if( _ids!=null ) {        // Move this ids into that ids
        if( that._ids==null ) that._ids = _ids;
        else that._ids.addAll(_ids);
        _ids=null;              // No longer here
      }
      if( that._ids!=null ) {   // All that ids onto worklist
        for( Ident id : that._ids ) id._hm=null; // Flag as 1-shot re-freshen
        work.addAll(that._ids); // On to worklist
      }
      return _u = that;         // Classic U-F union this into that.
    }

    @Override boolean _eq( HMType v, BitSetSparse dups ) {
      if( this==v ) return true;
      if( v==null ) return false;
      HMType v2 = v.find();
      if( !(v2 instanceof HMVar) ) return false;
      assert _u==null && v2._u==null;
      if( _t != ((HMVar)v2)._t) return false;
      HMVar v3 = EQS.computeIfAbsent(this,k -> (HMVar)v2);
      return v2 == v3;
    }

    @Override HMType _fresh(VStack vstk, HashMap<HMVar,HMVar> vars, HashMap<Oper,Oper> opers) {
      assert is_top();
      return occurs_in(vstk, new VBitSet()) // If in the lexical Stack
        ? this                      // Keep same var
        : vars.computeIfAbsent(this, e -> new HMVar(_t));
    }
  }

  static class Oper extends HMType {
    final String _name;
    final HMType[] _args;
    Oper(String name, HMType... args) { _name=name; _args=args; }
    static Oper fun(HMType... args) { return new Oper("->",args); }
    @Override public SB _str(SB sb, VBitSet dups, boolean debug) {
      if( dups.tset(_uid) ) return sb.p("v").p(_uid).p("$");  // Stop infinite print loops
      if( _name.equals("->") ) {
        if( debug ) sb.p("v").p(_uid).p(":");
        sb.p("{ ");
        _args[0]._str(sb,dups,debug);
        sb.p(" -> ");
        _args[1]._str(sb,dups,debug);
        return sb.p(" }");
      }
      sb.p(_name);
      if( debug ) sb.p(_uid);
      sb.p('(');
      for( HMType t : _args )
        t._str(sb,dups,debug).p(',');
      return sb.unchar().p(')');
    }

    @Override HMType find() { return this; }
    @Override HMType union(HMType that, Worklist work) {
      if( this==that ) return this;
      if( !(that instanceof Oper) ) return that.union(this,work);
      if( _uid < that._uid ) return that.union(this,work); // Minimize unique CNT values
      Oper op2 = (Oper)that;
      if( !_name.equals(op2._name) ||
          _args.length != op2._args.length )
        throw new RuntimeException("Cannot unify "+this+" and "+that);
      for( int i=0; i<_args.length; i++ )
        _args[i] = _args[i].union(op2._args[i],work); // Both union, and update U-F
      if(      _ids!=null ) { for( Ident id :      _ids ) id._hm=null;  work.addAll(     _ids); }
      if( that._ids!=null ) { for( Ident id : that._ids ) id._hm=null;  work.addAll(that._ids); }
      return that;
    }
    @Override boolean _eq( HMType v, BitSetSparse dups ) {
      assert is_top() && v.is_top();
      if( this==v ) return true;
      if( !(v instanceof Oper) ) return false;
      if( dups.tset(_uid,v._uid) )
        return true; // Checked already, something else has to be equal/unequal
      Oper o = (Oper)v;
      if( !_name.equals(o._name) ||
          _args.length!=o._args.length ) return false;
      for( int i=0; i<_args.length; i++ ) {
        HMType h0 =   _args[i];
        HMType h1 = o._args[i];
        if( !h0.is_top() )   _args[i] = h0 = h0.find();
        if( !h1.is_top() ) o._args[i] = h1 = h1.find();
        if( !h0._eq(h1,dups) )
          return false;
      }
      return true;
    }
    @Override HMType _fresh(VStack vstk, HashMap<HMVar,HMVar> vars, HashMap<Oper,Oper> opers) {
      assert is_top();
      Oper op = opers.get(this);
      if( op!=null ) return op;
      HMType[] args = new HMType[_args.length];
      op = new Oper(_name,args);
      opers.put(this,op);       // Stop cyclic structure endless looping
      for( int i=0; i<_args.length; i++ )
        args[i] = _args[i].find()._fresh(vstk,vars,opers);
      return op;
    }

  }
}
