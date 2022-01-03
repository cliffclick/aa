package com.cliffc.aa.HM;

import com.cliffc.aa.type.*;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;

/** Hindley-Milner typing.  A Java clone from:
 * http://dysphoria.net/code/hindley-milner/HindleyMilner.scala
 * Andrew Forrest
 * Based heavily on Nikita Borisov's Perl implementation at
 * http://web.archive.org/web/20050420002559/www.cs.berkeley.edu/~nikitab/courses/cs263/hm.html
 * which in turn is based on the paper by Luca Cardelli at
 * http://lucacardelli.name/Papers/BasicTypechecking.pdf

 * Complete stand-alone, for my research.
 * MEETs base types, instead of declaring type error.
 * Does standard lexical scoping, which is not needed for SSA form.
 */
public class HM1 {
  public static HMType HM(Syntax prog) {
    HashMap<String,HMType> env = new HashMap<>();
    // Simple types
    HMVar bool  = new HMVar(TypeInt.BOOL);
    HMVar int64 = new HMVar(TypeInt.INT64);
    HMVar flt64 = new HMVar(TypeFlt.FLT64);
    HMVar strp  = null; //new HMVar(TypeMemPtr.STRPTR);

    // Primitives
    HMVar var1 = new HMVar();
    HMVar var2 = new HMVar();
    env.put("pair",Oper.fun(var1, Oper.fun(var2, new Oper("pair",var1,var2))));

    HMVar var3 = new HMVar();
    env.put("if/else" ,Oper.fun(bool,Oper.fun(var3,Oper.fun(var3,var3))));
    env.put("if/else3",Oper.fun(bool,         var3,         var3,var3  ));

    env.put("dec",Oper.fun(int64,int64));
    env.put("*"  ,Oper.fun(int64,Oper.fun(int64,int64)));
    env.put("*2" ,Oper.fun(int64,         int64,int64 ));
    env.put("==0",Oper.fun(int64,bool));

    // Convert integer to a string; int->str
    env.put("str",Oper.fun(int64,strp));
    // Floating point Factor; sorta like {div/mod}
    env.put("factor",Oper.fun(flt64,new Oper("pair",flt64,flt64)));

    return prog.hm(env, new HashSet<>());
  }
  static void reset() { HMVar.reset(); }


  public static abstract class Syntax {
    abstract HMType hm(HashMap<String,HMType> env, HashSet<HMVar> nongen);
  }
  public static class Con extends Syntax {
    final Type _t;
    Con(Type t) { _t=t; }
    @Override public String toString() { return _t.toString(); }
    @Override HMType hm(HashMap<String,HMType> env, HashSet<HMVar> nongen) {
      return new HMVar(_t);
    }
  }
  public static class Ident extends Syntax {
    final String _name;
    Ident(String name) { _name=name; }
    @Override public String toString() { return _name; }
    @Override HMType hm(HashMap<String,HMType> env, HashSet<HMVar> nongen) {
      HMType t = env.get(_name);
      if( t==null )
        throw new RuntimeException("Parse error, "+_name+" is undefined");
      HMType f = t.fresh(nongen);
      return f;
    }
  }
  
  public static class Lambda extends Syntax {
    final String _arg0;
    final Syntax _body;
    Lambda(String arg0, Syntax body) { _arg0=arg0; _body=body; }
    @Override public String toString() { return "{ "+_arg0+" -> "+_body+" }"; }
    @Override HMType hm(HashMap<String,HMType> env, HashSet<HMVar> nongen) {
      HMVar tnew = new HMVar();
      // Push _arg0->tnew into env & nongen, popping them off after doing body
      env.put(_arg0,tnew);
      nongen.add(tnew);
      HMType trez = _body.hm(env,nongen);
      nongen.remove(tnew);
      env.remove(_arg0);
      return Oper.fun(tnew,trez);
    }
  }

  public static class Lambda2 extends Syntax {
    final String _arg0, _arg1;
    final Syntax _body;
    Lambda2(String arg0, String arg1, Syntax body) { _arg0=arg0; _arg1=arg1; _body=body; }
    @Override public String toString() { return "{ "+_arg0+" "+_arg1+" -> "+_body+" }"; }
    @Override HMType hm(HashMap<String,HMType> env, HashSet<HMVar> nongen) {
      HMVar tnew0 = new HMVar();
      HMVar tnew1 = new HMVar();
      // Push _arg0->tnew0 into env & nongen, popping them off after doing body
      env.put(_arg0,tnew0);
      env.put(_arg1,tnew1);
      nongen.add(tnew0);
      nongen.add(tnew1);
      HMType trez = _body.hm(env,nongen);
      nongen.remove(tnew0);
      nongen.remove(tnew1);
      env.remove(_arg0);
      env.remove(_arg1);
      return Oper.fun(tnew0,tnew1,trez);
    }
  }

  public static class Let extends Syntax {
    final String _arg0;
    final Syntax _def, _body;
    Let(String arg0, Syntax def, Syntax body) { _arg0=arg0; _def=def; _body=body; }
    @Override public String toString() { return "let "+_arg0+" = "+_def+" in "+_body+" }"; }
    @Override HMType hm(HashMap<String,HMType> env, HashSet<HMVar> nongen) {
      HMVar tndef = new HMVar();
      // Push _arg0->tnew into env & nongen, popping them off after doing body
      env.put(_arg0,tndef);
      nongen.add(tndef);
      HMType tdef = _def.hm(env,nongen);
      nongen.remove(tndef);
      tndef.union(tdef);
      HMType trez = _body.hm(env,nongen);
      env.remove(_arg0);
      return trez;
    }
  }
  
  public static class Apply extends Syntax {
    final Syntax _fun;
    final Syntax[] _args;
    Apply(Syntax fun, Syntax... args) { _fun=fun; _args=args; }
    @Override public String toString() { return "("+_fun+" "+Arrays.deepToString(_args)+")"; }
    @Override HMType hm(HashMap<String,HMType> env, HashSet<HMVar> nongen) {
      HMType tfun = _fun.hm(env,nongen);

      HMType[] targs = new HMType[_args.length+1];
      for( int i=0; i<_args.length; i++ )
        targs[i] = _args[i].hm(env,nongen);
      HMType trez = targs[_args.length] = new HMVar();
      HMType nfun = Oper.fun(targs);
      nfun.union(tfun);
      return trez;
    }
  }



  public static abstract class HMType {
    HMType _u;                  // U-F; always null for Oper
    abstract HMType union(HMType t);
    abstract HMType find();
    @Override public final String toString() { return _str(new SB(),new VBitSet(),true).toString(); }
    public String str() { return _str(new SB(),new VBitSet(),false).toString(); }
    abstract SB _str(SB sb, VBitSet vbs, boolean debug);
    boolean is_top() { return _u==null; }

    HMType fresh(HashSet<HMVar> nongen) {
      HashMap<HMType,HMType> vars = new HashMap<>();
      return _fresh(nongen,vars);
    }
    HMType _fresh(HashSet<HMVar> nongen, HashMap<HMType,HMType> vars) {
      HMType t2 = find();
      if( t2 instanceof HMVar ) {
        return t2.occurs_in(nongen) //
          ? t2                      // Keep same var
          : vars.computeIfAbsent(t2, e -> new HMVar(((HMVar)t2)._t));
      } else {
        Oper op = (Oper)t2;
        HMType[] args = new HMType[op._args.length];
        for( int i=0; i<args.length; i++ )
          args[i] = op._args[i]._fresh(nongen,vars);
        return new Oper(op._name,args);
      }
    }

    boolean occurs_in(HashSet<HMVar>nongen) {
      for( HMVar x : nongen ) if( occurs_in_type(x) ) return true;
      return false;
    }
    boolean occurs_in(HMType[] args) {
      for( HMType x : args ) if( occurs_in_type(x) ) return true;
      return false;
    }
    boolean occurs_in_type(HMType v) {
      assert is_top();
      HMType y = v.find();
      if( y==this )
        return true;
      if( y instanceof Oper )
        return occurs_in(((Oper)y)._args);
      return false;
    }
  }

  static class HMVar extends HMType {
    private Type _t;
    private final int _uid;
    private static int CNT;
    HMVar() { this(Type.ANY); }
    HMVar(Type t) { _uid=CNT++; _t=t; }
    static void reset() { CNT=1; }
    public Type type() { assert is_top(); return _t; }
    @Override public SB _str(SB sb, VBitSet dups, boolean debug) {
      if( _u!=null && !debug ) return _u._str(sb,dups,debug);
      sb.p("v").p(_uid);
      if( dups.tset(_uid) ) return sb.p("$");
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
    @Override HMType union(HMType that) {
      if( _u!=null ) return find().union(that);
      if( that instanceof HMVar ) that = that.find();
      if( this==that ) return this; // Do nothing
      if( occurs_in_type(that) )
        throw new RuntimeException("recursive unification");

      if( that instanceof HMVar ) {
        HMVar v2 = (HMVar)that;
        v2._t = _t.meet(v2._t);
      }
      else assert _t==Type.ANY; // Else this var is un-MEETd with any Con
      return _u = that;         // Classic U-F union
    }
  }

  static class Oper extends HMType {
    final String _name;
    final HMType[] _args;
    Oper(String name, HMType... args) { _name=name; _args=args; }
    static Oper fun(HMType... args) { return new Oper("->",args); }
    @Override public SB _str(SB sb, VBitSet dups, boolean debug) {
      if( _name.equals("->") ) {
        sb.p("{ ");
        for( int i=0; i<_args.length-1; i++ )
          _args[i]._str(sb,dups,debug).p(" ");
        sb.p("-> ");
        _args[_args.length-1]._str(sb,dups,debug);
        return sb.p(" }");
      }
      sb.p(_name).p('(');
      for( HMType t : _args )
        t._str(sb,dups,debug).p(',');
      return sb.unchar().p(')');
    }

    @Override HMType find() { return this; }
    @Override HMType union(HMType that) {
      if( !(that instanceof Oper) ) return that.union(this);
      Oper op2 = (Oper)that;
      if( !_name.equals(op2._name) ||
          _args.length != op2._args.length )
        throw new RuntimeException("Cannot unify "+this+" and "+that);
      for( int i=0; i<_args.length; i++ )
        _args[i].union(op2._args[i]);
      return this;
    }
  }
}
