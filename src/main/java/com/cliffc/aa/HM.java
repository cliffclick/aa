package com.cliffc.aa;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeInt;
import com.cliffc.aa.util.SB;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;

// Hindley-Milner typing.
public class HM {
  // Forwards-walk all Nodes
  public static void HM(Node scope) {
    //scope.walk_hm(new VBitSet(),new HashSet<>());
  }
  public static HMType HM(Syntax prog) {

    HashMap<String,HMType> env = new HashMap<>();
    // Simple types
    HMBase bool  = new HMBase(TypeInt.BOOL);
    HMBase int64 = new HMBase(TypeInt.INT64);
    
    // Primitives
    HMVar var1 = new HMVar();
    HMVar var2 = new HMVar();
    env.put("pair",new HMFun(var1, new HMFun(var2, new Oper("pair",var1,var2))));
    
    HMVar var3 = new HMVar();
    env.put("if/else",new HMFun(bool,new HMFun(var3,new HMFun(var3,var3))));

    env.put("dec",new HMFun(int64,int64));
    env.put("*",new HMFun(int64,new HMFun(int64,int64)));
    env.put("==0",new HMFun(int64,bool));

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
      return new HMBase(_t);
    }
  }
  public static class Ident extends Syntax {
    final String _name;
    Ident(String name) { _name=name; }
    @Override public String toString() { return _name; }
    @Override HMType hm(HashMap<String,HMType> env, HashSet<HMVar> nongen) {
      HMType t = env.get(_name);
      if( t==null ) throw new RuntimeException("Parse error, "+_name+" is undefined");
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
      throw com.cliffc.aa.AA.unimpl();
    }
  }
  public static class Let extends Syntax {
    final String _arg0;
    final Syntax _def, _body;
    Let(String arg0, Syntax def, Syntax body) { _arg0=arg0; _def=def; _body=body; }
    @Override public String toString() { return "let "+_arg0+" = "+_def+" in "+_body+" }"; }
    @Override HMType hm(HashMap<String,HMType> env, HashSet<HMVar> nongen) {
      HMVar tndef = new HMVar();
      HashMap<String,HMType> newenv = new HashMap<>(env);
      newenv.put(_arg0,tndef);
      HashSet<HMVar> newgen = new HashSet<>(nongen);
      nongen.add(tndef);
      HMType tdef = _def.hm(newenv,newgen);
      tndef.union(tdef);
      HMType trez = _body.hm(newenv,nongen);
      return trez;
    }
  }
  public static class Apply extends Syntax {
    final Syntax _fun, _arg;
    Apply(Syntax fun, Syntax arg) { _fun=fun; _arg=arg; }
    @Override public String toString() { return "("+_fun+" "+_arg+")"; }
    @Override HMType hm(HashMap<String,HMType> env, HashSet<HMVar> nongen) {
      HMType tfun = _fun.hm(env,nongen);
      HMType targ = _arg.hm(env,nongen);
      HMType trez = new HMVar();
      HMType nfun = new HMFun(targ,trez);
      nfun.union(tfun);
      return trez;
    }
  }



  public static abstract class HMType {
    HMType _u;                  // U-F; always null for Oper
    abstract HMType union(HMType t);
    abstract HMType find();
    public String str() { return find()._str(); }
    abstract String _str();
    
    HMType fresh(HashSet<HMVar> nongen) {
      HashMap<HMVar,HMVar> vars = new HashMap<>();
      return _fresh(nongen,vars);
    }
    HMType _fresh(HashSet<HMVar> nongen, HashMap<HMVar,HMVar> vars) {
      HMType t2 = find();
      if( t2 instanceof HMVar ) {
        HMVar v2 = (HMVar)t2;
        return !occurs_in(v2,nongen)
          ? vars.getOrElseUpdate(t2, new HMVar())
          : t2;
      } else {
        Oper op = (Oper)t2;
        HMType[] args = new HMType[op._args.length];
        for( int i=0; i<args.length; i++ )
          args[i] = op._args[i]._fresh(nongen,vars);
        return new Oper(op._name,args);
      }
    }
  }

  private static class HMVar extends HMType {
    private final int _uid;
    private static int CNT;
    HMVar() { _uid=CNT++; }
    static void reset() { CNT=1; }
    @Override public String toString() { return "v"+_uid+((_u==null)? "" : ">>"+_u); }
    @Override public String _str() { return "v"+_uid; }
    
    @Override HMType find() {
      if( _u==null ) return this; // Top of union tree
      if( _u._u==null ) return _u; // One-step from top
      throw com.cliffc.aa.AA.unimpl();
    }
    @Override HMType union(HMType other) {
      if( _u!=null ) return find().union(other);
      //if( other instanceof HMVar ) other = ((HMVar)other).find();
      if( this==other )
        throw com.cliffc.aa.AA.unimpl(); // Do nothing
      // TODO: Occurs+_in check
      return _u = other;        // Classic U-F union
    }
  }

  static class Oper extends HMType {
    final String _name;
    final HMType[] _args;
    Oper(String name, HMType... args) { _name=name; _args=args; }
    @Override public String toString() { return _name+" "+Arrays.toString(_args); }
    @Override public String _str() {
      SB sb = new SB().p(_name).p('(');
      for( HMType t : _args )
        sb.p(t.str()).p(',');
      return sb.unchar().p(')').toString();
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
  static class HMFun extends Oper {
    HMFun(HMType arg, HMType ret) { super("->",arg,ret); }
    @Override public String toString() { return "{ "+_args[0]+" -> "+_args[1]+" }"; }
    @Override public String _str() {
      return "{ "+_args[0].str()+" -> "+_args[1].str()+" }";
    }
  }

  public static class HMBase extends Oper {
    private Type _t;
    public HMBase(Type t) { super("con"); _t = t; }
    Type type() { return _t; }
    public void meet(Type t) { _t=_t.meet(t); }
    @Override public String toString() { return _t.toString(); }
    @Override public String _str() { return _t.toString(); }
  }
}
