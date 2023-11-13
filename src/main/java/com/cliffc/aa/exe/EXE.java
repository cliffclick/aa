package com.cliffc.aa.exe;

import com.cliffc.aa.AA;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.IntSupplier;

import static com.cliffc.aa.AA.TODO;

public class EXE {
  public static void main( String[] args ) {
    if( args.length != 1 )
      throw TODO("More args?");
    run(args[0],0,true,true);
  }

  // Parse; Type; Run
  public static void run( String prog, int rseed, boolean do_hm, boolean do_gcp ) {
    Syntax root = parse(prog);
    root.do_hm();
    System.out.println("Type: "+root.tvar().str(new SB(),null,null,false,false));
    System.out.println("Eval: "+root.eval(new Ary<Type>(Type.class)));
  }

  static final HashMap<String,PrimSyn> PRIMSYNS = new HashMap<>(){{
      put("+",new Add());
      put("-",new Sub());
      put("*",new Mul());
    }};
  

  
  // ----------------- PARSER ---------------------
  private static int X;
  private static byte[] BUF;
  @Override public String toString() { return str(); }
  static String str() { return new String(BUF,X,BUF.length-X); }
  static Syntax parse( String sprog ) {
    X = 0;
    BUF = sprog.getBytes();
    Syntax prog = fterm();
    if( skipWS() != -1 ) throw AA.TODO("Junk at end of program: " + str());
    // Inject Root
    return new Root(prog);
  }

  // Parse a term
  static Syntax term() {
    if( skipWS()==-1 ) return null;
    if( isDigit(BUF[X]) ) return number();

    // Parse a Lambda
    if( peek('{') ) {           // Lambda 
      Ary<String> args = new Ary<>(new String[]{null,null,"$dsp"});
      while( !peek('-') ) args.push(id());
      require('>');
      return new Lambda(args.asAry(), require(fterm(),'}'));
    }

    if( peek('(') ) {           // Parse an Apply
      Syntax fun = fterm();
      Ary<Syntax> args = new Ary<>(new Syntax[1],0);
      while( !peek(')') ) args.push(fterm());
      return new Apply(fun, args.asAry());
    }

    if( peek("if") ) {          // Parse an If
      Syntax pred = require(fterm(),'?');
      Syntax t    = require(fterm(),':');
      Syntax f    =         fterm();
      return new If(pred,t,f);
    }

    // Let or Id
    if( isAlpha0(BUF[X]) ) {
      String id = id();
      if( peek('=') )
        // Let expression; "id = fterm(); term..."
        return new Let(id,require(fterm(),';'),fterm());
      PrimSyn prim = PRIMSYNS.get(id); // No shadowing primitives or this lookup returns the prim instead of the shadow
      return prim==null ? new Ident(id) : prim.make(); // Make a prim copy with fresh HM variables
    }

    throw AA.TODO();
  }
  
  // Parse a term with an optional following field.
  private static Syntax fterm() {
    Syntax term = term();
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
    if( s.isEmpty() ) throw AA.TODO("Missing id");
    if( Util.eq(s,"_") ) return null; // Field is inferred
    return s;
  }
  private static Syntax number() {
    if( BUF[X]=='0' && (BUF[X+1]!='.' || !isDigit(BUF[X+2])) )
      { X++; return new Con(TypeNil.NIL); }
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
  private static boolean isAlpha0(byte c) { return ('a'<=c && c <= 'z') || ('A'<=c && c <= 'Z') || (c=='_') || (c=='*') || (c=='?') || (c=='+') || (c=='-'); }
  private static boolean isAlpha1(byte c) { return isAlpha0(c) || ('0'<=c && c <= '9') || (c=='/'); }
  private static boolean peek(char c) { if( skipWS()!=c ) return false; X++; return true; }
  private static boolean peek(String s) {
    skipWS();
    for( int i=0; i<s.length(); i++ )
      if( BUF[X+i]!=(byte)s.charAt(i) )
        return false;
    X += s.length();
    return true;
  }

  private static void require(char c) { if( skipWS()!=c ) throw AA.TODO("Missing '"+c+"'"); X++; }
  private static Syntax require(Syntax t, char c) { require(c); return t; }
  private static Syntax require(String s, Syntax t) { for( byte c : s.getBytes() ) require((char)c); return t; }
  
  // ----------------- Syntax ---------------------
  static abstract class Syntax implements IntSupplier {
    private static int CNT=1;
    final int _uid=CNT++;
    @Override public int getAsInt() { return _uid; }
    
    Syntax _par;                // Parent in the AST

    TV3 _tvar;                  // Current HM type
    TV3 tvar() {                // U-F find
      TV3 t = _tvar.find();
      return t == _tvar ? t : (_tvar = t);
    }
    TV3 debug_find() { return _tvar.debug_find(); } // Find, without the roll-up

    // Dataflow types.  Varies during a run of GCP.
    Type _flow;

    // Visit whole tree recursively, applying 'map' to self, and reducing that
    // with the recursive value from all children.
    abstract <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce );
    
    // Print for debugger
    @Override final public String toString() { return str(new SB()).toString(); }
    abstract SB str(SB sb);

    // First pass
    abstract void prep_tree(Ary<TV3> nongen);

    // Compute HM type
    void do_hm() {
      prep_tree(new Ary<TV3>(TV3.class));
      visit( syn -> {
          if( syn.tvar() instanceof TVErr terr ) {
            System.err.println(terr);
            System.exit(1);
          }
          if( syn.tvar() instanceof TVBase base && base._t instanceof TypeNil tn && tn.getClass()==TypeNil.class ) {
            System.err.println("Mixing int and float");
            System.exit(1);
          }
          return null;
        },
        (a,b)->null);
      // TODO: Worklist based HM typing
    }

    abstract Type eval( Ary<Type> stk);
  }

  
  // --- Constant ------------------------
  static class Con extends Syntax {
    final Type _con;
    Con( Type con ) { _con = con; }
    @Override SB str(SB sb) { return _con.str(sb,false,false); }
    @Override void prep_tree(Ary<TV3> nongen) { _tvar = TV3.from_flow(_con); }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) { return map.apply(this); }
    @Override Type eval( Ary<Type> stk) { return _con; }
  }

  // --- Ident ------------------------
  // Lambda argument or Let def
  static class Ident extends Syntax {
    private final String _name;       // The identifier name

    private TV3[] _nongen;
    private Syntax _def; // Either Lambda, and _argn is the argument number OR Let, and fresh===(_argn!=0)
    private int _argn;
    
    Ident( String name ) { _name=name; }
    @Override SB str(SB sb) { return sb.p(_name); }
    @Override void prep_tree(Ary<TV3> nongen) {
      for( Syntax syn = _par, prior=this; syn!=null; prior=syn, syn = syn._par ) {
        _def = syn;
        switch( syn ) {
        case Lambda lam:
          _argn = Util.find(lam._args,_name);
          if( _argn != -1 ) {
            _tvar = lam.arg(_argn); // Take TVar from the lambda directly
            return;
          }
          break;
        case Let let:
          if( let._arg.equals(_name) ) {
            _argn = prior==let._body ? 1 : 0;
            _tvar = new TVLeaf();
            _nongen = nongen.asAry();
            TV3 def = let._def .tvar();
            if( _argn==1 ) def.fresh_unify(null,_tvar,_nongen,false);
            else           def.      unify(     _tvar        ,false);
            return;
          }
        default: break;
        }
      }
      throw AA.TODO("'"+_name+"' not found");
    }
    boolean fresh() { return _def instanceof Let && _argn==1; }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) { return map.apply(this); }
    @Override Type eval( Ary<Type> stk) {
      // Walk the eval stack, looking for our definition.
      int i=stk._len-1;
      while( true ) {
        if( stk.at(i) instanceof TypeFunPtr tfp ) {
          Lambda lam = Lambda.FUNS.at(tfp.fidx());
          if( lam==_def )       // Correct lambda
            return stk.at(i-1-(_argn-AA.ARG_IDX)); // All args got pushed, get the correct one
          i -= lam.nargs()-AA.ARG_IDX+1;
        } else {
          int lidx = (int)stk.at(i).getl();
          Let let = Let.LETS.at(lidx);
          if( let==_def )       // Correct Let
            return stk.at(i-1); // Pushed the one def, so its just behind
          i = i-2;
        }
      }
    }
  }

  // --- Field ------------------------
  static class Field extends Syntax {
    final String _id;
    final Syntax _ptr;
    Field( String id, Syntax ptr ) { _ptr = ptr; ptr._par = this; _id=id; }
    @Override SB str(SB sb) { return _ptr.str(sb).p(".").p(_id); }
    @Override void prep_tree(Ary<TV3> nongen) {
      _tvar = new TVLeaf();
      _ptr.prep_tree(nongen);
      throw AA.TODO();
    }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      return reduce.apply(map.apply(this),_ptr.visit(map,reduce));
    }
    @Override Type eval( Ary<Type> stk) { throw AA.TODO(); }
  }

  // --- Lambda ------------------------
  static class Lambda extends Syntax {
    static final Ary<Lambda> FUNS = new Ary<>(Lambda.class);
    final Syntax _body;
    final String[] _args;       // Argument names
    final int _fidx;
    
    Lambda(String[] args, Syntax body ) {
      _body = body;  if( body!=null ) body._par = this;
      _args = args;
      _fidx = BitsFun.new_fidx();
      FUNS.setX(_fidx,this);
    }
    @Override SB str(SB sb) {
      sb.p("{ ");
      for( int i=AA.ARG_IDX; i< nargs(); i++ )
        sb.p(_args[i]).p(' ');
      return _body.str(sb.p("-> ")).p(" }");
    }
    int nargs() { return _args.length; }
    TV3 arg(int i) { return tvar().arg(i); }
    @Override void prep_tree(Ary<TV3> nongen) {
      _tvar = new TVLambda(nargs(),new TVLeaf(),new TVLeaf());
      // Extend the nongen set by the new variables
      for( int i=0; i<nargs(); i++ ) nongen.push(arg(i));
      // Prep the body
      _body.prep_tree(nongen);
      // Pop nongen stack
      nongen.pop(nargs());
      // TVLambda ret is made early, unify with body now
      tvar().as_lambda().ret().unify(_body.tvar(),false);
    }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      return reduce.apply(map.apply(this),_body.visit(map,reduce));
    }
    @Override Type eval( Ary<Type> stk) {
      Type rez = _body.tvar().as_flow(null);
      return TypeFunPtr.make(_fidx,nargs(),Type.ALL,rez);
    }    
    Type apply( Ary<Type> stk) { return _body.eval(stk); }
  }

  // --- Apply ------------------------
  static class Apply extends Syntax {
    final Syntax _fun;
    final Syntax[] _args;
    Apply( Syntax fun, Syntax[] args ) {
      _fun = fun;  fun._par = this;
      _args=args;
      for( Syntax arg : args ) arg._par = this;
    }
    @Override SB str(SB sb) {
      _fun.str(sb.p("(")).p(" ");
      for( Syntax arg : _args )
        arg.str(sb).p(" ");
      return sb.unchar().p(")");
    }
    int nargs() { return _args.length; }
    TVLambda fun() { return (TVLambda)_fun.tvar(); }
    @Override void prep_tree(Ary<TV3> nongen) {
      _tvar = new TVLeaf();
      _fun.prep_tree(nongen);
      for( Syntax arg : _args ) arg.prep_tree(nongen);

      TVLambda lam = fun();
      if( lam.nargs() != nargs()+AA.ARG_IDX ) throw AA.TODO("Expected "+(lam.nargs()-AA.ARG_IDX)+" args, found "+nargs()+" args");
      for( int i=0; i<nargs(); i++ )
        lam.arg(i+AA.ARG_IDX).unify(_args[i].tvar(),false);
      tvar().unify(lam.ret(),false);      
    }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      T slf = map.apply(this);
      T rez = reduce.apply(slf,_fun.visit(map,reduce));
      for( Syntax arg : _args )
        rez = reduce.apply(rez,arg.visit(map,reduce));
      return rez;
    }
    @Override Type eval( Ary<Type> stk) {
      // Eval the function
      TypeFunPtr tfp = (TypeFunPtr)_fun.eval(stk);
      // Eval and record the arguments
      Type[] args = Types.get(nargs());
      for( int i=0; i<nargs(); i++ )
        args[i] = _args[i].eval(stk);
      // Push args and function on the eval stack
      for( int i=nargs()-1; i>=0; i-- )
        stk.push(args[i]);
      stk.push(tfp);
      // Eval the body, in the context of the args
      Type rez = Lambda.FUNS.at(tfp.fidx()).apply(stk);
      // Pop the eval stack
      stk.pop(nargs()+1);
      return rez;
    }
  }

  // --- If ------------------------
  static class If extends Syntax {
    final Syntax _pred,_t,_f;
    If( Syntax pred, Syntax t, Syntax f ) {
      _pred = pred; pred._par = this;
      _t = t; t._par = this;
      _f = f; f._par = this;
    }
    @Override SB str(SB sb) {
      sb.p("if ");
      _pred.str(sb).p(" ? ");
      _t.str(sb).p(" : ");
      return _f.str(sb);
    }
    @Override void prep_tree(Ary<TV3> nongen) {
      _tvar = new TVLeaf();
      _pred.prep_tree(nongen);
      _t.prep_tree(nongen);
      _f.prep_tree(nongen);
      tvar().unify(_t.tvar(),false);
      tvar().unify(_f.tvar(),false);
    }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      T slf = map.apply(this), rez;
      rez = reduce.apply(slf,_pred.visit(map,reduce));
      rez = reduce.apply(rez,_t   .visit(map,reduce));
      rez = reduce.apply(rez,_f   .visit(map,reduce));
      return rez;
    }
    @Override Type eval( Ary<Type> stk) {
      Type pred = _pred.eval(stk);
      Syntax syn = pred==TypeNil.NIL || pred==TypeInt.ZERO ? _f : _t;
      return syn.eval(stk);
    }
  }
  
  // --- Let ------------------------
  static class Let extends Syntax {
    final Syntax _def, _body;
    final String _arg;       // Argument name
    static final Ary<Let> LETS = new Ary<Let>(Let.class);
    
    Let(String arg, Syntax def, Syntax body ) {
      _def  = def;  def ._par = this;
      _body = body; body._par = this;
      _arg  = arg;
      LETS.setX(_uid,this);
    }
    @Override SB str(SB sb) { return _body.str(_def.str(sb.p(_arg).p(" = ")).p("; ")); }
    @Override void prep_tree(Ary<TV3> nongen) {
      _tvar = new TVLeaf();
      TVLeaf def = new TVLeaf();
      nongen.push(def);
      _def  .prep_tree(nongen);
      nongen.pop(1);
      def   .unify(_def .tvar(),false); // Unify def with _def._tvar
      _body .prep_tree(nongen);
      tvar().unify(_body.tvar(),false); // Unify 'Let._tvar' with the '_body._tvar'
    }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      T rez = map.apply(this);
      T def = reduce.apply(rez,_def .visit(map,reduce));
      return  reduce.apply(def,_body.visit(map,reduce));
    }
    @Override Type eval( Ary<Type> stk) {
      stk.push(_def.eval(stk));
      stk.push(TypeInt.con(_uid));
      Type rez = _body.eval(stk);
      stk.pop();
      return rez;
    }    
  }


  // --- Root ------------------------
  static class Root extends Syntax {
    final Syntax _prog;
    Root( Syntax prog ) { _prog=prog;  prog._par = this; }
    @Override SB str( SB sb ) { return _prog.str(sb.p("Root ")); }
    @Override void prep_tree(Ary<TV3> nongen) {
      _prog.prep_tree(nongen);
      _tvar = _prog.tvar();
    }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      return reduce.apply(map.apply(this),_prog.visit(map,reduce));
    }
    @Override Type eval(Ary<Type> stk) { return _prog.eval(stk); }
  }

  // --- PrimSyn ------------------------
  abstract static class PrimSyn extends Lambda {
    static final String[][] IDS = new String[][] {
      {},
      {"x"},
      {"x","y"},
      {"x","y","z"},
    };
    static final Type[] TS = new Type[10];
    static TV3 INT64() { return TVBase.make(TypeInt.INT64); }
    
    final TV3[] _tvs;
    PrimSyn(TV3... tvs) {
      super(IDS[tvs.length-1],null);
      _tvs = tvs;
    }
    abstract PrimSyn make();
    TV3 tret() { return _tvs[_tvs.length-1]; }
    @Override void prep_tree(Ary<TV3> nongen) {
      TVLambda lam = new TVLambda(nargs()+AA.ARG_IDX,null,tret());
      for( int i=0; i<nargs(); i++ )
        lam.arg(AA.ARG_IDX+i).unify(_tvs[i],false);
      _tvar = lam;
    }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) { return map.apply(this);  }
    @Override Type eval( Ary<Type> stk) {
      return TypeFunPtr.make(_fidx,nargs(),Type.ALL,Type.ALL);
    }    
    @Override Type apply( Ary<Type> stk ) {
      for( int i=0; i<nargs(); i++ )
        TS[i] = stk.at(stk._len-2-i);
      return op();
    }
    abstract Type op();
  }

  // add integers
  static class Add extends PrimSyn {
    public Add() { super(INT64(), INT64(), INT64()); }
    @Override PrimSyn make() { return new Add(); }
    @Override SB str(SB sb) { return sb.p("+"); }
    @Override Type op() { return TypeInt.con(TS[0].getl()+TS[1].getl()); }
  }

  // sub integers
  static class Sub extends PrimSyn {
    public Sub() { super(INT64(), INT64(), INT64()); }
    @Override PrimSyn make() { return new Sub(); }
    @Override SB str(SB sb) { return sb.p("-"); }
    @Override Type op() { return TypeInt.con(TS[0].getl()-TS[1].getl()); }
  }

  // mul integers
  static class Mul extends PrimSyn {
    public Mul() { super(INT64(), INT64(), INT64()); }
    @Override PrimSyn make() { return new Mul(); }
    @Override SB str(SB sb) { return sb.p("*"); }
    @Override Type op() { return TypeInt.con(TS[0].getl()*TS[1].getl()); }
  }

}
