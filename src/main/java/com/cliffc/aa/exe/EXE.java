package com.cliffc.aa.exe;

import com.cliffc.aa.AA;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.HashMap;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.IntSupplier;

public class EXE {
  public static void reset() { KontVal.reset(); }
  public static void main( String[] args ) throws IOException {
    for( String arg : args ) {
      String prog = new String( Files.readAllBytes( Paths.get(arg)));
      run(prog,0,true,true);
    }
  }

  public static Root compile( String prog, int rseed, boolean do_hm, boolean do_gcp ) {
    reset();
    return parse(prog).do_hm();
  }

  // Parse; Type; Run
  public static void run( String prog, int rseed, boolean do_hm, boolean do_gcp ) {
    Root root = compile(prog,rseed,do_hm,do_gcp);
    System.out.println("Type: "+root.tvar().str(new SB(),null,null,false,false));
    System.out.println("Eval: "+root.eval(null));
  }

  static final HashMap<String,PrimSyn> PRIMSYNS = new HashMap<>(){{
      put("+",new Add());
      put("-",new Sub());
      put("*",new Mul());
      put("/",new Div());
      put("f+",new FAdd());
      put("pair",new Pair());
    }};
  

  
  // ----------------- PARSER ---------------------
  private static int X;
  private static byte[] BUF;
  @Override public String toString() { return str(); }
  static String str() { return new String(BUF,X,BUF.length-X); }
  static Root parse( String sprog ) {
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

    // Parse an Apply
    if( peek('(') ) {
      Syntax fun = fterm();
      Ary<Syntax> args = new Ary<>(new Syntax[1],0);
      while( !peek(')') ) args.push(fterm());
      return new Apply(fun, args.asAry());
    }

    // Parse an If
    if( peek("if") ) {
      Syntax pred = require(fterm(),'?');
      Syntax t    = require(fterm(),':');
      Syntax f    =         fterm();
      return new If(pred,t,f);
    }

    // Parse a struct
    if( peek("@{") ) {
      Struct str = new Struct();
      Ary<String> labs = new Ary<>(new String[1],0);
      Ary<Syntax> flds = new Ary<>(new Syntax[1],0);
      while( !peek("}") ) str.add(require(id(),'='),require(fterm(),';'));
      return str;      
    }
    
    // Let or Id
    if( isAlpha0(BUF[X]) || isOp(BUF[X]) ) {
      String id = id(isOp(BUF[X]));
      if( peek('=') )
        // Let expression; "id = fterm(); term..."
        return new Let(id,require(fterm(),';'),fterm());
      if( id.equals("nil") ) return new Nil();
      PrimSyn prim = PRIMSYNS.get(id); // No shadowing primitives or this lookup returns the prim instead of the shadow
      return prim==null ? new Ident(id) : prim.make(); // Make a prim copy with fresh HM variables
    }

    throw AA.TODO();
  }
  
  // Parse a term with an optional following field.
  private static Syntax fterm() {
    Syntax term = term();
    while( true ) {
      if( term==null || !peek('.') ) return term;
      String id = id();
      term = id==null ? new DynField(term) : new Field(id(),term);
    }
  }
  
  private static final SB ID = new SB();
  private static String id() { return id(false); }
  private static String id( boolean op ) {
    ID.clear();
    skipWS();
    while( X<BUF.length && ( isOp(BUF[X]) || isAlpha1(BUF[X])) )
      ID.p((char)BUF[X++]);
    String s = ID.toString().intern();
    if( s.isEmpty() ) throw AA.TODO("Missing id");
    if( Util.eq(s,"_") ) return null; // Field is inferred
    return s;
  }
  private static Syntax number() {
    int sum=0;
    while( X<BUF.length && isDigit(BUF[X]) )
      sum = sum*10+BUF[X++]-'0';
    if( X>= BUF.length || BUF[X]!='.' )
      return new Con(sum);
    // Ambiguous '.' in: 2.3 vs 2.x (field load from a number)
    if( X+1<BUF.length && isAlpha0(BUF[X+1]) )
      return new Con(sum);
    X++;
    double f = (double)sum;
    f = f + (BUF[X++]-'0')/10.0f;
    require('f');
    return new Con(f);
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
  private static boolean isOp    (byte c) { return "*?+-/".indexOf(c)>=0; }
  private static boolean isAlpha0(byte c) { return ('a'<=c && c <= 'z') || ('A'<=c && c <= 'Z') || (c=='_'); }
  private static boolean isAlpha1(byte c) { return isAlpha0(c) || ('0'<=c && c <= '9'); }
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
  private static String require(String s, char c) { require(c); return s; }
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

    // SEK style evaluation machine.
    // Env is a linked list, with a Val (for Let) or a set of Vals (for Lambda).
    // A Val is either an Int, or a Kontinuation; K has a Lambda and an Env.
    abstract Val eval( Env e );
  }

  
  // --- Constant ------------------------
  static class Con extends Syntax {
    final Val _con;
    Con( int   con ) { _con = new IntVal(con); }
    Con( double con ) { _con = new FltVal(con); }
    @Override SB str(SB sb) { return _con.str(sb,null); }
    @Override void prep_tree(Ary<TV3> nongen) { _tvar = TV3.from_flow(_con.as_flow()); }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) { return map.apply(this); }
    @Override Val eval( Env e ) { return _con; }
  }

  // --- Nil ------------------------
  static class Nil extends Syntax {
    @Override SB str(SB sb) { return sb.p("nil"); }
    @Override void prep_tree(Ary<TV3> nongen) { _tvar = new TVStruct(true); _tvar.add_may_nil(false); }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) { return map.apply(this); }
    @Override NilVal eval( Env e ) { return NilVal.NIL; }
  }

  // --- Ident ------------------------
  // Lambda argument or Let def
  static class Ident extends Syntax {
    private final String _name;       // The identifier name

    private int _dbidx;  // deBrujin index
    private int _argn;   // Arg index for Lambda, 0 for Let
    
    Ident( String name ) { _name=name; }
    @Override SB str(SB sb) { return sb.p(_name); }
    @Override void prep_tree(Ary<TV3> nongen) {
      int dbx = 0;
      boolean was_apply=false;
      for( Syntax syn = _par, prior=this; syn!=null; prior=syn, syn = syn._par ) {
        if( syn instanceof Lambda lam ) {
          if( (_argn=Util.find(lam._args,_name)) != -1 )
            // Take TVar from the lambda directly; and zero-bias the arg index
            {  init(lam.arg(_argn),dbx, _argn-AA.ARG_IDX);  return; }
          dbx++;                // Bump deBrujin index
          was_apply = false;
        } else if( syn instanceof Let let ) {
          if( let._arg.equals(_name) ) {
            boolean fresh = prior==let._body;
            if( was_apply && !fresh )
              throw new IllegalArgumentException("Cyclic reference to "+_name);
            init(fresh ? let._def.tvar().fresh(nongen.asAry()) : let._def.tvar(),dbx,0);
            return;
          }
          dbx++;                // Bump deBrujin index
        } else if( syn instanceof Apply apl ) {
          was_apply = true;
        }
      }
      throw AA.TODO("'"+_name+"' not found");
    }
    private void init( TV3 tv, int dbx, int argn ) { _tvar=tv; _dbidx=dbx; _argn=argn; }
    
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) { return map.apply(this); }
    @Override Val eval( Env e ) {
      Env e0=e;
      for( int i=0; i<_dbidx; i++ )
        e0 = e0._e;               // Index env via deBrujin index
      if( _argn==0 ) return e0._v0;
      if( _argn==1 ) return e0._v1;
      if( _argn==2 ) return e0._v2;
      throw AA.TODO();
    }
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
      _tvar = new TVLambda(nargs(),null,new TVLeaf());
      // Extend the nongen set by the new variables
      for( int i=AA.ARG_IDX; i<nargs(); i++ ) nongen.push(arg(i));
      // Prep the body
      _body.prep_tree(nongen);
      // Pop nongen stack
      nongen.pop(nargs()-AA.ARG_IDX);
      // TVLambda ret is made early, unify with body now
      tvar().as_lambda().ret().unify(_body.tvar(),false);
    }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      return reduce.apply(map.apply(this),_body.visit(map,reduce));
    }
    @Override KontVal eval( Env e ) { return new KontVal(e,this);  }    
    Val apply( Env e ) { return _body.eval(e); }
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
    @Override void prep_tree(Ary<TV3> nongen) {
      _tvar = new TVLeaf();
      _fun.prep_tree(nongen);
      for( Syntax arg : _args ) arg.prep_tree(nongen);

      TVLambda lam = new TVLambda(nargs()+AA.ARG_IDX,null,tvar());
      _fun.tvar().unify(lam,false);
      lam = lam.find().as_lambda();
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
    @Override Val eval( Env e ) {
      // Eval the function
      KontVal fun = _fun.eval(e).as_kont();
      Val a0=null, a1=null, a2=null;
      if( nargs() > 0 ) {
        a0 = _args[0].eval(e);
        if( nargs() > 1 ) {
          a1 = _args[1].eval(e);
          if( nargs() > 2 ) {
            throw AA.TODO();
          }
        }
      }
      e = new Env(fun._e,a0,a1,a2);
      // Eval the body, in the context the closure, extended by the args
      return fun._lam.apply(e);
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

      // pred is a simple constant?  Unify one side
      int cmp=0;
      if( _pred.tvar() instanceof TVBase base && base._t instanceof TypeNil tn ) {
        if( tn._nil ) { cmp= -1; assert !tn._sub; }
        if( tn._sub )   cmp=  1;
        if( tn==TypeInt.ZERO || tn==TypeFlt.ZERO ) cmp = -1;
      }
      // TODO: Cannot do NIL mixing withup up-cast of not-nil after IF
      //// Structs are ptrs in EXE for now
      //if( _pred.tvar() instanceof TVStruct s ) {
      //  // TVStruct version of a nil-TVPtr
      //  if(  s.may_nil() && s.len()==0 && s.is_open()  ) cmp= -1;
      //  // Not-nil struct is always true
      //  if( !s.may_nil() ) cmp=1;
      //}
      // Unify both sides
      if( cmp >= 0 ) tvar().unify(_t.tvar(),false);
      if( cmp <= 0 ) tvar().unify(_f.tvar(),false);
    }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      T slf = map.apply(this), rez;
      rez = reduce.apply(slf,_pred.visit(map,reduce));
      rez = reduce.apply(rez,_t   .visit(map,reduce));
      rez = reduce.apply(rez,_f   .visit(map,reduce));
      return rez;
    }
    @Override Val eval( Env e ) {
      Val pred = _pred.eval(e);
      boolean t = switch( pred ) {
      case IntVal II -> II._con!=0;
      case FltVal FF -> FF._con!=0;
      case StructVal s -> true;
      case NilVal n -> false;
      default -> throw AA.TODO();
      };
      Syntax syn = t ? _t : _f;
      return syn.eval(e);
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
    @Override Val eval( Env e ) {
      Env e0 = new Env(e,null); // Premature push: no def yet, so null
      Val def = _def.eval(e0);  // Eval def
      e0._v0 = def;             // Close the cycle
      if( def instanceof KontVal k ) 
        k._e = e0;              // Let Rec
      return _body.eval(e0);
    }    
  }

  // --- Struct ------------------------
  static class Struct extends Syntax {
    final Ary<String> _labels;
    final Ary<Syntax> _flds;
    Struct( ) { _labels = new Ary<>(String.class); _flds = new Ary<>(Syntax.class); }
    void add( String label, Syntax fld ) { _labels.push(label); _flds.push(fld); fld._par = this; }
    @Override SB str(SB sb) {
      sb.p("@{ ");
      for( int i=0; i<_flds._len; i++ )
        _flds.at(i).str(sb.p(_labels.at(i)).p(" = ")).p("; ");
      return sb.unchar(1).p("}");
    }
    @Override void prep_tree(Ary<TV3> nongen) {
      TVStruct str = new TVStruct(_labels);
      _tvar = str;
      for( int i=0; i<_flds._len; i++ ) {
        _flds.at(i).prep_tree(nongen);
        str.arg(i).unify(_flds.at(i).tvar(),false);
      }
    }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      T rez = map.apply(this);
      for( Syntax fld : _flds )
        rez = reduce.apply(rez,fld.visit(map,reduce));
      return rez;
    }
    @Override StructVal eval( Env e ) {
      StructVal s = new StructVal();      
      for( int i=0; i<_flds._len; i++ )
        s.add(_labels.at(i),_flds.at(i).eval(e));
      return s;
    }
  }

  // --- Field ------------------------
  static class Field extends Syntax {
    final String _lab;
    final Syntax _ptr;
    Field( String id, Syntax ptr ) { _ptr = ptr; ptr._par = this; _lab=id; }
    @Override SB str(SB sb) { return _ptr.str(sb).p(".").p(_lab); }
    @Override void prep_tree(Ary<TV3> nongen) {
      _tvar = new TVLeaf();
      _ptr.prep_tree(nongen);
      TVStruct s = new TVStruct(new String[]{_lab},new TV3[]{_tvar},true);
      // TODO: Cannot add use_nil without the full up-cast of not-nil after IF
      //s.add_use_nil();
      _ptr.tvar().unify(s,false);
      if( !(_ptr.tvar() instanceof TVStruct str && str.idx(_lab)>=0) )
        throw new IllegalArgumentException("Missing field '"+_lab+"'");
    }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      return reduce.apply(map.apply(this),_ptr.visit(map,reduce));
    }
    @Override Val eval( Env e ) { return _ptr.eval(e).as_struct().at(_lab); }
  }


  // --- DynField ------------------------
  static class DynField extends Syntax {
    final Syntax _ptr;
    DynField(Syntax ptr ) { _ptr = ptr; ptr._par = this; }
    @Override SB str(SB sb) { return _ptr.str(sb).p("._"); }
    @Override void prep_tree(Ary<TV3> nongen) {
      _tvar = new TVLeaf();
      _ptr.prep_tree(nongen);
      TVStruct s = new TVStruct(new String[]{},new TV3[]{},true);
      _ptr.tvar().unify(s,false);
    }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      return reduce.apply(map.apply(this),_ptr.visit(map,reduce));
    }
    @Override Val eval( Env e ) {
      //return _ptr.eval(e).as_struct().at(_lab);
      throw AA.TODO();
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
    @Override Val eval( Env e ) { return _prog.eval(e); }

    // Compute HM type
    Root do_hm() {
      prep_tree(new Ary<>(TV3.class));
      // Check for simple type errors
      visit( syn -> {
          if( syn.tvar() instanceof TVErr terr )
            throw new IllegalArgumentException(terr.toString());
          if( syn.tvar() instanceof TVBase base && base._t instanceof TypeNil tn && tn.getClass()==TypeNil.class ) {
            System.err.println("Mixing int and double");
            System.exit(1);
          }
          return null;
        },
        (a,b)->null);
      // TODO: Worklist based HM typing
      return this;
    }
  }

  // --- PrimSyn ------------------------
  abstract static class PrimSyn extends Lambda {
    static final String[][] IDS = new String[][] {
      {},
      {"0"},
      {"0","1"},
      {"0","1","2"},
    };
    static final Type[] TS = new Type[10];
    static TV3 INT64() { return TVBase.make(TypeInt.INT64); }
    static TV3 FLT64() { return TVBase.make(TypeFlt.FLT64); }
    
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
    @Override Val apply( Env e ) {
      if( e._v0.as_int()!=null ) 
        return new IntVal(iop(e._v0.as_int()._con,e._v1.as_int()._con));
      if( e._v0.as_flt()!=null ) 
        return new FltVal(dop(e._v0.as_flt()._con,e._v1.as_flt()._con));
      throw AA.TODO();
    }
    int    iop(int    x, int    y) { throw AA.TODO(); }
    double dop(double x, double y) { throw AA.TODO(); }
  }

  // add integers
  static class Add extends PrimSyn {
    public Add() { super(INT64(), INT64(), INT64()); }
    @Override PrimSyn make() { return new Add(); }
    @Override SB str(SB sb) { return sb.p("+"); }
    @Override int iop(int x, int y) { return x+y; }
  }

  // sub integers
  static class Sub extends PrimSyn {
    public Sub() { super(INT64(), INT64(), INT64()); }
    @Override PrimSyn make() { return new Sub(); }
    @Override SB str(SB sb) { return sb.p("-"); }
    @Override int iop(int x, int y) { return x-y; }
  }

  // mul integers
  static class Mul extends PrimSyn {
    public Mul() { super(INT64(), INT64(), INT64()); }
    @Override PrimSyn make() { return new Mul(); }
    @Override SB str(SB sb) { return sb.p("*"); }
    @Override int iop(int x, int y) { return x*y; }
  }

  // div integers
  static class Div extends PrimSyn {
    public Div() { super(INT64(), INT64(), INT64()); }
    @Override PrimSyn make() { return new Div(); }
    @Override SB str(SB sb) { return sb.p("/"); }
    @Override int iop(int x, int y) { return x/y; }
  }

  // add doubles
  static class FAdd extends PrimSyn {
    public FAdd() { super(FLT64(), FLT64(), FLT64()); }
    @Override PrimSyn make() { return new FAdd(); }
    @Override SB str(SB sb) { return sb.p("f+"); }
    @Override double dop(double x, double y) { return x+y; }
  }

  // Pair results
  static class Pair extends PrimSyn {
    final int _alias;
    private static TVLeaf x,y;
    public Pair() {
      super(x=new TVLeaf(),y=new TVLeaf(),new TVStruct(IDS[2],new TV3[]{x,y}));
      _alias = BitsAlias.new_alias(BitsAlias.LOCX);
    }
    @Override PrimSyn make() { return new Pair(); }
    @Override SB str(SB sb) { return sb.p("pair"); }
    @Override StructVal apply( Env e ) { return new StructVal().add("0",e._v0).add("1",e._v1); }
    @Override int iop(int x, int y) { throw AA.TODO(); }
  }


  // --- Env ---------------------------------------------------
  private static class Env {
    final Env _e;               // Linked list
    Val _v0, _v1, _v2;    // Values; referenced via deBrujin
    Env(Env e, Val v0, Val v1, Val v2) { _e=e; _v0=v0; _v1=v1; _v2=v2; }
    Env(Env e, Val v0, Val v1) { this(e,v0,v1,null); }
    Env(Env e, Val v0) { this(e,v0,null,null); }
    @Override public String toString() { return str(new SB(), new VBitSet()).toString(); }
    SB str(SB sb, VBitSet visit) {
      sb.p('(');
      if( _v0!=null ) _v0.str(sb       ,visit);
      if( _v1!=null ) _v1.str(sb.p(','),visit);
      if( _v2!=null ) _v2.str(sb.p(','),visit);
      sb.p(')');
      if( _e==null ) return sb;
      return _e.str(sb.p(','),visit);
    }
  }

  // --- Val -----------------------------------------------------
  // Either an integer (and _e==null) or a Continuation (_e!=null)
  public static abstract class Val {
    IntVal    as_int   () { return null; }
    FltVal    as_flt   () { return null; }
    KontVal   as_kont  () { return null; }    
    StructVal as_struct() { return null; }
    TypeNil as_flow() { throw AA.TODO(); }
    @Override final public String toString() { return str(new SB(), new VBitSet()).toString(); }
    abstract SB str(SB sb, VBitSet visit);
  }
  
  private static class IntVal extends Val {
    final int _con;
    IntVal(int con) { _con=con; }
    IntVal as_int() { return this; }
    SB str(SB sb, VBitSet visit) { return sb.p(_con); }
    TypeNil as_flow() { return TypeInt.con(_con); }
  }
  
  private static class FltVal extends Val {
    final double _con;
    FltVal(double con) { _con=con; }
    FltVal as_flt() { return this; }
    SB str(SB sb, VBitSet visit) { return sb.p(_con).p("f"); }
    TypeNil as_flow() { return TypeFlt.con(_con); }
  }
  
  private static class NilVal extends Val {
    static final NilVal NIL = new NilVal();
    SB str(SB sb, VBitSet visit) { return sb.p("nil"); }
  }
  
  private static class KontVal extends Val {
    private static int UID=1;
    private int _uid=UID++;
    Env _e;
    final Lambda _lam;
    KontVal(Env e, Lambda lam) { _e=e; _lam=lam; }
    KontVal as_kont() { return this; }
    SB str(SB sb, VBitSet visit) {
      sb.p("K").p(_uid);
      if( visit.tset(_uid) ) return sb;
      _lam.str(sb.p("[")).p(",");
      if( _e!=null ) _e.str(sb,visit);
      return sb.p("]");
    }
    public static void reset() { UID=1; }
  }
  
  private static class StructVal extends Val {
    int _len;
    String[] _labels = new String[2];
    Val   [] _vals   = new Val   [2];
    StructVal add(String label, Val val) {
      if( _len == _vals.length )  {
        _labels = Arrays.copyOf(_labels,_len<<1);
        _vals   = Arrays.copyOf(_vals  ,_len<<1);
      }
      _labels[_len  ] = label;
      _vals  [_len++] = val;
      return this;
    }
    StructVal as_struct() { return this; }
    Val at(String label) { return _vals[Util.find(_labels,label)]; }
    SB str(SB sb, VBitSet visit) {
      if( _labels.length==0 || _labels[0].equals("0") ) {
        sb.p("( ");
        for( int i=0; i<_len; i++ )
          _vals[i].str(sb,visit).p(", ");
        return sb.unchar(2).p(")");
      } else {
        sb.p("@{ ");
        for( int i=0; i<_len; i++ )
          _vals[i].str(sb.p(_labels[i]).p("="),visit).p("; ");
        return sb.p("}");
      }
    }
  }
}
