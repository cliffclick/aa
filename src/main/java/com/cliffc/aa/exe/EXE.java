package com.cliffc.aa.exe;

import com.cliffc.aa.AA;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;

import java.io.IOException;
import java.io.InputStreamReader;
import java.io.BufferedReader;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.HashMap;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.IntSupplier;
import java.util.Random;

import static com.cliffc.aa.AA.*;

public class EXE {
  
  public static void main( String[] args ) throws IOException {
    for( String arg : args ) {
      if( arg.equals("-") ) repl();
      else {
        String prog = new String( Files.readAllBytes( Paths.get(arg)));
        run(prog,0,true,true);
      }
    }
  }

  // Parse; Type; Run
  private static final String ANSI_RESET = "\u001B[0m"; 
  private static final String RED  = "\u001B[31m";
  private static final String GREEN= "\u001B[32m";
  private static final String BLUE = "\u001B[34m";
  private static final String GREEN_BACK= "\u001B[42m";
  public static void run( String prog, int rseed, boolean do_hm, boolean do_gcp ) {
    Root root = compile(prog,rseed,do_hm,do_gcp);
    System.out.println(GREEN_BACK+"Type:"+ANSI_RESET+" "+root.tvar().p());
    System.out.println(GREEN_BACK+"Eval:"+ANSI_RESET+" "+root.eval(null));
    System.out.flush();
  }

  // Parse; type
  public static Root compile( String prog, int rseed, boolean do_hm, boolean do_gcp ) {
    reset();
    return parse(prog).do_hm();
  }

  static final HashMap<String,PrimSyn> PRIMSYNS = new HashMap<>(){{
      put("+"  ,new Add ());
      put("-"  ,new Sub ());
      put("*"  ,new Mul ());
      put("/"  ,new Div ());
      put(">"  ,new GT  ());
      put("==" ,new EQ  ());
      put("+1" ,new Inc ());
      put("rnd",new Rnd ());
      put("i2f",new I2F ());
      put("f+" ,new FAdd());
      put("f*" ,new FMul());
      put("f-" ,new FSub());
      put("f>" ,new FGT ());
      put("f2i",new F2I ());
      put("#"  ,new Len ());
      put("s+" ,new SAdd());
      put("str",new Str ());
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
    if( skipWS() != -1 ) throw TODO("Junk at end of program: " + str());
    // Inject Root
    return new Root(prog);
  }

  // Parse a term
  static Syntax term() {
    if( skipWS()==-1 ) throw TODO("Program ended early, missing a term");
    if( isDigit(BUF[X]) ) return number();
    if( peek('"') ) return string();

    // Parse a Lambda
    if( peek('{') ) {           // Lambda 
      Ary<String> args = new Ary<>(new String[]{null,null,"$dyn"});
      while( !peek('-') ) args.push(id());
      require('>');
      return new Lambda(args.asAry(), require(fterm(),'}'));
    }

    // Parse an Apply
    if( peek('(') ) {
      Syntax fun = fterm();
      Ary<Syntax> args = new Ary<>(new Syntax[]{null,null,new Ident("$dyn")});
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
      while( !peek("}") ) str.add(require(id(),'='),require(fterm(),';'));
      return str;      
    }
    
    // Let or Id
    if( isAlpha0(BUF[X]) || isOp(BUF[X]) ) {
      String id = id(false);
      if( peek('=') )
        // Let expression; "id = fterm(); term..."
        return new Let(id,require(fterm(),';'),fterm());
      if( id.equals("nil") ) return new Nil();
      PrimSyn prim = PRIMSYNS.get(id); // No shadowing primitives or this lookup returns the prim instead of the shadow
      return prim==null ? new Ident(id) : prim.make(); // Make a prim copy with fresh HM variables
    }

    throw TODO();
  }
  
  // Parse a term with an optional following field.
  private static Syntax fterm() {
    Syntax term = term();
    while( true ) {
      if( !peek('.') ) return term;
      String id = id( true);
      term = id.equals("_") ? new DynField(term,new Ident("$dyn")) : new Field(false,id,term);
    }
  }
  
  private static final SB ID = new SB();
  private static String id() { return id( false); }
  private static String id( boolean num ) {
    ID.clear();
    skipWS();
    while( X<BUF.length && ( isAlpha1(BUF[X]) || isOp(BUF[X]) || (num && isDigit(BUF[X])) ) )
      ID.p((char)BUF[X++]);
    String s = ID.toString().intern();
    if( s.isEmpty() ) throw TODO("Missing id");
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

  private static Syntax string() {
    SB sb = new SB();
    while( !peek('"') ) sb.p((char)BUF[X++]);
    return new Con(sb.toString());
  }
  
  private static byte skipWS() {
    while(true) {
      if( X == BUF.length ) return -1;
      if( X+1<BUF.length && BUF[X]=='/' && BUF[X+1]=='/' )
        while( X<BUF.length && BUF[X]!='\n' ) X++;
      if( X+1<BUF.length && BUF[X]=='/' && BUF[X+1]=='*' )
        while( BUF[X-2]!='*' || BUF[X-1]!='/' ) X++;
      if( !isWS(BUF[X]) ) return BUF[X];
      X++;
    }
  }
  
  private static boolean isWS    (byte c) { return c == ' ' || c == '\t' || c == '\n' || c == '\r'; }
  private static boolean isDigit (byte c) { return '0' <= c && c <= '9'; }
  private static boolean isOp    (byte c) { return "*?+-/>#=".indexOf(c)>=0; }
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

  private static void require(char c) { if( skipWS()!=c ) throw TODO("Missing '"+c+"'"); X++; }
  private static Syntax require(Syntax t, char c) { require(c); return t; }
  private static String require(String s, char c) { require(c); return s; }

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

    // Visit whole tree recursively, applying 'map' to self, and reducing that
    // with the recursive value from all children.
    abstract <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce );
    
    // Print for debugger
    @Override final public String toString() { return str(new SB()).toString(); }
    abstract SB str(SB sb);

    // First pass
    abstract void prep_tree(Ary<TV3> nongen);

    // Later passes, true for progress
    boolean hm(boolean test) { return false; }

    // SEK style evaluation machine.
    // Env is a linked list, with a Val (for Let) or a set of Vals (for Lambda).
    // A Val is either an Int, or a Kontinuation; K has a Lambda and an Env.
    abstract Val eval( Env e );

    static void reset() { CNT=1; }
  }

  
  // --- Constant ------------------------
  static class Con extends Syntax {
    final Val _con;
    Con( int    con ) { _con = new IntVal(con); }
    Con( double con ) { _con = new FltVal(con); }
    Con( String con ) { _con = new StrVal(con); }
    @Override SB str(SB sb) { return _con.str(sb,null,null); }
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

  // --- DefDynTable ------------------------
  static class DefDynTable extends Syntax {
    @Override SB str(SB sb) { return sb.p("def$dyn"); }
    @Override void prep_tree(Ary<TV3> nongen) { _tvar = new TVLeaf(); }
    @Override boolean hm(boolean test) {
      return tvar() instanceof TVDynTable tdyn && tdyn.resolve( test );
    }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) { return map.apply(this); }
    boolean resolvedDyn() {
      return !(tvar() instanceof TVDynTable tdyn) || tdyn.all_resolved();
    }
    @Override Val eval( Env e ) {
      return new DynVal(tvar() instanceof TVDynTable tdyn ? tdyn : null);
    }
  }

  // --- Ident ------------------------
  // Lambda argument or Let def
  static class Ident extends Syntax {
    private final String _name;       // The identifier name

    private Syntax _def;
    private int _dbx;           // deBrujin index
    private int _argn;          // Arg index for Lambda, 0 for Let
    
    Ident( String name ) { _name=name; }
    @Override SB str(SB sb) { return sb.p(_name); }
    @Override void prep_tree(Ary<TV3> nongen) {
      int dbx = 0;
      boolean was_apply=false;
      for( Syntax syn = _par, prior=this; syn!=null; prior=syn, syn = syn._par ) {
        if( syn instanceof Lambda lam ) {
          if( (_argn=Util.find(lam._args,_name)) != -1 )
            // Take TVar from the lambda directly; and zero-bias the arg index
            {  init(lam,lam.arg(_argn), dbx, _argn);  return; }
          dbx++;                // Bump deBrujin index
          was_apply = false;
        } else if( syn instanceof Let let ) {
          if( let._arg.equals(_name) ) {
            boolean fresh = prior==let._body;
            if( was_apply && !fresh )
              throw new IllegalArgumentException("Cyclic reference to "+_name);
            init(let,fresh ? let._def.tvar().fresh(nongen.asAry()) : let._def.tvar(),dbx,ARG_IDX);
            return;
          }
          dbx++;                // Bump deBrujin index
        } else if( syn instanceof Root root ) {
          if( _name.equals("$dyn") ) {
            DefDynTable def = new DefDynTable();
            def._par = _par;
            if( _par instanceof DynField dfld ) dfld._dyn = def;
            else if( _par instanceof Field fld && fld._par instanceof Apply ) fld._ptr = def;
            else TODO();
            def.prep_tree(nongen);
            return;
          }
        } else if( syn instanceof Apply ) {
          was_apply = true;
        }
      }
      throw TODO("'"+_name+"' not found");
    }
    
    private void init( Syntax def, TV3 tv, int dbx, int argn ) {
      _tvar = tv;
      _def  = def;
      _dbx  = dbx;
      _argn = argn;
    }
    
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) { return map.apply(this); }
    @Override Val eval( Env e ) {
      // Normal lookup using deBrujin index
      Env e0 = e;
      for( int i=0; i<_dbx; i++ )
        e0 = e0._e;               // Index env via deBrujin index
      return e0._vs[_argn];
    }
  }

  // --- Lambda ------------------------
  static class Lambda extends Syntax {
    static final Ary<Lambda> FUNS = new Ary<>(Lambda.class);
    final Syntax _body;         // Function body
    final String[] _args;       // Argument names
    final int _fidx;            // Unique ID
    
    Lambda(String[] args, Syntax body ) {
      _body = body;  if( body!=null ) body._par = this;
      _args = args;
      _fidx = BitsFun.new_fidx();
      FUNS.setX(_fidx,this);
    }
    @Override SB str(SB sb) {
      sb.p("{ ");
      for( int i=AA.DSP_IDX; i< nargs(); i++ )
        sb.p(_args[i]).p(' ');
      return _body.str(sb.p("-> ")).p(" }");
    }
    int nargs() { return _args.length; }
    TV3 arg(int i) { return tvar().arg(i); }
    
    @Override void prep_tree(Ary<TV3> nongen) {
      _tvar = new TVLambda(nargs(),new TVLeaf(),new TVLeaf());
      // Extend the nongen set by the new variables
      for( int i=AA.DSP_IDX; i<nargs(); i++ ) nongen.push(arg(i));
      // Prep the body
      _body.prep_tree(nongen);
      // Pop nongen stack
      nongen.pop(nargs()-AA.DSP_IDX);
      // TVLambda ret is made early, unify with body now
      ((TVLambda)tvar()).ret().unify(_body.tvar(),false);
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
      args[DSP_IDX] = new Field(true,Util.uid("A",_uid),args[DSP_IDX]);
      _args=args;
      for( Syntax arg : args )
        if( arg != null )
          arg._par = this;
    }
    @Override SB str(SB sb) {
      _fun.str(sb.p("(")).p(" ");
      for( Syntax arg : _args )
        if( arg != null )
          arg.str(sb).p(" ");
      return sb.unchar().p(")");
    }
    int nargs() { return _args.length; }
    
    @Override void prep_tree(Ary<TV3> nongen) {
      _tvar = new TVLeaf();
      _fun.prep_tree(nongen);

      TV3 tfun = _fun.tvar();
      TVLambda lam = tfun instanceof TVLambda lam0 ? lam0
        : new TVLambda(nargs(),new TVLeaf(),tvar());
      if( !(tfun instanceof TVLambda) )
        tfun.unify(lam,false);
      
      assert lam.nargs() == nargs();
      for( int i=DSP_IDX; i<nargs(); i++ ) {
        _args[i].prep_tree(nongen);
        if( lam.arg(i) != null )
          lam.arg(i).unify( _args[i].tvar(), false );
      }
      tvar().unify(lam.ret(),false);
    }
    
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      T slf = map.apply(this);
      T rez = reduce.apply(slf,_fun.visit(map,reduce));
      for( Syntax arg : _args )
        if( arg != null )
          rez = reduce.apply(rez,arg.visit(map,reduce));
      return rez;
    }
    @Override Val eval( Env e ) {
      // Eval the function
      KontVal fun = _fun.eval(e).as_kont();
      Env e2 = new Env(fun._e);
      for( int i=DSP_IDX; i<nargs(); i++ )
        e2._vs[i] = _args[i].eval(e);
      // Eval the body, in the context of the closure extended by the args
      return fun._lam.apply(e2);
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
      case KontVal k -> true;   // Surely a bug
      case StructVal s -> true;
      case NilVal n -> false;
      default -> throw TODO();
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
      //_dyn = _body.dyn();
    }
    
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      T rez = map.apply(this);
      T def = reduce.apply(rez,_def .visit(map,reduce));
      return  reduce.apply(def,_body.visit(map,reduce));
    }
    @Override Val eval( Env e ) {
      Env e0 = new Env(e);       // Premature push: no def yet, so null
      Val def = _def.eval(e0);  // Eval def
      e0._vs[ARG_IDX] = def;    // Close the cycle
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
    final boolean _dyn;         // True if reading a TVDynTable/DynVal, False is reading a TVStruct/StructVal
    final String _lab;
    Syntax _ptr;
    Field( boolean dyn, String id, Syntax ptr ) { _dyn = dyn; _ptr = ptr; ptr._par = this; _lab=id; }
    @Override SB str(SB sb) { return _ptr.str(sb).p(".").p(_lab); }
    @Override void prep_tree(Ary<TV3> nongen) {
      _tvar = new TVLeaf();
      _ptr.prep_tree(nongen);

      TVStruct s;
      if( _dyn ) {
        TVDynTable tdyn = new TVDynTable();
        tdyn.add_apy(_par._uid,_tvar);
        s = tdyn;
        
      } else {
        s = new TVStruct(new String[]{_lab},new TV3[]{_tvar},true);
        // TODO: Cannot add use_nil without the full up-cast of not-nil after IF
        //s.add_use_nil();
      }
      _ptr.tvar().unify(s,false);
      if( !(_ptr.tvar() instanceof TVStruct str && str.idx(_lab)>=0) )
        throw new IllegalArgumentException("Missing field '"+_lab+"'");
    }
    
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      return reduce.apply(map.apply(this),_ptr.visit(map,reduce));
    }
    @Override Val eval( Env e ) {
      Val val = _ptr.eval(e);
      return _dyn ? val.as_dyn().at(_lab) : val.as_struct().at(_lab);
    }
  }


  // --- DynField ------------------------

  /*  see testOver4.aa for examples of DynTables

      Takes a DynTable input at runtime, finds itself at the table root, loads
      the field label, does the dynamic field lookup.

      In the AST, the parent supplies the DynTable input.  In general, a
      DynTable is required at Lambdas as an extra input, supplied by Apply (who
      gets it from their parent).  DynTables are tree-structured, matching the
      AST/lexical structure.
      
      In the Value/concrete domain, the input DynTable maps either DynFields
      (e.g. this field itself) or Idents (Fresh in AA), and can be treated as a
      special kind of TVStruct - with AST elements as field labels.  A DynField
      label maps to a field label (e.g. string).  An Ident/Fresh label maps to a
      nested DynTable, recursively.

      In the TVar domain, the DynTable like a TVStruct whose labels are known
      as the name of the DynField/Ident itself, and whose field types need to
      be resolved.  To allow for resolution, the DynTable field type is the
      DynField input TVStruct type, and has to resolve by unifying 1 of those
      choices (which then fixes the resolved label in the DynTable).
      
   */
  
  static class DynField extends Syntax {
    Syntax _ptr;
    Syntax _dyn;          // 
    DynField(Syntax ptr, Syntax dyn ) {
      _ptr = ptr;
      _dyn = dyn;
      ptr._par = this;
      dyn._par = this;
    }
    @Override SB str(SB sb) { return _ptr.str(sb).p("._"); }
    @Override void prep_tree(Ary<TV3> nongen) {
      _tvar = new TVLeaf();
      _ptr.prep_tree(nongen);
      _dyn.prep_tree(nongen);
      TVStruct s = new TVStruct(new String[]{},new TV3[]{},true);
      _ptr.tvar().unify(s,false);
      TVDynTable dyn = new TVDynTable();
      _dyn.tvar().unify(dyn,false);
      dyn = (TVDynTable)dyn.find();
      dyn.add_dyn(_uid,s.find(),_tvar);
    }

    // Re-unify with resolved labels
    @Override boolean hm(boolean test) {
      TVDynTable tab = (TVDynTable)_dyn.tvar();
      return tab.resolve(test);
    }

    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      T rez = map.apply(this);
      T ptr = reduce.apply(rez,_ptr.visit(map,reduce));
      return  reduce.apply(ptr,_dyn.visit(map,reduce));
    }
    @Override Val eval( Env e ) {
      DynVal dyn = _dyn.eval(e).as_dyn();
      String label = dyn._dyn.find_label(_uid);
      return _ptr.eval(e).as_struct().at(label);
    }
  }


  // --- Root ------------------------
  static class Root extends Syntax {
    final Syntax  _prog;
    Root( Syntax prog ) {
      _prog=prog;
      prog._par = this;
    }
    @Override SB str( SB sb ) { return _prog.str(sb.p("Root ")); }
    @Override void prep_tree(Ary<TV3> nongen) {
      _prog.prep_tree(nongen);
      _tvar = _prog.tvar();
    }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      return reduce.apply(map.apply(this),_prog.visit(map,reduce));
    }
    @Override Val eval( Env e ) {
      e = new Env(null);
      return _prog.eval(e);
    }

    // Compute HM type
    Root do_hm() {
      prep_tree(new Ary<>(TV3.class));
      boolean progress=true;
      while( progress ) {
        progress = visit( syn -> syn.hm(false), (a,b) -> a || b );
      }
      // Check for simple type errors
      visit( syn -> {
          if( syn.tvar() instanceof TVErr terr )
            throw new IllegalArgumentException(terr.toString());
          if( syn.tvar() instanceof TVBase base && base._t instanceof TypeNil tn && tn.getClass()==TypeNil.class )
            throw new IllegalArgumentException("Mixing basic types");
          return null;
        },
        (a,b)->null);

      visit( syn -> {
          if( syn instanceof DefDynTable dyn && !dyn.resolvedDyn() )
            throw new IllegalArgumentException("Unresolved dynamic field");
          else return null;
        }, (a,b) -> null );
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
    static TV3 INT64() { return new TVBase(TypeInt.INT64); }
    static TV3 FLT64() { return new TVBase(TypeFlt.FLT64); }
    static TV3 STR  () { return new TVBase(TypeMemPtr.STRPTR); }
    
    final TV3[] _tvs;
    PrimSyn(TV3... tvs) {
      super(IDS[tvs.length-1],null);
      _tvs = tvs;
    }
    abstract PrimSyn make();
    TV3 tret() { return _tvs[_tvs.length-1]; }
    
    @Override void prep_tree(Ary<TV3> nongen) {
      TVLambda lam = new TVLambda(nargs()+AA.ARG_IDX,new TVLeaf(),tret());
      for( int i=0; i<nargs(); i++ )
        lam.arg(AA.ARG_IDX+i).unify(_tvs[i],false);
      _tvar = lam;
    }
    
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) { return map.apply(this);  }
    @Override Val apply( Env e ) {
      Val v1 = e._vs[ARG_IDX+1];
      IntVal i0 = e._vs[ARG_IDX].as_int();
      FltVal f0 = e._vs[ARG_IDX].as_flt();
      if( i0!=null ) return new IntVal(iop(i0._con,v1==null ? 0   : v1.as_int()._con));
      if( f0!=null ) return new FltVal(dop(f0._con,v1==null ? 0.0 : v1.as_flt()._con));      
      throw TODO();
    }
    int    iop(int    x, int    y) { throw TODO(); }
    double dop(double x, double y) { throw TODO(); }
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

  // greater integers
  static class GT extends PrimSyn {
    public GT() { super(INT64(), INT64(), INT64()); }
    @Override PrimSyn make() { return new GT(); }
    @Override SB str(SB sb) { return sb.p(">"); }
    @Override int iop(int x, int y) { return x>y ? 1 : 0; }
  }

  // equal integers
  static class EQ extends PrimSyn {
    public EQ() { super(INT64(), INT64(), INT64()); }
    @Override PrimSyn make() { return new EQ(); }
    @Override SB str(SB sb) { return sb.p("=="); }
    @Override int iop(int x, int y) { return x==y ? 1 : 0; }
  }

  // inc integers
  static class Inc extends PrimSyn {
    public Inc() { super(INT64(), INT64()); }
    @Override PrimSyn make() { return new Inc(); }
    @Override SB str(SB sb) { return sb.p("+1"); }
    @Override int iop(int x, int y) { return x+1; }
  }

  // convert ints
  static class I2F extends PrimSyn {
    public I2F() { super(INT64(), FLT64()); }
    @Override PrimSyn make() { return new I2F(); }
    @Override SB str(SB sb) { return sb.p("i2f"); }
    @Override Val apply( Env e ) {
      IntVal i0 = e._vs[ARG_IDX].as_int();
      return new FltVal(i0._con);
    }
  }

  // random boolean
  static class Rnd extends PrimSyn {
    private static final Random R = new Random(0x123456789L);
    public Rnd() { super(INT64()); }
    @Override PrimSyn make() { return new Rnd(); }
    @Override SB str(SB sb) { return sb.p("rnd"); }
    @Override Val apply(Env e) {
      return new IntVal(R.nextBoolean() ? 1 : 0);
    }
    static void reset() { R.setSeed(0x123456789L); };
  }

  // add doubles
  static class FAdd extends PrimSyn {
    public FAdd() { super(FLT64(), FLT64(), FLT64()); }
    @Override PrimSyn make() { return new FAdd(); }
    @Override SB str(SB sb) { return sb.p("f+"); }
    @Override double dop(double x, double y) { return x+y; }
  }

  // mul doubles
  static class FMul extends PrimSyn {
    public FMul() { super(FLT64(), FLT64(), FLT64()); }
    @Override PrimSyn make() { return new FMul(); }
    @Override SB str(SB sb) { return sb.p("f*"); }
    @Override double dop(double x, double y) { return x*y; }
  }

  // sub doubles
  static class FSub extends PrimSyn {
    public FSub() { super(FLT64(), FLT64(), FLT64()); }
    @Override PrimSyn make() { return new FSub(); }
    @Override SB str(SB sb) { return sb.p("f-"); }
    @Override double dop(double x, double y) { return x-y; }
  }
  
  // greater doubles
  static class FGT extends PrimSyn {
    public FGT() { super(FLT64(), FLT64(), INT64()); }
    @Override PrimSyn make() { return new FGT(); }
    @Override SB str(SB sb) { return sb.p("f>"); }
    @Override Val apply( Env e ) {
      FltVal f0 = e._vs[ARG_IDX  ].as_flt();
      FltVal f1 = e._vs[ARG_IDX+1].as_flt();
      return new IntVal(f0._con > f1._con ? 1 : 0);
    }
  }

  // convert doubles
  static class F2I extends PrimSyn {
    public F2I() { super(FLT64(), INT64()); }
    @Override PrimSyn make() { return new F2I(); }
    @Override SB str(SB sb) { return sb.p("f2i"); }
    @Override Val apply( Env e ) {
      FltVal f0 = e._vs[ARG_IDX].as_flt();
      return new IntVal((int)(f0._con+.5));
    }
  }

  // String length
  static class Len extends PrimSyn {
    public Len() { super(STR(), INT64()); }
    @Override PrimSyn make() { return new Len(); }
    @Override SB str(SB sb) { return sb.p("#"); }
    @Override Val apply( Env e ) {
      StrVal s0 = e._vs[ARG_IDX].as_str();
      return new IntVal(s0._con.length());
    }
  }

  // concat strings
  static class SAdd extends PrimSyn {
    public SAdd() { super(STR(), STR(), STR()); }
    @Override PrimSyn make() { return new SAdd(); }
    @Override SB str(SB sb) { return sb.p("s+"); }
    @Override Val apply( Env e ) {
      StrVal s0 = e._vs[ARG_IDX  ].as_str();
      StrVal s1 = e._vs[ARG_IDX+1].as_str();
      return new StrVal(s0._con + s1._con);
    }
  }

  // convert int to string
  static class Str extends PrimSyn {
    public Str() { super(INT64(), STR()); }
    @Override PrimSyn make() { return new Str(); }
    @Override SB str(SB sb) { return sb.p("str"); }
    @Override Val apply( Env e ) {
      IntVal i0 = e._vs[ARG_IDX].as_int();
      return new StrVal(""+i0._con);
    }
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
    @Override StructVal apply( Env e ) { return new StructVal().add("0",e._vs[ARG_IDX]).add("1",e._vs[ARG_IDX+1]); }    
  }


  // --- Env ---------------------------------------------------
  static int EVCNT;
  private static class Env {
    final Env _e;               // Linked list
    final Val[] _vs;            // Values; referenced via deBrujin
    final int _uid = EVCNT++;
    Env(Env e) { _e=e; _vs = new Val[ARG_IDX+2]; }
    @Override public String toString() { return str(new SB(),null,null).toString(); }
    public final SB str(SB sb, VBitSet visit, VBitSet dups) {
      if( visit==null ) {
        assert dups==null;
        _get_dups(visit=new VBitSet(),dups=new VBitSet());
        visit.clear();
      }
      return _str(sb,visit,dups);
    }
    final SB _str(SB sb, VBitSet visit, VBitSet dups) {
      sb.p("( ");
      if( _vs[DSP_IDX]!=null ) _vs[DSP_IDX].str(sb.p("$dyn="),visit,dups).p(',');
      for( int i=ARG_IDX; i< _vs.length; i++ )
        if( _vs[i] != null )
          _vs[i].str(sb.p("e").p(i).p("="),visit,dups).p(',');
      sb.unchar(1).p(")");
      if( _e==null ) return sb;
      return _e.str(sb.p(','),visit,dups);
    }
    void _get_dups(VBitSet visit, VBitSet dups) {
      if( visit.tset(_uid) )
        { dups.set(_uid); return; }
      for( int i=DSP_IDX; i< _vs.length; i++ )
        if( _vs[i] != null )
          _vs[i]._get_dups(visit,dups);      
    }
    public static void reset() { EVCNT=0; }
  }

  // --- Val -----------------------------------------------------
  // Either an integer (and _e==null) or a Continuation (_e!=null)
  public static abstract class Val {
    IntVal    as_int   () { return null; }
    FltVal    as_flt   () { return null; }
    StrVal    as_str   () { return null; }
    KontVal   as_kont  () { return null; }    
    StructVal as_struct() { return null; }
    TypeNil   as_flow  () { throw TODO(); }
    DynVal    as_dyn   () { return null; }
    final int _uid = EVCNT++;
    @Override final public String toString() { return str(new SB(),null,null).toString(); }
    public final SB str(SB sb, VBitSet visit, VBitSet dups) {
      if( visit==null ) {
        assert dups==null;
        _get_dups(visit=new VBitSet(),dups=new VBitSet());
        visit.clear();
      }
      return _str(sb,visit,dups);
    }

    abstract SB _str(SB sb, VBitSet visit, VBitSet dups);
    void _get_dups(VBitSet visit, VBitSet dups) {
      if( visit.tset(_uid) )
        dups.set(_uid);
    }
  }
  
  private static class IntVal extends Val {
    final int _con;
    IntVal(int con) { _con=con; }
    IntVal as_int() { return this; }
    SB _str(SB sb, VBitSet visit, VBitSet dups) { return sb.p(_con); }
    TypeNil as_flow() { return TypeInt.con(_con); }
  }
  
  private static class FltVal extends Val {
    final double _con;
    FltVal(double con) { _con=con; }
    FltVal as_flt() { return this; }
    SB _str(SB sb, VBitSet visit, VBitSet dups) { return sb.p(_con).p("f"); }
    TypeNil as_flow() { return TypeFlt.con(_con); }
  }
  
  private static class StrVal extends Val {
    final String _con;
    StrVal(String con) { _con=con; }
    StrVal as_str() { return this; }
    SB _str(SB sb, VBitSet visit, VBitSet dups) { return sb.p('"').p(_con).p('"'); }
    TypeNil as_flow() { return TypeMemPtr.STRPTR; }
  }
  
  private static class NilVal extends Val {
    static final NilVal NIL = new NilVal();
    SB str(SB sb, VBitSet visit) { return sb.p("nil"); }
    SB _str(SB sb, VBitSet visit, VBitSet dups) { return sb.p("nil"); }
  }
  
  private static class KontVal extends Val {
    private static int UID=1;
    private final int _uid=UID++;
    Env _e;
    final Lambda _lam;
    KontVal(Env e, Lambda lam) { _e=e; _lam=lam; }
    KontVal as_kont() { return this; }
    SB _str(SB sb, VBitSet visit, VBitSet dups) {
      sb.p("K").p(_uid);
      if( visit.tset(_uid) ) return sb;
      sb.p("[");
      //_lam.str();
      sb.p("LAMBDA");
      sb.p(",");
      if( _e!=null ) _e.str(sb,visit,dups);
      return sb.p("]");
    }
    @Override void _get_dups(VBitSet visit, VBitSet dups) {
      if( visit.tset(_uid) )
        dups.set(_uid);
      if( _e!=null ) _e._get_dups(visit,dups);
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
    @Override StructVal as_struct() { return this; }
    Val at(String label) { return _vals[Util.find(_labels,label)]; }
    SB _str(SB sb, VBitSet visit, VBitSet dups) {
      if( _labels.length==0 || _labels[0].equals("0") ) {
        sb.p("( ");
        for( int i=0; i<_len; i++ )
          _vals[i].str(sb,visit,dups).p(", ");
        return sb.unchar(2).p(")");
      } else {
        sb.p("@{ ");
        for( int i=0; i<_len; i++ )
          _vals[i].str(sb.p(_labels[i]).p("="),visit,dups).p("; ");
        return sb.p("}");
      }
    }
    @Override void _get_dups(VBitSet visit, VBitSet dups) {
      if( visit.tset(_uid) )
        dups.set(_uid);
      for( int i=0; i<_len; i++ )
        _vals[i]._get_dups(visit,dups);
    }
  }

  
  private static class DynVal extends Val {
    final TVDynTable _dyn;
    DynVal(TVDynTable dyn) { _dyn = dyn; }
    @Override DynVal as_dyn() { return this; }
    
    Val at(String lab) {
      assert lab.charAt(0)=='A'; // Only for Applys and nested dyntable
      if( _dyn==null ) return this;
      TV3 dyn = _dyn.arg(lab);
      return new DynVal(dyn instanceof TVDynTable tdyn ? tdyn : null);
    }
    
    @Override SB _str(SB sb, VBitSet visit, VBitSet dups) { return _dyn==null ? sb.p(0) :_dyn.str(sb,visit,dups,false,true); }
    @Override void _get_dups(VBitSet visit, VBitSet dups) {
      if( visit.tset(_uid) )
        dups.set(_uid);
      if( _dyn!=null )
        _dyn._get_dups(visit,dups,false,false);
    }
  }

  // REPL
  private static void repl() throws IOException {
    BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
    while( true ) {
      System.out.print(BLUE+"aa> "+ANSI_RESET);
      System.out.flush();
      String str = in.readLine();
      if( str == null ) break;
      try {
        run(str,0,true,true);
      } catch( Exception e ) {
        System.err.print(RED);
        System.err.println(e);
        System.err.print(ANSI_RESET);
        System.err.flush();
      }
    }
    in.close();
  }

  public static void reset() {
    Syntax.reset();
    Rnd.reset();
    Env.reset();
    KontVal.reset();
  }
}
