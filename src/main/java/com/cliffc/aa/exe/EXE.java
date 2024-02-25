package com.cliffc.aa.exe;

import com.cliffc.aa.AA;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Random;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.IntSupplier;

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
    if( isDigit(BUF[X]) || (BUF[X]=='-' && isDigit(BUF[X+1])) )
        return number();
    if( peek('"') ) return string();

    // Parse a Lambda
    if( peek('{') ) {           // Lambda
      Ary<String> args = new Ary<>(new String[]{null,null,null,"$dyn"});
      while( !peek('-') ) args.push(id());
      require('>');
      return new Lambda(args.asAry(), require(fterm(),'}'));
    }

    // Parse an Apply
    if( peek('(') ) {
      Syntax fun = fterm();
      Ary<Syntax> args = new Ary<>(new Syntax[]{null,null,null,new AField(new Ident("$dyn"))});
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
      term = id.equals("_") ? new DynField(term,new Ident("$dyn")) : new Field(id,term);
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
    boolean neg=false;
    if( peek('-') ) neg=true;
    while( X<BUF.length && isDigit(BUF[X]) )
      sum = sum*10+BUF[X++]-'0';
    if( X>= BUF.length || BUF[X]!='.' )
      return new Con(neg ? -sum : sum);
    // Ambiguous '.' in: 2.3 vs 2.x (field load from a number)
    if( X+1<BUF.length && isAlpha0(BUF[X+1]) )
      return new Con(neg ? -sum : sum);
    X++;
    double f = (double)sum;
    f = f + (BUF[X++]-'0')/10.0f;
    require('f');
    return new Con(neg ? -f : f);
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
    // Frame and Lambda counter
    static int FCNT=2;
    
    Syntax _par;                // Parent in the AST

    TV3 _tvar;                  // Current HM type
    public TV3 tvar() {         // U-F find
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
    // env is a linked list, with a <String,Val> mapping
    // A Val is either an Int, or a Kontinuation; K has a Lambda and an StructVal.
    final Val eval( PtrVal penv ) { Val def = eval0(penv); return eval1(penv,def); }
    // 2 parts; first part defs (if any) in the local StructVal.
    // Second part fills in the def.
    // Allows cyclic structs and self-recursive functions.
    abstract Val eval0( PtrVal penv );
    Val eval1( PtrVal penv, Val def ) { return def; };

    static void reset() { CNT=1; FCNT=2; }

    public void add_work() { }
  }

  
  // --- Constant ------------------------
  static class Con extends Syntax {
    final Val _con;
    Con( int    con ) { _con = new IntVal(con); }
    Con( double con ) { _con = new FltVal(con); }
    Con( String con ) { _con = new StrVal(con); }
    @Override final SB str(SB sb) { return _con.str(sb); }
    @Override void prep_tree(Ary<TV3> nongen) { _tvar = TV3.from_flow(_con.as_flow()); }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) { return map.apply(this); }
    @Override Val eval0( PtrVal penv ) { return _con; }
  }

  // --- Nil ------------------------
  static class Nil extends Syntax {
    @Override SB str(SB sb) { return sb.p("nil"); }
    @Override void prep_tree(Ary<TV3> nongen) { _tvar = new TVPtr(BitsAlias.EMPTY,new TVStruct(true)); _tvar.add_may_nil(false); }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) { return map.apply(this); }
    @Override NilVal eval0( PtrVal penv ) { return NilVal.NIL; }
  }

  // --- DefDynTable ------------------------
  static class DefDynTable extends Syntax {
    @Override SB str(SB sb) { return sb.p("def$dyn"); }
    @Override void prep_tree(Ary<TV3> nongen) { _tvar = new TVLeaf(); }
    @Override boolean hm(boolean test) {
      return tvar() instanceof TVDynTable tdyn && tdyn.resolve( test );
    }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) { return map.apply(this); }
    // Type flow of the TVDynTable, set after the program types
    private DynVal _dyn;
    // True if all resolved
    boolean resolvedDyn() {
      _dyn = new DynVal(tvar() instanceof TVDynTable tdyn ? tdyn : null);
      return _dyn._dyn==null || _dyn._dyn.all_resolved(); // Type error: Failed to resolve
    }
    @Override DynVal eval0( PtrVal penv ) { return _dyn; }
  }

  // --- Ident ------------------------
  // Lambda argument or Let def
  static class Ident extends Syntax {
    private final String _name;       // The identifier name

    private Syntax _def;
    private int _dbx;           // deBrujin index
    private String _argn;       // Arg index for Lambda, 0 for Let
    
    Ident( String name ) { _name=name; }
    @Override SB str(SB sb) { return sb.p(_name); }
    @Override void prep_tree(Ary<TV3> nongen) {
      int dbx = 0;
      boolean was_apply=false;
      for( Syntax syn = _par, prior=this; syn!=null; prior=syn, syn = syn._par ) {
        switch( syn ) {
        case Lambda lam -> {
          int argn = Util.find(lam._args,_name);
          if( argn != -1 ) {
            // Take TVar from the lambda directly; and zero-bias the arg index
            String dbarg = Util.eq(_name,"$dyn") ? _name : ("arg"+(argn-(ARG_IDX+1))).intern();
            init(lam, lam.arg(argn), dbx, dbarg);
            return;
          }
          dbx++;                // Bump deBrujin index
          was_apply = false;
        }
        case Let let -> {
          if( let._arg.equals(_name) ) {
            boolean fresh = prior==let._body;
            if( !fresh && was_apply && !(prior instanceof Struct) )
              throw new IllegalArgumentException("Cyclic reference to "+_name);
            init(let,fresh ? let._def.tvar().fresh(nongen.asAry()) : let._def.tvar(),dbx,_name);
            return;
          }
          dbx++;                // Bump deBrujin index
        }
        //case Struct str -> {
        //  if( str._closure ) {  // Closure is basically a pile-o-Lets
        //    if( (_argn=str._labels.find(_name)) != -1 )
        //      // Take TVar from the Struct, and since closure its fresh also
        //      { init(str,str.fld(_argn).tvar().fresh(nongen.asAry()),dbx,_argn); return; }
        //    //dbx++;              // Bump deBrujin index
        //  }
        //}
        case Root root -> {
          if( _name.equals("$dyn") ) {
            DefDynTable def = new DefDynTable();
            def._par = _par;
            if( _par instanceof DynField dfld ) dfld._dyn = def;
            else if( _par instanceof AField fld ) fld._ptr = def;
            else TODO();
            def.prep_tree(nongen);
            return;
          }
        }
        case Apply apply -> was_apply = true;
        default -> {}
        }
      }
      throw TODO("'"+_name+"' not found");
    }
    
    private void init( Syntax def, TV3 tv, int dbx, String argn ) {
      _tvar = tv;
      _def  = def;
      _dbx  = dbx;
      _argn = argn;
    }
    
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) { return map.apply(this); }
    @Override Val eval0( PtrVal penv ) {
      // Normal lookup using deBrujin index
      PtrVal ptr = penv;
      for( int i=0; i<_dbx; i++ )
        ptr = ptr.load().dsp();    // Index env via deBrujin index
      return ptr.load().at(_argn); // 
    }
  }

  // --- Lambda ------------------------
  static class Lambda extends Syntax {
    static final Ary<Lambda> FUNS = new Ary<>(Lambda.class);
    final Syntax _body;         // Function body
    final String[] _args;       // Argument names
    final int _fid;             // Unique ID for frame and lambda
    
    Lambda(String[] args, Syntax body ) {
      _body = body;  if( body!=null ) body._par = this;
      _args = args;
      _fid = FCNT++;
      FUNS.setX(_fid,this);
    }
    @Override SB str(SB sb) {
      sb.p(_fid).p("{ ");
      for( int i=AA.DSP_IDX; i< nargs(); i++ )
        sb.p(_args[i]).p(' ');
      return _body.str(sb.p("-> ")).p(" }");
    }
    SB strShort( SB sb ) { return sb.p("LAM").p(_fid); }
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
      ((TVLambda)tvar()).ret().unify(_body.tvar(),false);
    }
    
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      return reduce.apply(map.apply(this),_body.visit(map,reduce));
    }
    @Override KontVal eval0( PtrVal penv ) { return new KontVal(penv,this); }
    Val apply( PtrVal penv ) { return _body.eval(penv); }
  }

  // --- Apply ------------------------
  static class Apply extends Syntax {
    final Syntax _fun;
    final Syntax[] _args;
    Apply( Syntax fun, Syntax[] args ) {
      _fun = fun;  fun._par = this;
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
        : new TVLambda(nargs(),null,tvar());
      if( !(tfun instanceof TVLambda) )
        tfun.unify(lam,false);
      
      assert lam.nargs() == nargs();
      for( int i=ARG_IDX; i<nargs(); i++ ) {
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
    @Override Val eval0( PtrVal penv ) {
      // Eval the function
      KontVal fun = _fun.eval(penv).as_kont();
      // TODO: keeping existing structure until I can roll this StructVal build into
      // the function header and not at the Call/Apply site.
      StructVal env2 = new StructVal(fun._penv);
      PtrVal penv2 = new PtrVal(fun._lam._fid,env2);
      env2.add("$dyn",_args[ARG_IDX].eval(penv));
      for( int i=ARG_IDX+1; i<nargs(); i++ )
        env2.arg(i-(ARG_IDX+1),_args[i].eval(penv));
      // Eval the body, in the context of the closure extended by the args
      return fun._lam.apply(penv2);
      // TODO: pre-bind Prims...
      // (3 .+ 4)  // dot-field is ok after a prim int/flt/str.  Does prim lookup & binds.
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
    @Override Val eval0( PtrVal penv ) {
      Val pred = _pred.eval(penv);
      boolean t = switch( pred ) {
      case IntVal II -> II._con!=0;
      case FltVal FF -> FF._con!=0;
      case KontVal k -> true;   // Surely a bug
      case StructVal s -> true;
      case NilVal n -> false;
      case PtrVal p -> true;
      default -> throw TODO();
      };
      Syntax syn = t ? _t : _f;
      return syn.eval(penv);
    }
  }
  
  // --- Let ------------------------
  static class Let extends Syntax {
    final Syntax _def, _body;
    final String _arg;       // Argument name
    int _fid;                // Enclosing frame alias
    static final Ary<Let> LETS = new Ary<Let>(Let.class);
    
    Let(String arg, Syntax def, Syntax body ) {
      _def  = def;  def ._par = this;
      _body = body; body._par = this;
      _arg  = arg;
      LETS.setX(_uid,this);
    }
    @Override SB str(SB sb) { return _body.str(_def.str(sb.p(_arg).p(" = ")).p("; ")); }
    @Override void prep_tree(Ary<TV3> nongen) {
      for( Syntax syn = _par; true; syn = syn._par ) {
        if( syn instanceof Lambda lam ) { _fid = lam ._fid; break; }
        if( syn instanceof Root root  ) { _fid = root._fid; break; }
      }
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
    @Override Val eval0( PtrVal penv ) {
      PtrVal p0 = new PtrVal(_fid,new StructVal(penv)); // Premature push: no def yet, so null
      Val def = _def.eval0(p0);  // Eval def part 0
      p0.load().add(_arg,def);   // Close the cycle
      _def.eval1(p0,def);        // Eval def part 1
      //if( def instanceof KontVal k )
      //  k._env = e0;            // Let Rec
      return _body.eval(p0);
    }
  }

  // --- Struct ------------------------
  /**
     GIANT TODO:
     
     Observed that AA mixes Structs and Closures, on purpose.
     EXE does not.

     This is the Root Cause of why the AA test testStable.testStruct() fails but
     the matching EXE tests testStruct[9,10,12] (especially 12) don't have issues.

     The AA code triggers a recursive def of the display/closure, which appears
     as a polymorphic empty struct inside the DynTables and when fresh-unifying
     endlessly fresh clones and grows without bounds.  Doesn't happen for EXE
     variants, which end up with no or trivial displays.

     To show this problem in EXE (where its hugely easier to control and debug)
     I need to fold Let and Struct together.  Let needs to becomes a LetMutRec
     (its really a LetRec already), and then its basically a Struct plus or
     minus some "is_closure" flag and whether or not Idents are polymorphic or
     not.  Loads from Fields are not polymorphic, inside LetMutRec defs, or
     Lambda args.  Idents from closures ARE polymorphic.


   */
    

  static class Struct extends Syntax {
    final Ary<String> _labels;
    final Ary<Syntax> _flds;
    final int _fid;
    Struct( ) {
      _labels = new Ary<>(String.class);
      _flds = new Ary<>(Syntax.class);
      _fid = FCNT++;
    }
    void add( String label, Syntax fld ) { _labels.push(label); _flds.push(fld); fld._par = this; }
    Syntax fld(int i) { return _flds.at(i); }
    @Override SB str(SB sb) {
      sb.p('*').p(_fid).p("@{ ");
      for( int i=0; i<_flds._len; i++ )
        fld(i).str(sb.p(_labels.at(i)).p(" = ")).p("; ");
      return sb.unchar(1).p("}");
    }
    @Override void prep_tree(Ary<TV3> nongen) {
      TVStruct str = new TVStruct(_labels);
      _tvar = new TVPtr(BitsAlias.EMPTY,str);
      for( int i=0; i<_flds._len; i++ ) {
        fld(i).prep_tree(nongen);
        str.arg(i).unify(fld(i).tvar(),false);
      }
    }
    
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      T rez = map.apply(this);
      for( Syntax fld : _flds )
        rez = reduce.apply(rez,fld.visit(map,reduce));
      return rez;
    }
    @Override PtrVal eval0( PtrVal penv ) {
      return new PtrVal(_fid,new StructVal());
    }
    @Override PtrVal eval1( PtrVal penv, Val val ) {
      PtrVal ptr = (PtrVal)val;
      StructVal s = ptr.load();
      for( int i=0; i<_flds._len; i++ )
        s.add(_labels.at(i),fld(i).eval(penv));
      return ptr;
    }
  }

  // --- Field ------------------------
  static class Field extends Syntax {
    final String _lab;
    Syntax _ptr;
    Field( String lab, Syntax ptr ) { _ptr = ptr; ptr._par = this; _lab=lab; }
    @Override SB str(SB sb) { return _ptr.str(sb).p(".").p(_lab); }
    @Override void prep_tree(Ary<TV3> nongen) {
      _tvar = new TVLeaf();
      _ptr.prep_tree(nongen);

      TVPtr ptr = new TVPtr(BitsAlias.EMPTY,new TVStruct(new String[]{_lab},new TV3[]{_tvar},true));
      // TODO: Cannot add use_nil without the full up-cast of not-nil after IF
      //s.add_use_nil();
      _ptr.tvar().unify(ptr,false);
      if( ptr.find().as_ptr().load().idx(_lab) == -1 )
        throw new IllegalArgumentException("Missing field '"+_lab+"'");
    }
    
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      return reduce.apply(map.apply(this),_ptr.visit(map,reduce));
    }
    @Override Val eval0( PtrVal penv ) {
      return _ptr.eval(penv).as_ptr().load().at(_lab);
    }
  }

  // --- AField ------------------------
  static class AField extends Syntax {
    Syntax _ptr;
    AField( Syntax ptr ) { _ptr = ptr; ptr._par = this; }
    @Override SB str(SB sb) { return _ptr.str(sb).p(".A").p(_par._uid); }
    @Override void prep_tree(Ary<TV3> nongen) {
      _tvar = new TVLeaf();
      _ptr.prep_tree(nongen);
      
      TV3 tv3 = tvar();
      TV3 ptr = _ptr.tvar();
      // Inflate ptr to a dyntable
      TVDynTable ptrdyn;
      if( ptr instanceof TVDynTable tdyn0 )
        ptrdyn = tdyn0;
      else
        ptr.unify(ptrdyn = new TVDynTable(),false);
      
      TV3 self = ptrdyn.find_apy(_par);
      if( self==null )
        ptrdyn.add_apy(_par,tv3);
      else
        assert self==tv3;

      ptrdyn.resolve(false);
    }

    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      return reduce.apply(map.apply(this),_ptr.visit(map,reduce));
    }
    @Override Val eval0( PtrVal penv ) {
      return _ptr.eval(penv).as_dyn().at((Apply)_par);
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
    Syntax _ptr;                // The struct to select from; a list of labels
    Syntax _dyn;                // The DynTable, gives a self->label mapping
    private String _label;
    DynField(Syntax ptr, Syntax dyn ) {
      _ptr = ptr;
      _dyn = dyn;
      ptr._par = this;
      dyn._par = this;
      _label = (_uid+"Load").intern(); // Generated by TVDynTable
    }
    @Override SB str(SB sb) { return _ptr.str(sb).p("._"); }
    @Override void prep_tree(Ary<TV3> nongen) {
      _tvar = new TVLeaf();
      _ptr.prep_tree(nongen);
      _dyn.prep_tree(nongen);
      TVPtr ptr = new TVPtr(BitsAlias.EMPTY,new TVStruct(new String[]{},new TV3[]{},true));
      _ptr.tvar().unify(ptr,false);
      TVDynTable dyn = new TVDynTable();
      _dyn.tvar().unify(dyn,false);
      dyn = (TVDynTable)dyn.find();
      dyn.add_dyn(this,ptr.find(),_tvar);
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
    @Override Val eval0( PtrVal penv ) {
      DynVal dyn = _dyn.eval(penv).as_dyn();
      String label = dyn._dyn.find_label(this);
      return _ptr.eval(penv).as_ptr().load().at(label);
    }
  }


  // --- Root ------------------------
  public static class Root extends Syntax {
    final Syntax  _prog;
    final int _fid;             // Root or global frame
    Root( Syntax prog ) {
      _prog=prog;
      prog._par = this;
      _fid = 0;
    }
    @Override SB str( SB sb ) { return _prog.str(sb.p("Root ")); }
    @Override void prep_tree(Ary<TV3> nongen) {
      _prog.prep_tree(nongen);
      _tvar = _prog.tvar();
    }
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) {
      return reduce.apply(map.apply(this),_prog.visit(map,reduce));
    }
    @Override public Val eval0( PtrVal penv ) {
      penv = new PtrVal(_fid,new StructVal(null));
      return _prog.eval(penv);
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
          if( syn instanceof DefDynTable dyn && !dyn.resolvedDyn() ) {
            boolean resolve_progress = dyn.hm(false);
            throw new IllegalArgumentException("Unresolved dynamic field");
          }
          else return null;
        }, (a,b) -> null );
      // TODO: Worklist based HM typing
      return this;
    }
  }

  // --- PrimSyn ------------------------
  abstract static class PrimSyn extends Lambda {
    static final String[][] IDS = new String[][] {
      {"ctl","mem","dsp"},
      {"ctl","mem","dsp","dyn"},
      {"ctl","mem","dsp","dyn","0"},
      {"ctl","mem","dsp","dyn","0","1"},
    };
    static TV3 INT64() { return new TVBase(TypeInt.INT64); }
    static TV3 FLT64() { return new TVBase(TypeFlt.FLT64); }
    static TV3 STR  () { return new TVBase(TypeMemPtr.STRPTR); }
    
    final TV3[] _tvs;
    PrimSyn(TV3... tvs) {
      super(IDS[tvs.length],null);
      _tvs = tvs;
    }
    abstract PrimSyn make();
    abstract String name();
    @Override final SB str(SB sb) { return sb.p(name()); }
    TV3 tret() { return _tvs[_tvs.length-1]; }
    
    @Override void prep_tree(Ary<TV3> nongen) {
      TVLambda lam = new TVLambda(nargs(),null,tret());
      for( int i=0; i<_tvs.length-1; i++ )
        lam.arg(ARG_IDX+1+i).unify(_tvs[i],false);
      _tvar = lam;
    }
    
    @Override <T> T visit( Function<Syntax,T> map, BiFunction<T,T,T> reduce ) { return map.apply(this);  }
    @Override Val apply( PtrVal penv ) {
      // See Apply.eval for field names
      Val v0 = penv.load().arg(0);
      Val v1 = penv.load().arg(1);
      if( v0 instanceof IntVal i0 ) return new IntVal(iop(i0._con,v1==null ?  0  : v1.getl()));
      if( v0 instanceof FltVal f0 ) return new FltVal(dop(f0._con,v1==null ?  0  : v1.getd()));
      if( v0 instanceof StrVal s0 ) return new StrVal(sop(s0._con,v1==null ? null: v1.gets()));
      throw TODO();
    }
    long   iop(long   x, long   y) { throw TODO(); }
    double dop(double x, double y) { throw TODO(); }
    String sop(String x, String y) { throw TODO(); }
  }

  // add integers
  static class Add extends PrimSyn {
    public Add() { super(INT64(), INT64(), INT64()); }
    @Override PrimSyn make() { return new Add(); }
    @Override String name() { return "+"; }
    @Override long iop(long x, long y) { return x+y; }
  }

  // sub integers
  static class Sub extends PrimSyn {
    public Sub() { super(INT64(), INT64(), INT64()); }
    @Override PrimSyn make() { return new Sub(); }
    @Override String name() { return "-"; }
    @Override long iop(long x, long y) { return x-y; }
  }

  // mul integers
  static class Mul extends PrimSyn {
    public Mul() { super(INT64(), INT64(), INT64()); }
    @Override PrimSyn make() { return new Mul(); }
    @Override String name() { return "*"; }
    @Override long iop(long x, long y) { return x*y; }
  }

  // div integers
  static class Div extends PrimSyn {
    public Div() { super(INT64(), INT64(), INT64()); }
    @Override PrimSyn make() { return new Div(); }
    @Override String name() { return "/"; }
    @Override long iop(long x, long y) { return x/y; }
  }

  // greater integers
  static class GT extends PrimSyn {
    public GT() { super(INT64(), INT64(), INT64()); }
    @Override PrimSyn make() { return new GT(); }
    @Override String name() { return ">"; }
    @Override long iop(long x, long y) { return x>y ? 1 : 0; }
  }

  // equal integers
  static class EQ extends PrimSyn {
    public EQ() { super(INT64(), INT64(), INT64()); }
    @Override PrimSyn make() { return new EQ(); }
    @Override String name() { return "=="; }
    @Override long iop(long x, long y) { return x==y ? 1 : 0; }
  }

  // inc integers
  static class Inc extends PrimSyn {
    public Inc() { super(INT64(), INT64()); }
    @Override PrimSyn make() { return new Inc(); }
    @Override String name() { return "+1"; }
    @Override long iop(long x, long y) { return x+1; }
  }

  // convert ints
  static class I2F extends PrimSyn {
    public I2F() { super(INT64(), FLT64()); }
    @Override PrimSyn make() { return new I2F(); }
    @Override String name() { return "i2f"; }
    @Override Val apply( PtrVal penv ) {
      return new FltVal(penv.load().arg(0).getl());
    }
  }

  // random boolean
  static class Rnd extends PrimSyn {
    private static final Random R = new Random(0x123456789L);
    public Rnd() { super(INT64()); }
    @Override PrimSyn make() { return new Rnd(); }
    @Override String name() { return "rnd"; }
    @Override IntVal apply( PtrVal penv ) {
      return new IntVal(R.nextBoolean() ? 1 : 0);
    }
    static void reset() { R.setSeed(0x123456789L); };
  }

  // add doubles
  static class FAdd extends PrimSyn {
    public FAdd() { super(FLT64(), FLT64(), FLT64()); }
    @Override PrimSyn make() { return new FAdd(); }
    @Override String name() { return "f+"; }
    @Override double dop(double x, double y) { return x+y; }
  }

  // mul doubles
  static class FMul extends PrimSyn {
    public FMul() { super(FLT64(), FLT64(), FLT64()); }
    @Override PrimSyn make() { return new FMul(); }
    @Override String name() { return "f*"; }
    @Override double dop(double x, double y) { return x*y; }
  }

  // sub doubles
  static class FSub extends PrimSyn {
    public FSub() { super(FLT64(), FLT64(), FLT64()); }
    @Override PrimSyn make() { return new FSub(); }
    @Override String name() { return "f-"; }
    @Override double dop(double x, double y) { return x-y; }
  }
  
  // greater doubles
  static class FGT extends PrimSyn {
    public FGT() { super(FLT64(), FLT64(), INT64()); }
    @Override PrimSyn make() { return new FGT(); }
    @Override String name() { return "f>"; }
    @Override IntVal apply( PtrVal penv ) {
      return new IntVal(penv.load().arg(0).getd() > penv.load().arg(1).getd() ? 1 : 0);
    }
  }

  // convert doubles
  static class F2I extends PrimSyn {
    public F2I() { super(FLT64(), INT64()); }
    @Override PrimSyn make() { return new F2I(); }
    @Override String name() { return "f2i"; }
    @Override IntVal apply( PtrVal penv ) {
      return new IntVal((long)(penv.load().arg(0).getd()+0.5));
    }
  }

  // String length
  static class Len extends PrimSyn {
    public Len() { super(STR(), INT64()); }
    @Override PrimSyn make() { return new Len(); }
    @Override String name() { return "#"; }
    @Override IntVal apply( PtrVal penv ) {
      StrVal s = (StrVal)penv.load().arg(0);
      return new IntVal(s._con.length());
    }
  }

  // concat strings
  static class SAdd extends PrimSyn {
    public SAdd() { super(STR(), STR(), STR()); }
    @Override PrimSyn make() { return new SAdd(); }
    @Override String name() { return "s+"; }
    @Override Val apply( PtrVal penv ) {
      String s0 = penv.load().arg(0).gets();
      String s1 = penv.load().arg(1).gets();
      return new StrVal(s0+s1);
    }
  }

  // convert int to string
  static class Str extends PrimSyn {
    public Str() { super(INT64(), STR()); }
    @Override PrimSyn make() { return new Str(); }
    @Override String name() { return "str"; }
    @Override StrVal apply( PtrVal penv ) {
      Val i0 = penv.load().arg(0);
      return new StrVal(""+i0.getl());
    }
  }

  // Pair results
  static class Pair extends PrimSyn {
    static final String[] FLDS = new String[]{TypeFld.CLZ,"0","1"};
    private static TVLeaf x,y;
    private static int alias;
    final int _fid;
    public Pair() {
      super(x=new TVLeaf(),y=new TVLeaf(),new TVPtr(BitsAlias.make0(alias = FCNT++),new TVStruct(FLDS,new TV3[]{TVPtr.PTRCLZ,x,y})));
      _fid = alias;
    }
    @Override PrimSyn make() { return new Pair(); }
    @Override String name() { return "pair"; }
    @Override PtrVal apply( PtrVal penv ) {
      StructVal sv = new StructVal();
      sv.add(TypeFld.CLZ,PtrVal.PTRCLZ);
      sv.add("0",penv.load().arg(0));
      sv.add("1",penv.load().arg(1));
      return new PtrVal(_fid,sv);
    }
  }


  // --- Val -----------------------------------------------------
  // Either an integer (and _e==null) or a Continuation (_e!=null)
  public static abstract class Val {
    static int EVCNT;
    IntVal    as_int   () { return null; }
    FltVal    as_flt   () { return null; }
    StrVal    as_str   () { return null; }
    PtrVal    as_ptr   () { return null; }
    KontVal   as_kont  () { return null; }    
    StructVal as_struct() { return null; }
    TypeNil   as_flow  () { throw TODO(); }
    DynVal    as_dyn   () { return null; }
    final int _uid = EVCNT++;
    @Override final public String toString() { return str(new SB()).toString(); }
    final SB str(SB sb) {
      VBitSet visit = new VBitSet();
      NonBlockingHashMapLong<String> dups  = new NonBlockingHashMapLong<>();
      _get_dups(visit,dups);
      visit.clear();
      return _str(sb,visit,dups);
    }
    // Tik-Tok printing, this is Tik
    SB _str(SB sb, VBitSet visit, NonBlockingHashMapLong<String> dups) {
      String dup = dups.get(_uid);
      if( dup!=null ) sb.p(dup);
      if( visit.tset(_uid) ) return sb;
      if( dup!=null ) sb.p(':');
      return _str0(sb,visit,dups);
    }
    // Tik-Tok printing, this is Tok
    abstract SB _str0(SB sb, VBitSet visit, NonBlockingHashMapLong<String> dups);
    String _get_dups(VBitSet visit, NonBlockingHashMapLong<String> dups) {
      return visit.tset(_uid) ? dup_name(dups) : null;
    }
    String dup_name( NonBlockingHashMapLong<String> dups ) {
      return dups.put(_uid,""+(char)('A'+dups.size()));
    }
    long   getl() { throw TODO(); }
    double getd() { throw TODO(); }
    String gets() { throw TODO(); }
    public static void reset() { EVCNT=0; }
  }
  
  private static class IntVal extends Val {
    final long _con;
    IntVal(long con) { _con=con; }
    IntVal as_int() { return this; }
    @Override SB _str (SB sb, VBitSet visit, NonBlockingHashMapLong<String> dups) { return sb.p(_con); }
    @Override SB _str0(SB sb, VBitSet visit, NonBlockingHashMapLong<String> dups) { throw TODO(); }
    @Override long getl() { return _con; }
    TypeNil as_flow() { return TypeInt.con(_con); }
  }
  
  private static class FltVal extends Val {
    final double _con;
    FltVal(double con) { _con=con; }
    FltVal as_flt() { return this; }
    @Override SB _str (SB sb, VBitSet visit, NonBlockingHashMapLong<String> dups) { return sb.p(_con).p("f"); }
    @Override SB _str0(SB sb, VBitSet visit, NonBlockingHashMapLong<String> dups) { throw TODO(); }
    @Override double getd() { return _con; }
    TypeNil as_flow() { return TypeFlt.con(_con); }
  }
  
  private static class StrVal extends Val {
    final String _con;
    StrVal(String con) { _con=con; }
    StrVal as_str() { return this; }
    @Override SB _str (SB sb, VBitSet visit, NonBlockingHashMapLong<String> dups) { return sb.p('"').p(_con).p('"'); }
    @Override SB _str0(SB sb, VBitSet visit, NonBlockingHashMapLong<String> dups) { throw TODO(); }
    @Override String gets() { return _con; }
    TypeNil as_flow() { return TypeMemPtr.STRPTR; }
  }
  
  private static class NilVal extends Val {
    static final NilVal NIL = new NilVal();
    @Override SB _str (SB sb, VBitSet visit, NonBlockingHashMapLong<String> dups) { return sb.p("nil"); }
    @Override SB _str0(SB sb, VBitSet visit, NonBlockingHashMapLong<String> dups) { throw TODO(); }
  }
  
  private static class KontVal extends Val {
    PtrVal _penv;
    final Lambda _lam;
    KontVal(PtrVal penv, Lambda lam) { _penv=penv; _lam=lam; }
    KontVal as_kont() { return this; }
    @Override SB _str0(SB sb, VBitSet visit, NonBlockingHashMapLong<String> dups) {
      _penv._str(sb.p("<"),visit,dups);
      _lam .strShort(sb.p(","));
      return sb.p(">");
    }
    @Override String _get_dups(VBitSet visit, NonBlockingHashMapLong<String> dups) {
      if( visit.tset(_uid) ) return dup_name(dups);
      return _penv==null ? null : _penv._get_dups(visit,dups);
    }
  }
  
  private static class PtrVal extends Val {
    static final PtrVal PTRCLZ = new PtrVal(0,new StructVal());
    final StructVal _val;
    final int _fid;
    PtrVal( int fidx, StructVal val ) { _val = val; _fid = fidx; }
    @Override PtrVal as_ptr() { return this; }
    StructVal load() { return _val; }
    SB strShort(SB sb) { return sb.p("*[").p(_fid).p("]"); }
    @Override SB _str0(SB sb, VBitSet visit, NonBlockingHashMapLong<String> dups) {
      return load()._str(strShort(sb),visit,dups);
    }
    @Override String _get_dups(VBitSet visit, NonBlockingHashMapLong<String> dups) {
      if( this==PTRCLZ ) return null;
      if( visit.tset(_uid) ) return dup_name(dups);
      return _val._get_dups(visit,dups);
    }
  }

  private static class StructVal extends Val {
    static final String[] ARGS = new String[]{"arg0","arg1","arg2"};
    @Override StructVal as_struct() { return this; }
    int _len;
    String[] _labels = new String[2];
    Val   [] _vals   = new Val   [2];
    StructVal( ) { }
    StructVal( PtrVal env ) { add(TypeFld.CLZ,env); }
    void add( String label, Val val) {
      if( _len == _vals.length )  {
        _labels = Arrays.copyOf(_labels,_len<<1);
        _vals   = Arrays.copyOf(_vals  ,_len<<1);
      }
      _labels[_len  ] = label;
      _vals  [_len++] = val;
    }
    Val at(String label) {
      int idx = Util.find(_labels,label);
      return idx == -1 ? null : _vals[idx];
    }
    Val  arg( int i ) { return at(ARGS[i]  ); }
    void arg( int i, Val v) { add(ARGS[i],v); }
    PtrVal dsp() { return (PtrVal)at(TypeFld.CLZ); }
    SB _str0(SB sb, VBitSet visit, NonBlockingHashMapLong<String> dups) {
      if( _len==0 ) return sb.p("()");
      
      if( Util.find(_labels,"0")!= -1 ) {
        sb.p("( ");
        for( int i=0; i<_len; i++ ) {
          if( Util.eq(_labels[i],TypeFld.CLZ) )  sb.p("_, ");
          else if( _vals[i]==null ) sb.p("null, ");
          else _vals[i]._str(sb,visit,dups).p(", ");
        }
        return sb.unchar(2).p(")");
      } else {
        sb.p("@{ ");
        for( int i=0; i<_len; i++ )
          if( Util.eq(_labels[i],TypeFld.CLZ) )  sb.p("_ ");
          else {
            sb.p(_labels[i]).p("=");
            if( _vals[i]==null ) sb.p("null");
            else _vals[i]._str(sb,visit,dups).p("; ");
          }
        return sb.p("}");
      }
    }
    @Override String _get_dups(VBitSet visit, NonBlockingHashMapLong<String> dups) {
      if( _len==0 ) return null; // Not a dup, just replicate
      if( visit.tset(_uid) ) return dup_name(dups);
      for( int i=0; i<_len; i++ )
        if( _vals[i]!=null ) 
          _vals[i]._get_dups(visit,dups);
      return null;
    }
  }

  private static class DynVal extends Val {
    final TVDynTable _dyn;
    DynVal(TVDynTable dyn) { _dyn = dyn; }
    @Override DynVal as_dyn() { return this; }
    
    Val at(Apply a) {
      if( _dyn==null ) return this;
      TV3 dyn = _dyn.find_apy(a);
      return new DynVal(dyn instanceof TVDynTable tdyn ? tdyn : null);
    }
    
    @Override SB _str0(SB sb, VBitSet visit, NonBlockingHashMapLong<String> dups) {
      return _dyn==null ? sb.p(0) : _dyn.str(sb,null,null,false,true);
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
    Val.reset();
    com.cliffc.aa.Env.top_reset(); // Hard reset
  }
}
