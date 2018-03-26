package com.cliffc.aa;

import com.cliffc.aa.util.Ary;

import java.text.NumberFormat;
import java.text.ParsePosition;
  
/** an implementation of language AA
 */

public class Parse {
  private final String _src;            // Source for error messages; usually a file name
  private final Env _e;                 // Lookup context
  private final byte[] _buf;            // Bytes being parsed
  private int _x;                       // Parser index
  private int _line;                    // Zero-based line number
  GVNGCP _gvn;                          // Pessimistic types

  // Fields strictly for Java number parsing
  private final NumberFormat _nf;
  private final ParsePosition _pp;
  private final String _str;

  Parse( String src, Env env, String str ) {
    _src = src;
    _line= 0;
    _e   = env;
    _buf = str.getBytes();
    _x   = 0;

    // Set fields strictly for Java number parsing
    _nf = NumberFormat.getInstance();
    _nf.setGroupingUsed(false);
    _pp = new ParsePosition(0);
    _str = str;          // Keep a complete string copy for java number parsing
    _gvn = new GVNGCP(false);   // Pessimistic during parsing
  }
  // Parse the string in the given lookup context, and return an executable program
  Node go( ) {
    Node res = top();
    if( skipWS() != -1 ) throw err("Syntax error; trailing junk");
    return res;
  }

  /** Parse a top-level */
  private Node top() {
    // Currently only supporting exprs
    return expr0();
  }

  /** Wheee.... parse grammer round 2...
   *  prog = expr END
   *  expr = term [binop term]*   // gather all the binops and sort by prec
   *  term = nfact                // No function call
   *  term = nfact ( [expr,]* )+  // One or more function calls in a row, args are delimited
   *  term = nfact nfact*         // One function call, all the args listed
   *  nfact= unop* fact           // Zero or more unop calls over a fact
   *  fact = id                   // variable lookup
   *  fact = num                  // number
   *  fact = (binop)              // Special syntactic form of binop; no spaces allowed; returns function constant
   *  fact = (unop)               // Special syntactic form of  unop; no spaces allowed; returns function constant
   *  fact = (expr)               // General expression called recursively
   *  binop = +-*/%&|             // etc; primitive lookup; can determine infix binop at parse-time
   *  unop  =  -!~                // etc; primitive lookup; can determine infix  unop at parse-time
   */
  
  /** Parse an expression:
   * e0 := null
   * e0 := e1
   * e0 := e1(e0,...) // fcn call; zero-or-more args allowed
   * e0 := e1 e0...   // fcn call; one -or-more args allowed

   * e1 := unop
   * e1 := [unop] e2 [binop e2]* // associates based on operator precedence across whole list of op-expr-op-expr...

   * e2 := e3 [. var] // optional lookup restricted to type/class of e3

   * e3 := var        // Basic vars pre-exist for primitives
   * e3 := num
   * e3 := (e0)       // grouping
   */

  // Return a top-level expression; may be null if there is none
  // e0 := e1         // not a fcn call
  // e0 := e1(e0,...) // fcn call; zero-or-more args allowed
  // e0 := e1 e1...   // fcn call; one -or-more args allowed
  private Node expr0() {
    Node fun = expr1(), arg;
    if( fun == null ) return null;   // No expression at all
    if( skipWS() == -1 ) return fun; // Just the original expression
    // Function application; parse out the argument list
    Ary<Node> args = new Ary<>(new Node[]{fun});
    if( peek('(') ) {               // Traditional fcn application
      if( (arg=expr1()) != null ) { // Check for a no-arg fcn call
        args.add(arg);              // Add first arg
        while( peek(',') ) {        // Gather comma-separated args
          if( (arg=expr1()) == null ) throw err("Missing argument in function call");
          args.add(arg);
        }
      }
      require(')'); 
    } else {                    // lispy-style fcn application
      while( (arg = expr1()) != null ) // While have args
        args.add(arg);                 // Gather WS-separate args
      if( args.len()==1 ) return fun;  // Not a function call
    }
    
    // Limit function choices to those matching arg count and type
    Type t = _gvn.type(fun);
    TypeFun tf;
    if( t instanceof TypeFun ) tf = (TypeFun)t;
    else if( t instanceof TypeUnion ) {
      tf = pick_fun((TypeUnion)t,args,1);
      if( tf == null ) throw AA.unimpl();
      _gvn.setype(fun,tf);
    } else throw err("A function is being called, but "+fun+" is not a function");
    if( tf._ts._ts.length != args._len-1 )
      throw err(""+tf+" expects "+tf._ts._ts.length+" arguments but called with "+(args._len-1));
    return _gvn.ideal(new ApplyNode(args.asAry()));
  }
  
  // associates based on operator precedence across whole list of op-expr-op-expr...
  // e1 := [unop] e2 [binop e2]* 
  private Node expr1() {
    Ary<Type> funs = new Ary<>(new Type[1],0);
    Ary<Node> args = new Ary<>(new Node[1],0);

    // Parse an optional unary function
    int oldx = _x;
    String un = token();
    Type unfun = un==null ? null : _e.lookup(un, TypeFun.any(un,1)); // Unary arg-count functions
    if( unfun==null ) _x=oldx;  // Reset if no leading unary function

    // Parse first required e2 after option unary func
    Node e2 = expr2();
    if( e2 == null )  // not a unary fcn application, so return the fcns if any
      return unfun == null ? null : _gvn.ideal(new ConNode(unfun));
    // Collect 1st fcn/arg pair; if no unary then 1st fcn is null
    funs.add(unfun);   args.add(e2);
    
    // Now loop for binop/arg pairs: parse Kleene star of [binop e2]
    while( true ) {
      int oldx2 = _x;
      String bin = token();
      if( bin==null ) break;
      Type binfun = _e.lookup(bin,TypeFun.any(bin,2)); // BinOp, or null
      if( binfun==null ) { _x=oldx2; break; } // Not a binop
      e2 = expr2();
      if( e2 == null ) throw err("missing expr after binary op "+bin);
      funs.add(binfun);  args.add(e2);
    }

    // Have a list of interspersed operators and args.
    // Build an expr tree with precedence.  First find max precedence.
    int max=-1;
    for( Type t : funs ) if( t != null ) max = Math.max(max,t.op_prec());
    // Now starting at max working down, group list by pairs into a tree
    while( args.len() > 1 || funs.at(0) != null ) {
      for( int i=0; i<funs.len(); i++ ) { // For all ops of this precedence level, left-to-right
        Type t = funs.at(i);
        if( t != null && t.op_prec()==max ) {
          TypeFun tf = (t instanceof TypeFun) ? (TypeFun)t : pick_fun((TypeUnion)t,args,i==0?0:i-1);
          Node pfun = _gvn.ideal(new ConNode(tf));
          if( i==0 ) {          // Unary op?
            args.set(i  ,_gvn.ideal(new ApplyNode(pfun, // Apply unary op
                                                  convert(args.at(i),tf._ts._ts[0]))));
            funs.set(i,null);   // Clear unary slot
          } else {              // Binary: build tree node, reduce list length
            args.set(i-1,_gvn.ideal(new ApplyNode(pfun,
                                       convert(args.at(i-1),tf._ts._ts[0]),
                                       convert(args.at(i  ),tf._ts._ts[1]))));
            funs.remove(i);  args.remove(i);  i--;
          }
        }
      }
      max--;
    }
    Type fun = funs.at(0);
    Node arg = args.at(0);
    return fun==null ? arg : _gvn.ideal(new ApplyNode(_gvn.ideal(new ConNode(fun)),arg)); // Apply any left over unary op
  }

  // optional lookup restricted to type/class of e3
  // e2 := e3 [. var] 
  private Node expr2() {
    Node e3 = expr3();
    if( peek('.') ) throw AA.unimpl();
    return e3;
  }
  
  // e3 := var        // Basic vars pre-exist for primitives
  // e3 := num
  // e3 := (e0)       // grouping
  private Node expr3() {
    int oldx = _x;
    if( skipWS() == -1 ) return null;
    if( peek('(') ) {
      Node e0 = expr0();
      if( e0==null ) { _x = oldx; return null; } // A bare "()" pair is not an e3
      require(')'); return e0;
    }
    byte c = _buf[_x];
    if( '0' <= c && c <= '9' ) return _gvn.ideal(new ConNode(number()));
    String tok = token();
    if( tok == null ) return null;
    Type var = _e.lookup(tok,Type.ANY);
    if( var == null ) { _x = oldx; return null; }
    if( var.canBeConst() ) return _gvn.ideal(new ConNode(var));
    // need to return the Node representing the var in the environment
    throw AA.unimpl();
  }

  // Toss out choices where any args are not "isa" the call requirements,
  // and error if there is not exactly 1 choice.
  // i==0 is 1-arg, i==1 is 2-arg
  private TypeFun pick_fun( TypeUnion tu, Ary<Node> args, int x ) {
    Type[] funs = tu._ts._ts;
    Type[] actuals = new Type[((TypeFun)funs[0])._args.length];
    for( int i=0; i<actuals.length; i++ ) actuals[i] = _gvn.type(args.at(x+i));
    TypeFun z=null;  int zcvts=999;
    // for each function, see if the args isa.  If not, toss it out.
    for( int i=0,j; i<funs.length; i++ ) {
      TypeFun fun = (TypeFun)funs[i];
      Type[] fargs = fun._ts._ts;
      int cvts=0;
      for( j=0; j<actuals.length; j++ )
        if( !(actuals[j].isa(fargs[j])) ) break;
        else if( !actuals[j].isBitShape(fargs[j]) ) cvts++;
      if( j<actuals.length ) continue; // Some argument does not apply; drop this choice
      if( z==null || cvts < zcvts ) { z=fun; zcvts = cvts; }
      else throw err("Ambiguous function choices");
    }
    return z;
  }

  // Throw in a primitive format conversion as needed
  private Node convert( Node actual, Type formal ) {
    Type act = _gvn.type(actual);
    if( act.isBitShape(formal) ) return actual;
    TypeFun cvt = Prim.convert(act,formal);
    if( cvt.is_lossy() ) throw new IllegalArgumentException("Requires lossy conversion");
    return _gvn.ideal(new ApplyNode(_gvn.ideal(new ConNode(cvt)),actual));
  }
  
 
  // Lexical tokens.  Any alpha, followed by any alphanumerics is a alpha-
  // token; alpha-tokens end with WS or any operator character.  Any collection
  // of the classic operator characters are a token, except that they will break
  // un-ambiguously.
  private String token() {
    byte c=skipWS();  int x = _x;
    if(   isAlpha0(c) ) while( _x < _buf.length && isAlpha1(_buf[_x]) ) _x++;
    else if( isOp0(c) ) while( _x < _buf.length && isOp1   (_buf[_x]) ) _x++;
    else return null;           // Not a token; specifically excludes e.g. all bytes >= 128, or most bytes < 32
    return new String(_buf,x,_x-x);
  }
  private boolean is_token(byte c ) { return isAlpha0(c) || isOp0(c); }
  
  // Parse a number; WS already skipped and sitting at a digit.  Relies on
  // Javas number parsing.
  private Type number() {
    _pp.setIndex(_x);
    Number n = _nf.parse(_str,_pp);
    _x = _pp.getIndex();
    if( n instanceof Long   ) return TypeInt.con(n.  longValue());
    if( n instanceof Double ) return TypeFlt.make(0,64,(n.doubleValue()));
    throw new RuntimeException(n.getClass().toString()); // Should not happen
  }
  
  // Require a specific character (after skipping WS) or polite error
  private void require( char c ) {
    if( peek(c) ) return;
    throw err("Expected '"+c+"' but "+(_x>=_buf.length?"ran out of text":"found '"+(char)(_buf[_x])+"' instead"));
  }

  private boolean peek( char c ) {
    if( skipWS()!=c ) return false;
    _x++;                       // Skip peeked character
    return true;
  }
  
  /** Advance parse pointer to the first non-whitespace character, and return
   *  that character, -1 otherwise.  */
  private byte skipWS() {
    while( _x < _buf.length ) {
      byte c = _buf[_x];
      if( c=='/' && _x+1 < _buf.length && _buf[_x+1]=='/' ) { skipEOL()  ; continue; }
      if( c=='/' && _x+1 < _buf.length && _buf[_x+1]=='*' ) { skipBlock(); continue; }
      if( c=='\n' ) _line++;
      if( !isWS(c) ) return c;
      _x++;
    }
    return -1;
  }
  private void skipEOL  () { throw AA.unimpl(); }
  private void skipBlock() { throw AA.unimpl(); }

  /** Return true if `c` passes a test */
  private static boolean isWS    (byte c) { return c == ' ' || c == '\t' || c == '\n' || c == '\r'; }
  private static boolean isAlpha0(byte c) { return ('a'<=c && c <= 'z') || ('A'<=c && c <= 'Z') || (c=='_'); }
  private static boolean isAlpha1(byte c) { return isAlpha0(c) || ('0'<=c && c <= '9'); }
  private static boolean isOp0   (byte c) { return "!#$%*+,-.;:=<>?@^[]{}~/".indexOf(c) != -1; }
  private static boolean isOp1   (byte c) { return isOp0(c); }

  // Handy for the debugger to print 
  @Override public String toString() { return new String(_buf,_x,_buf.length-_x); }

  // Build a string of the given message, the current line being parsed,
  // and line of the pointer to the current index.
  private String errMsg(String s) {
    // find line start
    int a=_x;
    while( a > 0 && _buf[a-1] != '\n' ) --a;
    if( _buf[a]=='\r' ) a++; // do not include leading \n or \n\r
    // find line end
    int b=_x;
    while( b < _buf.length && _buf[b] != '\n' ) b++;
    if( b < _buf.length ) b--; // do not include trailing \n or \n\r
    // error message
    StringBuilder sb = new StringBuilder().append('\n');
    sb.append(_src).append(':').append(_line).append(':').append(s).append('\n');
    sb.append(new String(_buf,a,b-a)).append('\n');
    int line_start = 0;
    for( int i=line_start; i<_x; i++ )
      sb.append(' ');
    sb.append('^').append('\n');
    return sb.toString();
  }
  private IllegalArgumentException err(String s) { return new IllegalArgumentException(errMsg(s)); }

  private String err_hint(Type... ts) {
    boolean allnum=true;
    for( Type t : ts ) if( !t.isa(Type.NUM) ) allnum=false;
    return allnum ? ", this can happen if there is no common (loss-free conversion) numeric format" : "";
  }
}
