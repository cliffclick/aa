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
  Node go( ) { return prog(); }

  /** Wheee.... parse grammer round 2...
   *  prog = stmt END
   *  stmt = [id = ] expr [; stmt]* // id must not exist, and is available in later statements
   *  expr = term [binop term]*   // gather all the binops and sort by prec
   *  term = nfact                // No function call
   *  term = nfact ( [expr,]* )+  // One or more function calls in a row, args are delimited
   // *  term = nfact nfact*         // One function call, all the args listed
   *  nfact= uniop* fact          // Zero or more uniop calls over a fact
   *  fact = id                   // variable lookup
   *  fact = num                  // number
   *  fact = (binop)              // Special syntactic form of binop; no spaces allowed; returns function constant
   *  fact = (uniop)              // Special syntactic form of uniop; no spaces allowed; returns function constant
   *  fact = (stmt)               // General statement called recursively
   *  binop = +-*%&|              // etc; primitive lookup; can determine infix binop at parse-time
   *  uniop  =  -!~               // etc; primitive lookup; can determine infix uniop at parse-time
   */
  /** Parse a top-level:
   *  prog = expr END */
  private Node prog() {
    // Currently only supporting exprs
    Node res = stmt();
    if( skipWS() != -1 ) throw err("Syntax error; trailing junk");
    return res;
  }

  private Node stmt() {
    // Scan for 'id ='.  Error if id pre-exists.  If either 'id' or '=' is not
    // found, then no assignment.
    int oldx = _x;
    String token = token();
    if( token != null ) {
      Type t = _e.lookup(token,Type.ANY);
      if( peek('=') ) {         // Assignment?
        if( t != null ) throw err("Cannot re-assign ref "+token);
      } else {                  // No assignment
        _x = oldx;              // Unwind token parse
        token = null;
      }
    }
    Node expr = expr();
    if( token != null ) {
      // here need to expand _e to make token to expr.
      // TODO: _e maps names to Nodes, not Types.
      throw AA.unimpl();
    }
    return expr;
  }
  
  /** Parse an expression, a list of terms and infix operators
   *  expr = term [binop term]*
   *  @return Node does NOT need gvn() */
  private Node expr() {
    Node term = gvn(term());
    if( term == null ) return null; // Term is required, so missing term implies not any expr
    // Collect 1st fcn/arg pair
    Ary<Type> funs = new Ary<>(new Type[1],0);
    Ary<Node> args = new Ary<>(new Node[1],0);
    funs.add(null);   args.add(term);
    
    // Now loop for binop/term pairs: parse Kleene star of [binop term]
    while( true ) {
      int oldx = _x;
      skipWS();
      String bin = token();
      if( bin==null ) break;    // Valid parse, but no more Kleene star
      Type binfun = _e.lookup(bin,TypeFun.any(bin,2)); // BinOp, or null
      if( binfun==null ) { _x=oldx; break; } // Not a binop, no more Kleene star
      term = gvn(term());
      if( term == null ) throw err("missing expr after binary op "+bin);
      funs.add(binfun);  args.add(term);
    }

    // Have a list of interspersed operators and terms.
    // Build a tree with precedence.
    int max=-1;                 // First find max precedence.
    for( Type t : funs ) if( t != null ) max = Math.max(max,t.op_prec());
    // Now starting at max working down, group list by pairs into a tree
    while( args.len() > 1 ) {
      for( int i=1; i<funs.len(); i++ ) { // For all ops of this precedence level, left-to-right
        Type t = funs.at(i);
        assert t.op_prec() <= max;
        if( t.op_prec() < max ) continue; // Not yet
        // Either a function, or an overload-of-functions.  Resolve overloads.
        TypeFun tf = (t instanceof TypeFun) ? (TypeFun)t : pick_fun((TypeUnion)t,args,i-1,2);
        args.set(i-1,gvn(new ApplyNode(gvn(new ConNode(tf)),
                                       convert(args.at(i-1),tf._ts._ts[0]),
                                       convert(args.at(i  ),tf._ts._ts[1]))));
        funs.remove(i);  args.remove(i);  i--;
      }
      max--;
    }
    return args.at(0);
  }

  /** Parse a function call, or not
   *  term = nfact                // No function call
   *  term = nfact ( [expr,]* )+  // One or more function calls in a row, each set of args are delimited
   *  term = nfact nfact*         // One function call, all the args listed
   *  @return Node needs gvn() */
  private Node term() {
    Node fun = nfact(), arg;    // nfactor
    if( fun == null ) return null;   // No term at all
    if( skipWS() == -1 ) return fun; // Just the original term
    // Function application; parse out the argument list
    Ary<Node> args = new Ary<>(new Node[]{gvn(fun)});
    if( peek('(') ) {               // Traditional fcn application
      if( (arg=stmt()) != null ) {  // Check for a no-arg fcn call
        args.add(arg);              // Add first arg
        while( peek(',') ) {        // Gather comma-separated args
          if( (arg=stmt()) == null ) throw err("Missing argument in function call");
          args.add(arg);
        }
      }
      require(')'); 
    } else {                    // lispy-style fcn application
      // TODO: Unable resolve amibguity with mixing "(fun arg0 arg1)" and
      // "fun(arg0,arg1)" argument calls.  Really having trouble with parsing
      // "1-2", where "1" parses in the function position and "-2" is a uniop
      // '-' applied to a 2: "-(2)".  This parses as the function "1" and its
      // single arg "-(2)" - but "1" is not a function.
      return fun;              // No function call
      
      //while( (arg = stmt()) != null ) // While have args
      //  args.add(arg);                // Gather WS-separate args
      //if( args.len()==1 ) return fun; // Not a function call
    }
    
    // Limit function choices to those matching arg count and type
    Type t = _gvn.type(fun);
    TypeFun tf = resolve_function_type(t,args,args._len-1);
    if( tf._ts._ts.length != args._len-1 )
      throw err(""+tf+" expects "+tf._ts._ts.length+" arguments but called with "+(args._len-1));
    _gvn.setype(fun,tf);
    return new ApplyNode(args.asAry());
  }
  
  /** Parse any leading unary ops before a factor
   *  nfact = fact | uniop nfact 
   *  @return Node needs gvn() */
  private Node nfact() {
    int oldx = _x;
    skipWS();
    String uni = token();
    if( uni!=null ) { // Valid parse
      Type unifun = _e.lookup(uni,TypeFun.any(uni,1));
      if( unifun != null && unifun.op_prec() > 0 )  {
        Node arg = gvn(nfact()); // Recursive call
        if( arg == null ) throw err("Call to unary function "+unifun+", but missing the one required argument");
        TypeFun tf = resolve_function_type(unifun,new Ary<>(new Node[]{null,arg}),1);
        return new ApplyNode(gvn(new ConNode(tf)),arg);
      } else {
        _x=oldx;                // Unwind token parse and try again for a factor
      }
    }
    return fact();
  }

  /** Parse a factor, a leaf grammer token
   *  fact = id        // variable lookup, NOT a binop or uniop but might be e.g. function-valued, including un-/binops as values
   *  fact = num       // number
   *  fact = (binop)   // Special syntactic form of binop; no spaces allowed; returns function constant
   *  fact = (uniop)   // Special syntactic form of uniop; no spaces allowed; returns function constant
   *  fact = (expr)    // General expression called recursively
   *  @return Node needs gvn() */
  private Node fact() {
    if( skipWS() == -1 ) return null;
    byte c = _buf[_x];
    if( '0' <= c && c <= '9' ) return new ConNode(number());
    int oldx = _x;
    if( peek('(') ) { // Either a special-syntax pre/infix op, or a nested expression
      Type op = look_token();
      if( peek(')') && op != null && op.op_prec() > 0 )
        return new ConNode(op); // Return operator as a function constant
      _x = oldx+1;         // Back to the opening paren
      Node ex = stmt();
      if( ex==null ) { _x = oldx; return null; } // A bare "()" pair is not an expr
      require(')');
      return ex;
    }
    
    // Check for a valid 'id'
    Type var = look_token();
    // Disallow uniop and binop functions as factors.
    if( var == null || var.op_prec() > 0 ) { _x = oldx; return null; }
    // TODO: Need to return the Node representing the var in the environment
    if( var.canBeConst() ) return new ConNode(var);
    throw AA.unimpl();
  }

  // Lookup the immediate next token, withOUT advancing the cursor.
  // Used to lookup special op forms, e.g. "(-)" or "(++)".
  private Type look_token() {
    String tok = token();
    return tok == null ? null : _e.lookup(tok,Type.ANY);
  }
  
  // Convert type 't' and the args list to a single resolved function type
  private TypeFun resolve_function_type(Type t, Ary<Node> args, int nargs ) {
    if( t instanceof TypeFun ) return (TypeFun)t;
    if( t instanceof TypeUnion ) {
      TypeFun tf = pick_fun((TypeUnion)t,args,1,nargs);
      if( tf == null ) throw err(t+" does not have a "+nargs+"-argument version or the argument types do not match");
      return tf;
    } 
    throw err("A function is being called, but "+t+" is not a function type");
  }
  
  // Toss out choices where any args are not "isa" the call requirements,
  // and error if there is not exactly 1 choice.  Only the 1-arg list
  // resolves as a 1-arg function, otherwise always this is called
  // on binops.
  private TypeFun pick_fun( TypeUnion tu, Ary<Node> args, int x, int nargs ) {
    Type[] funs = tu._ts._ts;
    Type[] actuals = new Type[nargs];
    for( int i=0; i<actuals.length; i++ ) actuals[i] = _gvn.type(args.at(x+i));
    TypeFun z=null;  int zcvts=999;
    // for each function, see if the actual args isa the formal args.  If not, toss it out.
    for( int i=0,j; i<funs.length; i++ ) {
      TypeFun fun = (TypeFun)funs[i];
      Type[] fargs = fun._ts._ts;
      if( fargs.length != actuals.length ) continue; // Argument count mismatch
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
    return gvn(new ApplyNode(gvn(new ConNode(cvt)),actual));
  }
  
 
  // Lexical tokens.  Any alpha, followed by any alphanumerics is a alpha-
  // token; alpha-tokens end with WS or any operator character.  Any collection
  // of the classic operator characters are a token, except that they will break
  // un-ambiguously.
  private String token() {
    if( _x >= _buf.length ) return null;
    byte c=_buf[_x];  int x = _x;
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

  private Node gvn(Node n) { return n==null ? null : _gvn.ideal(n); }
  

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
