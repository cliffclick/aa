package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.util.Ary;

import java.text.NumberFormat;
import java.text.ParsePosition;
  
/** an implementation of language AA
 *
 *  GRAMMAR:
 *  prog = stmt END
 *  stmt = [id =]* expr [; stmt]* // ids must not exist, and are available in later statements
 *  expr = term [binop term]*   // gather all the binops and sort by prec
 *  term = nfact                // No function call
 *  term = nfact ( [expr,]* )+  // One or more function calls in a row, args are delimited
 // *  term = nfact nfact*         // One function call, all the args listed
 *  nfact= uniop* fact          // Zero or more uniop calls over a fact
 *  fact = id                   // variable lookup
 *  fact = num                  // number
 *  fact = (stmt)               // General statement called recursively
 *  fact = {func}               // Anonymous function declaration
 *  fact = {binop}              // Special syntactic form of binop; no spaces allowed; returns function constant
 *  fact = {uniop}              // Special syntactic form of uniop; no spaces allowed; returns function constant
 *  binop = +-*%&|              // etc; primitive lookup; can determine infix binop at parse-time
 *  uniop  =  -!~               // etc; primitive lookup; can determine infix uniop at parse-time
 *  func = { [[id]* ->]? stmt } // Anonymous function declaration
 */

public class Parse {
  private final String _src;            // Source for error messages; usually a file name
  private Env _e;                       // Lookup context; pushed and popped as scopes come and go
  private Node _ctrl;                   // Current control
  private final byte[] _buf;            // Bytes being parsed
  private int _x;                       // Parser index
  private int _line;                    // Zero-based line number
  GVNGCP _gvn;                          // Pessimistic types

  // Fields strictly for Java number parsing
  private final NumberFormat _nf;
  private final ParsePosition _pp;
  private final String _str;

  Parse( String src, Env env, GVNGCP gvn, String str ) {
    _src = src;
    _line= 0;
    _e   = env;
    _ctrl= env.lookup_filter(" control ",gvn,Type.CONTROL);
    _buf = str.getBytes();
    _x   = 0;

    // Set fields strictly for Java number parsing
    _nf = NumberFormat.getInstance();
    _nf.setGroupingUsed(false);
    _pp = new ParsePosition(0);
    _str = str;          // Keep a complete string copy for java number parsing
    _gvn = gvn;          // Pessimistic during parsing
  }
  // Parse the string in the given lookup context, and return an executable program
  Node go( ) { return prog(); }

  /** Parse a top-level:
   *  prog = stmt END */
  private Node prog() {
    // Currently only supporting exprs
    Node res = stmt();
    if( skipWS() != -1 ) throw err("Syntax error; trailing junk");
    return res;
  }

  /** Parse an expression, a list of terms and infix operators
   *  stmt = [id =]* expr [; stmt]* // ids must not exist, and are available in later statements
   *  @return Node does NOT need gvn() */
  private Node stmt() {
    Ary<String> toks = new Ary<>(new String[1],0);
    while( true ) {
      int oldx = _x;
      String tok = token();  // Scan for 'id = ...'
      if( tok == null ) break;
      if( !peek('=') ) { _x = oldx; break; } // Unwind token parse
      if( _e.lookup(tok)!=null ) throw err("Cannot re-assign ref '"+tok+"'");
      toks.add(tok);
    }
    Node expr = expr();
    if( expr == null ) {
      if( toks._len > 0 ) throw err("Missing expr after assignment of '"+toks.last()+"'");
      else return null;
    }
    for( String tok : toks )
      if( _e.lookup(tok)!=null ) throw err("Cannot re-assign ref '"+tok+"'");
      else _e.add(tok,expr);
    while( peek(';') )
      expr = stmt();
    return expr;
  }
  
  /** Parse an expression, a list of terms and infix operators
   *  expr = term [binop term]*
   *  @return Node does NOT need gvn() */
  private Node expr() {
    Node term = gvn(term());
    if( term == null ) return null; // Term is required, so missing term implies not any expr
    // Collect 1st fcn/arg pair
    Ary<Node> funs = new Ary<>(new Node[1],0);
    Ary<Node> args = new Ary<>(new Node[1],0);
    funs.add(null);   args.add(term);
    
    // Now loop for binop/term pairs: parse Kleene star of [binop term]
    while( true ) {
      int oldx = _x;
      String bin = token();
      if( bin==null ) break;    // Valid parse, but no more Kleene star
      Node binfun = _e.lookup_filter(bin,_gvn,TypeFun.any(2)); // BinOp, or null
      if( binfun==null ) { _x=oldx; break; } // Not a binop, no more Kleene star
      term = term();
      if( term == null ) throw err("missing expr after binary op "+bin);
      funs.add(gvn(binfun));  args.add(gvn(term));
    }

    // Have a list of interspersed operators and terms.
    // Build a tree with precedence.
    int max=-1;                 // First find max precedence.
    for( Node n : funs ) if( n != null ) max = Math.max(max,n.op_prec());
    // Now starting at max working down, group list by pairs into a tree
    while( args.len() > 1 ) {
      for( int i=1; i<funs.len(); i++ ) { // For all ops of this precedence level, left-to-right
        Node fun = funs.at(i);
        assert fun.op_prec() <= max;
        if( fun.op_prec() < max ) continue; // Not yet
        args.set(i-1,gvn(new ApplyNode(fun,args.at(i-1),args.at(i))));
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
    Node fun = gvn(nfact()), arg;    // nfactor
    if( fun == null ) return null;   // No term at all
    if( skipWS() == -1 ) return fun; // Just the original term
    // Function application; parse out the argument list
    Ary<Node> args = new Ary<>(new Node[]{fun});
    if( peek('(') ) {               // Traditional fcn application
      if( _gvn.type(fun).ret() == null )
        throw err("A function is being called, but "+_gvn.type(fun)+" is not a function type");
      if( (arg=stmt()) != null ) {  // Check for a no-arg fcn call
        args.add(arg);              // Add first arg
        while( peek(',') ) {        // Gather comma-separated args
          if( (arg=stmt()) == null ) throw err("Missing argument in function call");
          args.add(arg);
        }
      }
      require(')'); 
    } else {                    // lispy-style fcn application
      // TODO: Unable resolve ambiguity with mixing "(fun arg0 arg1)" and
      // "fun(arg0,arg1)" argument calls.  Really having trouble with parsing
      // "1-2", where "1" parses in the function position and "-2" is a uniop
      // '-' applied to a 2: "-(2)".  This parses as the function "1" and its
      // single arg "-(2)" - but "1" is not a function.
      return fun;              // No function call
      //while( (arg = stmt()) != null ) // While have args
      //  args.add(arg);                // Gather WS-separate args
      //if( args.len()==1 ) return fun; // Not a function call
    }
    Node rez = gvn(new ApplyNode(args.asAry()));
    if( _gvn.type(rez)==Type.ANY )
      throw err("Argument mismatch in call to "+fun);
    return rez;
  }
  
  /** Parse any leading unary ops before a factor
   *  nfact = fact | uniop nfact 
   *  @return Node needs gvn() */
  private Node nfact() {
    int oldx = _x;
    String uni = token();
    if( uni!=null ) { // Valid parse
      Node unifun = gvn(_e.lookup_filter(uni,_gvn,TypeFun.any(1)));
      if( unifun != null && unifun.op_prec() > 0 )  {
        Node arg = gvn(nfact()); // Recursive call
        if( arg == null )
          throw err("Call to unary function "+unifun+", but missing the one required argument");
        return new ApplyNode(unifun,arg);
      } else {
        _x=oldx;                // Unwind token parse and try again for a factor
      }
    }
    return fact();
  }

  /** Parse a factor, a leaf grammar token
   *  fact = num       // number
   *  fact = (expr)    // General expression called recursively
   *  fact = {binop}   // Special syntactic form of binop; no spaces allowed; returns function constant
   *  fact = {uniop}   // Special syntactic form of uniop; no spaces allowed; returns function constant
   *  fact = {func}    // Anonymous function declaration
   *  fact = id        // variable lookup, NOT a binop or uniop but might be e.g. function-valued, including un-/binops as values
   *  @return Node needs gvn() */
  private Node fact() {
    if( skipWS() == -1 ) return null;
    byte c = _buf[_x];
    if( '0' <= c && c <= '9' ) return new ConNode<>(number());
    int oldx = _x;
    if( peek('(') ) { // Either a special-syntax pre/infix op, or a nested expression
      Node ex = stmt();
      if( ex==null ) { _x = oldx; return null; } // A bare "()" pair is not an expr
      require(')');
      return ex;
    }
    // Anonymous function or operator
    if( peek('{') ) {
      String tok = token0();
      Node op = tok == null ? null : _e.lookup(tok);
      if( peek('}') && op != null && op.op_prec() > 0 )
        return op;              // Return operator as a function constant
      _x = oldx+1;              // Back to the opening paren
      return func();            // Anonymous function
    }
    
    // Check for a valid 'id'
    String tok = token0();
    if( tok == null ) return null;
    Node var = _e.lookup(tok);
    if( var == null )  throw err("Unknown ref '"+tok+"'");
    // Disallow uniop and binop functions as factors.
    if( var.op_prec() > 0 ) { _x = oldx; return null; }
    return var;
  }

  /** Parse an anonymous function; the opening '{' already parsed
   *  func = { [[id]* ->]? stmt } // Anonymous function declaration
   *  @return Node needs gvn() */
  private Node func() {
    int oldx = _x;
    Ary<String> ids = new Ary<>(new String[1],0);
    while( true ) {
      String tok = token();
      if( tok == null ) { ids.clear(); _x=oldx; break; } // not a "[id]* ->"
      if( tok.equals("->") ) break;
      ids.add(tok);
    }
    FunNode fun = (FunNode)gvn(new FunNode());
    _e = new Env(_e);           // Nest an environment for the local vars
    int cnt=0;                  // Add parameters to local environment
    for( String id : ids )  _e.add(id,gvn(new ParmNode(fun,++cnt,id)));
    Node ret = stmt();          // Parse function body
    fun.add_def(ret);           // Close cycle over function, so can find the return later
    _e = _e._par;               // Pop nested environment
    require('}');
    return fun;                 // Return function
  }
  
  private String token() { skipWS();  return token0(); }
  // Lexical tokens.  Any alpha, followed by any alphanumerics is a alpha-
  // token; alpha-tokens end with WS or any operator character.  Any collection
  // of the classic operator characters are a token, except that they will break
  // un-ambiguously.
  private String token0() {
    if( _x >= _buf.length ) return null;
    byte c=_buf[_x];  int x = _x;
    if(   isAlpha0(c) ) while( _x < _buf.length && isAlpha1(_buf[_x]) ) _x++;
    else if( isOp0(c) ) while( _x < _buf.length && isOp1   (_buf[_x]) ) _x++;
    else return null;           // Not a token; specifically excludes e.g. all bytes >= 128, or most bytes < 32
    return new String(_buf,x,_x-x);
  }

  // Parse a number; WS already skipped and sitting at a digit.  Relies on
  // Javas number parsing.
  private Type number() {
    _pp.setIndex(_x);
    Number n = _nf.parse(_str,_pp);
    _x = _pp.getIndex();
    if( n instanceof Long   ) return TypeInt.con(      n.  longValue());
    if( n instanceof Double ) return TypeFlt.make(0,64,n.doubleValue());
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
  private static boolean isOp0   (byte c) { return "!#$%*+,-.;:=<>?@^[]~/".indexOf(c) != -1; }
  private static boolean isOp1   (byte c) { return isOp0(c); }

  private Node gvn(Node n) { return n==null ? null : _gvn.xform(n); }
  

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
}
