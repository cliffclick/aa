package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.util.Ary;

import java.text.NumberFormat;
import java.text.ParsePosition;
  
/** an implementation of language AA
 *
 *  GRAMMAR:
 *  prog = stmt END
 *  stmt = [id =]* ifex [; stmt]* // ids must not exist, and are available in later statements
 *  ifex = expr ? expr : expr   // trinary logic
 *  expr = term [binop term]*   // gather all the binops and sort by prec
 *  term = nfact                // No function call
 *  term = nfact ( [stmt,]* )+  // One or more function calls in a row, args are delimited
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
  private final byte[] _buf;            // Bytes being parsed
  private int _x;                       // Parser index
  private int _line;                    // Zero-based line number
  GVNGCM _gvn;                          // Pessimistic types
  
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
    _gvn = Env._gvn;     // Pessimistic during parsing
  }
  // Parse the string in the given lookup context, and return an executable program
  TypeEnv go( ) { return prog(); }

  /** Parse a top-level:
   *  prog = ifex END */
  private TypeEnv prog() {
    // Currently only supporting exprs
    Node res = stmt();
    if( skipWS() != -1 ) res = con(err_ctrl("Syntax error; trailing junk"));
    _e._scope.add_def(res);     // Hook, so not deleted
    _gvn.iter();    // Pessimistic optimizations; might improve error situation
    res = _e._scope.pop(); // New and improved result

    // TODO: Optimistic Pass Goes Here, to improve error situation

    // Result type
    Type tres = _gvn.type(res);
    kill(res);

    // Gather errors
    Env par = _e._par;
    Ary<String> errs = par.gather_errs(_gvn);
    if( tres instanceof TypeErr ) // Result can be an error, even if no c-flow has an error
      errs = add_err(errs,((TypeErr)tres)._msg); // One more error
    return new TypeEnv(tres,_e,errs);
  }

  /** Parse a list of statements.  A statement is a list of variables to
   *  let-assign, and an ifex for the value.  The variables must not already
   *  exist, and are available in all later statements.
   *  stmt = [id =]* ifex [; stmt]*
   */
  private Node stmt() {
    Ary<String> toks = new Ary<>(new String[1],0);
    while( true ) {
      int oldx = _x;
      String tok = token();  // Scan for 'id = ...'
      if( tok == null ) break;
      if( !peek('=') ) { _x = oldx; break; } // Unwind token parse
      toks.add(tok);
    }
    Node ifex = ifex();
    if( ifex == null ) {
      if( toks._len > 0 ) return con(err_ctrl("Missing ifex after assignment of '"+toks.last()+"'"));
      else return null;
    }
    for( String tok : toks )
      if( _e.lookup(tok)==null ) _e.add(tok,ifex);
      else err_ctrl0("Cannot re-assign ref '"+tok+"'");
    while( peek(';') ) {   // Another expression?
      kill(ifex);          // prior expression result no longer alive in parser
      ifex = stmt();
    }
    return ifex;
  }
  
  /** Parse an if-expression, with lazy eval on the branches.  Assignments to
   *  new variables are allowed in either arm (as-if each arm is in a mini
   *  scope), and variables assigned on all live arms are available afterwards.
   *  ifex = expr ? expr : expr
   */
  private Node ifex() {
    Node expr = expr();
    if( expr == null ) return null; // Expr is required, so missing expr implies not any ifex
    if( !peek('?') ) return expr;   // No if-expression
    try( TmpNode ctrls = new TmpNode() ) {
      int vidx = _e._scope._defs._len; // Set of live variables
      Node ifex = gvn(new IfNode(ctrl(),expr));
      ctrls.add_def(ifex);      // Keep alive, even if 1st Proj kills last use, so 2nd Proj can hook
      set_ctrl(gvn(new ProjNode(ifex,1))); // Control for true branch
      if( ctrls.add_def(expr()) == null ) throw AA.unimpl(); // 1
      ctrls.add_def(ctrl()); // 2 - hook true-side control
      ScopeNode t_scope = _e._scope.split(vidx); // Split out the new vars on the true side
      require(':');
      set_ctrl(gvn(new ProjNode(ifex,0)));
      if( ctrls.add_def(expr()) == null ) throw AA.unimpl(); // 3
      ctrls.add_def(ctrl()); // 4 - hook false-side control
      ScopeNode f_scope = _e._scope.split(vidx); // Split out the new vars on the false side
      set_ctrl(init(new RegionNode(null,ctrls.at(2),ctrls.at(4))));
      _e._scope.common(this,t_scope,f_scope); // Add a PhiNode for all commonly defined variables
      _e._scope.add_def(gvn(new PhiNode(ctrl(),ctrls.at(1),ctrls.at(3)))); // Add a PhiNode for the result
    }
    return _e._scope.pop();
  }
  
  /** Parse an expression, a list of terms and infix operators.  The whole list
   *  is broken up into a tree based on operator precedence.
   *  expr = term [binop term]*
   */
  private Node expr() {
    Node term = term();
    if( term == null ) return null; // Term is required, so missing term implies not any expr
    // Collect 1st fcn/arg pair
    Ary<Node> funs = new Ary<>(new Node[1],0);
    try( TmpNode args = new TmpNode() ) {
      funs.add(null);   args.add_def(term);
      
      // Now loop for binop/term pairs: parse Kleene star of [binop term]
      while( true ) {
        int oldx = _x;
        String bin = token();
        if( bin==null ) break;    // Valid parse, but no more Kleene star
        Node binfun = _e.lookup_filter(bin,2); // BinOp, or null
        if( binfun==null ) { _x=oldx; break; } // Not a binop, no more Kleene star
        term = term();
        if( term == null ) term = con(err_ctrl("missing expr after binary op "+bin));
        funs.add(binfun);  args.add_def(term);
      }
  
      // Have a list of interspersed operators and terms.
      // Build a tree with precedence.
      int max=-1;                 // First find max precedence.
      for( Node n : funs ) if( n != null ) max = Math.max(max,n.op_prec());
      // Now starting at max working down, group list by pairs into a tree
      while( args._defs._len > 1 ) {
        for( int i=1; i<funs.len(); i++ ) { // For all ops of this precedence level, left-to-right
          Node fun = funs.at(i);
          assert fun.op_prec() <= max;
          if( fun.op_prec() < max ) continue; // Not yet
          args.set_def(i-1,gvn(new CallNode(ctrl(),fun,args.at(i-1),args.at(i))),_gvn);
          funs.remove(i);  args.remove(i);  i--;
        }
        max--;
      }
      return args.del(0);       // Return the remaining expression
    }
  }

  /** Parse a function call, or not
   *  term = nfact                // No function call
   *  term = nfact ( [expr,]* )+  // One or more function calls in a row, each set of args are delimited
   *  term = nfact nfact*         // One function call, all the args listed
   */
  private Node term() {
    Node fun = nfact(), arg;         // nfactor
    if( fun == null ) return null;   // No term at all
    if( skipWS() == -1 ) return fun; // Just the original term
    // Function application; parse out the argument list
    try( CallNode args = new CallNode() ) {
      args.add_def(ctrl());
      args.add_def(fun);
      if( peek('(') ) {               // Traditional fcn application
        if( (arg=stmt()) != null ) {  // Check for a no-arg fcn call
          args.add_def(arg);          // Add first arg
          while( peek(',') ) {        // Gather comma-separated args
            if( (arg=stmt()) == null ) arg = con(err_ctrl("Missing argument in function call"));
            args.add_def(arg);
          }
        }
        require(')'); 
        if( _gvn.type(fun).ret() == null )
          return con(err_ctrl("A function is being called, but "+_gvn.type(fun)+" is not a function type"));
      } else {                  // lispy-style fcn application
        // TODO: Unable resolve ambiguity with mixing "(fun arg0 arg1)" and
        // "fun(arg0,arg1)" argument calls.  Really having trouble with parsing
        // "1-2", where "1" parses in the function position and "-2" is a uniop
        // '-' applied to a 2: "-(2)".  This parses as the function "1" and its
        // single arg "-(2)" - but "1" is not a function.
        return args.del(1);     // No function call
        //while( (arg = stmt()) != null ) // While have args
        //  args.add_def(arg);            // Gather WS-separate args
        //if( args.len()==1 ) return fun; // Not a function call
      }
      Node call = gvn(args);    // No syntax errors; flag Call not auto-close
      if( _gvn.type(call)._type==Type.TERROR ) {
        kill(call);
        return con(err_ctrl("Argument mismatch in call to " + fun));
      }
      return call;
    }
  }
  
  /** Parse any leading unary ops before a factor
   *  nfact = fact | uniop nfact 
   */
  private Node nfact() {
    int oldx = _x;
    String uni = token();
    if( uni!=null ) { // Valid parse
      Node unifun = _e.lookup_filter(uni,1);
      if( unifun != null && unifun.op_prec() > 0 )  {
        Node arg = nfact(); // Recursive call
        if( arg == null ) { err_ctrl0("Call to unary function '"+uni+"', but missing the one required argument"); return null; }
        return gvn(new CallNode(ctrl(),unifun,arg));
      } else {
        _x=oldx;                // Unwind token parse and try again for a factor
        if( unifun != null ) kill(unifun); // Might be made new by the lookup_filter, but then no-good
      }
    }
    return fact();
  }

  /** Parse a factor, a leaf grammar token
   *  fact = num       // number
   *  fact = (stmt)    // General statement called recursively
   *  fact = {binop}   // Special syntactic form of binop; no spaces allowed; returns function constant
   *  fact = {uniop}   // Special syntactic form of uniop; no spaces allowed; returns function constant
   *  fact = {func}    // Anonymous function declaration
   *  fact = id        // variable lookup, NOT a binop or uniop but might be e.g. function-valued, including un-/binops as values
   */
  private Node fact() {
    if( skipWS() == -1 ) return null;
    byte c = _buf[_x];
    if( '0' <= c && c <= '9' ) return con(number());
    int oldx = _x;
    if( peek('(') ) {           // a nested statement
      Node s = stmt();
      if( s==null ) { _x = oldx; return null; } // A bare "()" pair is not a statement
      require(')');
      return s;
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
    if( var == null )
      return con(err_ctrl("Unknown ref '"+tok+"'"));
    // Disallow uniop and binop functions as factors.
    if( var.op_prec() > 0 ) { _x = oldx; return null; }
    return var;
  }

  /** Parse an anonymous function; the opening '{' already parsed.  After the
   *  '{' comes an optional list of arguments and a '->' token.
   *  func = { [[id]* ->]? stmt }
   */
  private Node func() {
    int oldx = _x;
    Ary<String> ids = new Ary<>(new String[1],0);
    while( true ) {
      String tok = token();
      if( tok == null ) { ids.clear(); _x=oldx; break; } // not a "[id]* ->"
      if( tok.equals("->") ) break;
      ids.add(tok);
    }
    FunNode fun = (FunNode)init(new FunNode(TypeFun.any(ids._len)));
    Node old_ctrl = ctrl();
    set_ctrl(fun);
    try( Env e = new Env(_e) ) {// Nest an environment for the local vars
      _e = e;                   // Push nested environment
      int cnt=0;                // Add parameters to local environment
      for( String id : ids )  _e.add(id,init(new ParmNode(++cnt,id,fun,con(Type.SCALAR))));
      Node rpc = _e.add(" rpc ",init(new ParmNode(ids._len+1,"$rpc",fun,con(TypeInt.TRUE))));
      Node rez = stmt();        // Parse function body
      Node ret = e._ret = gvn(new RetNode(fun,rez,rpc,1));
      _e = _e._par;             // Pop nested environment
      require('}');
      return ret;               // Return function
    } finally {
      set_ctrl(old_ctrl);
    }
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
    err_ctrl0("Expected '"+c+"' but "+(_x>=_buf.length?"ran out of text":"found '"+(char)(_buf[_x])+"' instead"));
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

  public Node gvn (Node n) { return n==null ? null : _gvn.xform(n); }
  public Node init(Node n) { return n==null ? null : _gvn.init (n); }
  public void kill(Node n) { if( n._uses._len==0 ) _gvn.kill(n); }
  public Node ctrl() { return _e._scope.get(" control "); }
  // Set and return a new control
  private Node set_ctrl(Node n) { return _e._scope.update(" control ",n,_gvn); }

  private Node con( Type t ) { return _gvn.con(t); }

  // Whack current control with a syntax error
  private TypeErr err_ctrl(String s) { return TypeErr.make(err_ctrl0(s)); }
  private String err_ctrl0(String s) {
    String msg = errMsg(s);
    set_ctrl(gvn(new ErrNode(ctrl(),msg)));
    return msg;
  }

  public static Ary<String> add_err( Ary<String> errs, String msg ) {
    if( errs == null ) errs = new Ary<>(new String[1],0);
    errs.add(msg);
    return errs;
  }

  // Build a string of the given message, the current line being parsed,
  // and line of the pointer to the current index.
  public String errMsg(String s) {
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
  // Handy for the debugger to print 
  @Override public String toString() { return new String(_buf,_x,_buf.length-_x); }

}
