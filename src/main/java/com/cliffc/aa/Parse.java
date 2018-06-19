package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.Bits;
import com.cliffc.aa.util.SB;

import java.text.NumberFormat;
import java.text.ParsePosition;
import java.util.BitSet;

/** an implementation of language AA
 *
 *  GRAMMAR:
 *  prog = stmt END
 *  stmt = [id[@type]? =]* ifex [; stmt]* // ids must not exist, and are available in later statements
 *  ifex = expr ? expr : expr   // trinary logic
 *  expr = term [binop term]*   // gather all the binops and sort by prec
 *  term = tfact                // No function call
 *  term = tfact ( [stmt,]* )+  // One or more function calls in a row, args are delimited
 // *  term = tfact tfact*         // One function call, all the args listed
 *  tfact= nfact[@type]?        // Optional type after a nfact
 *  nfact= uniop* fact          // Zero or more uniop calls over a fact
 *  fact = id                   // variable lookup
 *  fact = num                  // number
 *  fact = "str"                // string
 *  fact = (stmt)               // General statement parsed recursively
 *  fact = {func}               // Anonymous function declaration
 *  fact = {binop}              // Special syntactic form of binop; no spaces allowed; returns function constant
 *  fact = {uniop}              // Special syntactic form of uniop; no spaces allowed; returns function constant
 *  binop= +-*%&|/<>!=          // etc; primitive lookup; can determine infix binop at parse-time
 *  uniop=  -!~                 // etc; primitive lookup; can determine infix uniop at parse-time
 *  func = { [[id]* ->]? stmt } // Anonymous function declaration
 *  str  = [.\%]*               // String contents; \t\n\r\% standard escapes
 *  str  = %[num]?[.num]?fact   // Percent escape embeds a 'fact' in a string; "name=%name\n"
 *  type = tcon                 // Types are a tcon or a tfun
 *  type = tfun
 *  tcon = int, int[1,8,16,32,64], flt, flt[32,64], real, str
 *  tfun = {[[type]* ->]? type }// Function types mirror func decls
 */

public class Parse {
  private final String _src;            // Source for error messages; usually a file name
  private Env _e;                       // Lookup context; pushed and popped as scopes come and go
  private final byte[] _buf;            // Bytes being parsed
  private int _x;                       // Parser index
  private int _line;                    // Zero-based line number
  private GVNGCM _gvn;                  // Pessimistic types
  
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
    if( res == null ) res = con(TypeErr.ALL);
    _e._scope.add_def(ctrl());  // Hook, so not deleted
    _e._scope.add_def(res);     // Hook, so not deleted
    // Delete names at the top scope before final optimization.
    _e._scope.promote_forward_del_locals(_gvn,null);
    _gvn.iter();    // Pessimistic optimizations; might improve error situation
    // Run GCP from the global top, so we also get all the initial constants
    // and all users of those constants.  
    Env par = _e._par;
    _e._scope.add_def(par._scope); // Hook start control into all the constants
    _gvn.gcp(par._scope);          // Global Constant Propagation
    _e._scope.pop();               // Remove start hook
    res = _e._scope.pop();         // New and improved result
    Node ctrl = _e._scope.pop();   // Exit control

    // Gather errors
    Ary<String> errs = null;
    Type tres = Env.lookup_valtype(res);    // Result type
    if( tres instanceof TypeErr && tres != TypeErr.ALL && tres != TypeErr.ANY )
      errs = add_err(errs,((TypeErr)tres)._msg);
    // Disallow forward-refs as top-level results
    if( res.is_forward_ref() )
      errs = add_err(errs,forward_ref_err(((EpilogNode)res).fun().name()));
    // Hunt for typing errors in the alive code
    assert par._par==null;      // Top-level only
    BitSet bs = new BitSet();
    bs.set(_e._scope._uid);     // Do not walk top-level scope
    if( errs == null ) errs = res.walkerr_def(errs,bs,_gvn);
    if( errs == null ) errs = _e._scope.walkerr_use(null,new BitSet(),_gvn);
    if( errs == null && skipWS() != -1 ) errs = add_err(null,errMsg("Syntax error; trailing junk"));
    kill(res);
    return new TypeEnv(tres,_e,errs);
  }

  /** Parse a list of statements.  A statement is a list of variables to
   *  let-assign, and an ifex for the value.  The variables must not already
   *  exist, and are available in all later statements.
   *  stmt = [id[@type]? =]* ifex [; stmt]*
   */
  private Node stmt() {
    Ary<String> toks = new Ary<>(new String[1],0);
    Ary<Type  > ts   = new Ary<>(new Type  [1],0);
    while( true ) {
      int oldx = _x;
      String tok = token();  // Scan for 'id = ...'
      if( tok == null ) break;
      Type t = null;
      if( peek('@') && (t=type())==null ) return con(err_ctrl("Missing type"));
      if( !peek('=') ) { _x = oldx; break; } // Unwind token parse
      toks.add(tok);
      ts  .add(t  );
    }
    Node ifex = ifex();
    if( ifex == null )
      return toks._len == 0 ? null
        : con(err_ctrl("Missing ifex after assignment of '"+toks.last()+"'"));
    // Honor all type requests, all at once
    for( Type t : ts ) if( t != null ) ifex = gvn(new TypeNode(t,ifex,errMsg()));
    for( String tok : toks ) {
      Node n = _e.lookup(tok);
      if( n==null ) {           // Token not already bound to a value
        _e.add(tok,ifex);       // Bind token to a value
      } else { // Handle forward referenced function definitions
        if( n.is_forward_ref() ) ((EpilogNode)n).merge_ref_def(_gvn,tok,(EpilogNode)ifex);
        else err_ctrl0("Cannot re-assign ref '"+tok+"'");
      }
    }
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
      set_ctrl(gvn(new CProjNode(ifex,1))); // Control for true branch
      if( ctrls.add_def(expr()) == null ) throw AA.unimpl(); // 1
      ctrls.add_def(ctrl()); // 2 - hook true-side control
      ScopeNode t_scope = _e._scope.split(vidx); // Split out the new vars on the true side
      require(':');
      set_ctrl(gvn(new CProjNode(ifex,0)));
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
        Node binfun = _e.lookup_filter(bin,_gvn,2); // BinOp, or null
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
          Node call = do_call(new CallNode(errMsg(),ctrl(),fun,args.at(i-1),args.at(i)));
          args.set_def(i-1,call,_gvn);
          funs.remove(i);  args.remove(i);  i--;
        }
        max--;
      }
      return args.del(0);       // Return the remaining expression
    }
  }

  /** Parse a function call, or not
   *  term = tfact                // No function call
   *  term = tfact ( [expr,]* )+  // One or more function calls in a row, each set of args are delimited
   *  term = tfact tfact*         // One function call, all the args listed
   */
  private Node term() {
    Node fun = tfact(), arg;         // tfactor
    while( fun != null ) {           // Have tfact?
      if( skipWS() == -1 ) return fun; // Just the original term
      // Function application; parse out the argument list
      try( CallNode args = new CallNode(errMsg()) ) {
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
        Type t = _gvn.type(fun);
        if( !t.is_fun_ptr() )
          return con(err_ctrl("A function is being called, but "+t+" is not a function type"));
        fun = do_call(args); // No syntax errors; flag Call not auto-close, and go again
      }
    }
    return null;
  }
  
  /** Parse a type after a fact
   *  tfact = nfact[@type]
   */
  private Node tfact() {
    Node n = nfact();
    return (n!=null && peek('@')) ? gvn(new TypeNode(type(),n,errMsg())) : n;
  }
  
  /** Parse any leading unary ops before a factor
   *  nfact = fact | uniop nfact
   */
  private Node nfact() {
    int oldx = _x;
    String uni = token();
    if( uni!=null ) { // Valid parse
      Node unifun = _e.lookup_filter(uni,_gvn,1);
      if( unifun != null && unifun.op_prec() > 0 )  {
        Node arg = nfact(); // Recursive call
        if( arg == null ) { err_ctrl0("Call to unary function '"+uni+"', but missing the one required argument"); return null; }
        return do_call(new CallNode(errMsg(),ctrl(),unifun,arg));
      } else {
        _x=oldx;                // Unwind token parse and try again for a factor
      }
    }
    return fact();
  }

  /** Parse a factor, a leaf grammar token
   *  fact = num       // number
   *  fact = "string"  // string
   *  fact = (stmt)    // General statement parsed recursively
   *  fact = {binop}   // Special syntactic form of binop; no spaces allowed; returns function constant
   *  fact = {uniop}   // Special syntactic form of uniop; no spaces allowed; returns function constant
   *  fact = {func}    // Anonymous function declaration
   *  fact = id        // variable lookup, NOT a binop or uniop but might be e.g. function-valued, including un-/binops as values
   */
  private Node fact() {
    if( skipWS() == -1 ) return null;
    byte c = _buf[_x];
    if( '0' <= c && c <= '9' ) return con(number());
    if( '"' == c ) return con(string());
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
    if( var == null ) // Assume any unknown ref is a forward-ref of a recursive function
      return _e.add(tok,gvn(EpilogNode.forward_ref(_gvn,_e._scope,tok)));
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
    Node old_ctrl = ctrl();
    FunNode fun = init(new FunNode(ids._len,old_ctrl));
    try( Env e = new Env(_e) ) {// Nest an environment for the local vars
      _e = e;                   // Push nested environment
      set_ctrl(fun);            // New control is function head
      int cnt=0;                // Add parameters to local environment
      for( String id : ids )  _e.add(id,gvn(new ParmNode(cnt++,id,fun,con(Type.SCALAR))));
      Node rpc = gvn(new ParmNode(-1,"rpc",fun,_gvn.con(TypeRPC.ALL_CALL)));
      Node rez = stmt();        // Parse function body
      Node epi = gvn(new EpilogNode(ctrl(),rez,rpc,fun));
      require('}');             // 
      _e = _e._par;             // Pop nested environment
      set_ctrl(old_ctrl);       // Back to the pre-function-def control
      return epi;               // Return function; close-out and DCE 'e'
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
    if( n instanceof Long   ) return TypeInt.con(n.  longValue());
    if( n instanceof Double ) return TypeFlt.con(n.doubleValue());
    throw new RuntimeException(n.getClass().toString()); // Should not happen
  }

  /** Parse a String; _x is at '"'.
   *  str  = [.\%]*               // String contents; \t\n\r\% standard escapes
   *  str  = %[num]?[.num]?fact   // Percent escape embeds a 'fact' in a string; "name=%name\n"
   */
  private Type string() {
    int oldx = ++_x;
    byte c;
    while( (c=_buf[_x++]) != '"' ) {
      if( c=='%' ) throw AA.unimpl();
      if( c=='\\' ) throw AA.unimpl();
      if( _x == _buf.length ) return err_ctrl("Unterminated string");
    }
    return TypeStr.make(0,new String(_buf,oldx,_x-oldx-1));
  }

  /** Parse a type
   *  type = tcon                 // Types are a tcon or a tfun
   *  type = tfun
   *  tcon = int, int[1,8,16,32,64], flt, flt[32,64], real, str
   *  tfun = {[[type]* ->]? type }// Function types mirror func decls
   */
  private Type type() {
    Type t = type0();
    return (t==null || t==TypeErr.ANY) ? err_ctrl("missing type") : t;
  }
  // Type or null or TypeErr.ANY for '->' token
  private Type type0() {
    if( !peek('{') ) {          // Primitive type, not function type
      int oldx = _x;
      String tok = token();
      if( tok==null ) return null;
      if( tok.equals("->") ) return TypeErr.ANY;
      Type t = _e.lookup_type(tok);
      if( t==null ) _x = oldx;  // Unwind if not a primitive type
      return t;
    }
    Ary<Type> ts = new Ary<>(new Type[1],0);  Type t;
    while( (t=type0()) != null && t != TypeErr.ANY  )
      ts.add(t);                // Collect arg types
    Type ret;
    if( t==TypeErr.ANY ) {      // Found ->, expect return type
      ret = type0();
      if( ret == null ) return null;
    } else {                    // Allow no-args and simple return type
      if( ts._len != 1 ) return null;
      ret = ts.pop();           // Get single return type
    }
    require('}');
    return TypeTuple.make_fun_ptr(TypeFun.make(TypeTuple.make(ts.asAry()),ret,Bits.FULL));
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
  private static boolean isOp0   (byte c) { return "!#$%*+,-.;:=<>?@^[]~/&".indexOf(c) != -1; }
  private static boolean isOp1   (byte c) { return isOp0(c); }

  public Node gvn (Node n) { return n==null ? null : _gvn.xform(n); }
  private <N extends Node> N init( N n ) { return n==null ? null : _gvn.init (n); }
  private void kill( Node n ) { if( n._uses._len==0 ) _gvn.kill(n); }
  public Node ctrl() { return _e._scope.get(" control "); }
  // Set and return a new control
  private void set_ctrl(Node n) { _e._scope.update(" control ",n,_gvn); }

  private Node con( Type t ) { return _gvn.con(t); }

  private Node do_call( Node call0 ) {
    Node call = gvn(call0);
    // Primitives frequently inline immediately, and do not need following
    // control/data projections.
    if( !(call instanceof CallNode)) return call;

    call.add_def(call);         // Hook, so not deleted after 1st use
    set_ctrl(gvn(new CProjNode(call,0)));
    Node ret = gvn(new ProjNode(call,1));
    ret.add_def(ret);           // Hook, so not deleted when call goes
    if( call.pop()._uses._len==0 )
      _gvn.kill(call);
    return ret.pop();
  }

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
  // Make a private clone just for delayed error messages
  private Parse( Parse P ) {
    _src = P._src;  
    _buf = P._buf;
    _x   = P._x;
    _line= P._line;
    _e   = null;  _gvn = null;  _nf  = null;  _pp  = null;  _str = null;
  }
  // Delayed error message
  private Parse errMsg() { return new Parse(this); }

  // Polite error message for mismatched types
  public String typerr( Type t0, Type t1 ) {
    return t0.is_forward_ref() // Forward/unknown refs as args to a call report their own error
      ? forward_ref_err(FunNode.name(((TypeTuple)t0).get_fun().fidx()))
      : errMsg(t0+" is not a "+t1);
  }

  // Standard mis-use of a forward-ref error (assumed to be a forward-decl of a
  // recursive function; all other uses are treated as an unknown-ref error).
  private String forward_ref_err(String name) { return errMsg("Unknown ref '"+name+"'"); }
  // Build a string of the given message, the current line being parsed,
  // and line of the pointer to the current index.
  public String errMsg(String s) {
    if( s.charAt(0)=='\n' ) return s;
    // find line start
    int a=_x;
    while( a > 0 && _buf[a-1] != '\n' ) --a;
    if( _buf[a]=='\r' ) a++; // do not include leading \n or \n\r
    // find line end
    int b=_x;
    while( b < _buf.length && _buf[b] != '\n' ) b++;
    if( b < _buf.length ) b--; // do not include trailing \n or \n\r
    // error message
    SB sb = new SB().p('\n').p(_src).p(':').p(_line).p(':').p(s).p('\n');
    sb.p(new String(_buf,a,b-a)).p('\n');
    int line_start = 0;
    for( int i=line_start; i<_x; i++ )
      sb.p(' ');
    return sb.p("^\n").toString();
  }
  // Handy for the debugger to print 
  @Override public String toString() { return new String(_buf,_x,_buf.length-_x); }

}
