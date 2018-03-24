package com.cliffc.aa;

import java.text.NumberFormat;
import java.text.ParsePosition;
import java.util.ArrayList;
  
/** an implementation of language AA
 */

public class Parse {
  private final String _src;            // Source for error messages; usually a file name
  private final Env _e;                 // Lookup context
  private final byte[] _buf;            // Bytes being parsed
  private int _x;                       // Parser index
  private int _line;                    // Zero-based line number

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
  }
  // Parse the string in the given lookup context, and return an executable program
  Prog go( ) {
    Prog res = top();
    if( skipWS() != -1 ) throw err("Syntax error; trailing junk");
    return res;
  }

  /** Parse a top-level */
  private Prog top() {
    // Currently only supporting exprs
    return expr0();
  }

  // -(3  ) ==> ok, e0:=e1;        e1:unary:-   e2:3
  // -(3,1) ==> ok, e0:=e1(e0,e0); e1:binop:- ( e2:3 , e2:1 )
  // - 3    ==> ok, e0:=e1;        e1:unary:-   e2:3
  
  // +(3  ) ==>err, e0:=e1;        e1:unary:+   e2:3
  // +(3,1) ==> ok, e0:=e1(e0,e0); e1:binop:+ ( e2:3 , e2:1 )
  // + 3    ==>err, e0:=e1;        e1:unary:+   e2:3
  
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
  private Prog expr0() {
    Prog fun = expr1(), arg;
    if( fun == null ) return null;   // No expression at all
    if( skipWS() == -1 ) return fun; // Just the original expression
    // Function application; parse out the argument list
    ArrayList<Prog> args = new ArrayList<>();
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
      if( args.isEmpty() ) return fun; // Not a function call
    }
    Prog[] pargs = args.toArray(new Prog[args.size()]);
    
    // Limit function choices to those matching arg count and type
    Type[] ts = new Type[pargs.length];
    for( int i=0; i<ts.length; i++ ) ts[i] = pargs[i]._t;
    Type funt = TypeFun.make(fun._t.funame(),null,TypeTuple.make(ts),Type.SCALAR).meet(fun._t);
    if( funt == Type.ALL || funt == Type.SCALAR )
      throw err("Either "+fun+" is not a function, or is being called with "+ts.length+" args but expects a different number");
    fun._t = funt; // Tighten allowed functions
    return new ProgApply(fun,pargs);
  }
  
  // associates based on operator precedence across whole list of op-expr-op-expr...
  // e1 := [unop] e2 [binop e2]* 
  private Prog expr1() {
    ArrayList<Type> funs = new ArrayList<>();
    ArrayList<Prog> args = new ArrayList<>();

    // Parse an optional unary function
    int oldx = _x;
    String un = token();
    Type unfun = un==null ? null : _e.lookup(un, TypeFun.any(un,1)); // Unary arg-count functions
    if( unfun==null ) { un=null; _x=oldx; } // Reset if no leading unary function

    // Parse first required e2 after option unary func
    Prog e2 = expr2();
    if( e2 == null )  // not a unary fcn application, so return the fcns if any
      return unfun == null ? null : new ProgCon(unfun);
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
    while( args.size() > 1 || funs.get(0) != null ) {
      for( int i=0; i<funs.size(); i++ ) { // For all ops of this precedence level, left-to-right
        Type t = funs.get(i);
        if( t != null && t.op_prec()==max ) {
          Prog pfun = new ProgCon(t);
          if( i==0 ) {          // Unary op?
            args.set(i,new ProgApply(pfun,args.get(i))); // Apply unary op
            funs.set(i,null);   // Clear unary slot
          } else {              // Binary: build tree node, reduce list length
            args.set(i-1,new ProgApply(pfun,args.get(i-1),args.get(i)));
            funs.remove(i);  args.remove(i);  i--;
          }
        }
      }
      max--;
    }
    Type fun = funs.get(0);
    Prog arg = args.get(0);
    return fun==null ? arg : new ProgApply(new ProgCon(fun),arg); // Apply any left over unary op
  }

  // optional lookup restricted to type/class of e3
  // e2 := e3 [. var] 
  private Prog expr2() {
    Prog e3 = expr3();
    if( peek('.') ) throw AA.unimpl();
    return e3;
  }
  
  // e3 := var        // Basic vars pre-exist for primitives
  // e3 := num
  // e3 := (e0)       // grouping
  private Prog expr3() {
    int oldx = _x;
    if( skipWS() == -1 ) return null;
    if( peek('(') ) {
      Prog e0 = expr0();
      if( e0==null ) { _x = oldx; return null; } // A bare "()" pair is not an e3
      require(')'); return e0;
    }
    byte c = _buf[_x];
    if( '0' <= c && c <= '9' ) return new ProgCon(number());
    String tok = token();
    if( tok == null ) return null;
    Type var = _e.lookup(tok,Type.ANY);
    if( var == null ) { _x = oldx; return null; }
    return var.canBeConst() ? new ProgCon(var) : new ProgVar(tok,var);
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
