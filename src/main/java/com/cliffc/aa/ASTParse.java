package com.cliffc.aa;

import com.cliffc.aa.ast.*;
import com.cliffc.aa.node.PrimNode;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.Util;

import java.text.NumberFormat;
import java.text.ParsePosition;
import java.util.BitSet;

import static com.cliffc.aa.AA.ARG_IDX;
import static com.cliffc.aa.AA.TODO;

/*** an implementation of language AA
 */

public class ASTParse {
  private final String _src;    // Source for error messages; usually a file name
  private final String _prog;   // Program source
  private final byte[] _buf;    // Bytes being parsed
  private int _x;               // Parser index

  // Fields strictly for Java number parsing
  private static final NumberFormat _nf = NumberFormat.getInstance();
  private static final ParsePosition _pp = new ParsePosition(0);
  static { _nf.setGroupingUsed(false); }


  ASTParse( String src, String prog ) {
    _src = src;
    _prog = prog;
    _buf = prog.getBytes();
    _x   = 0;
  }

  // Handy for the debugger to print
  @Override public String toString() { return new String(_buf,_x,_buf.length-_x); }


  public ErrMsg prog(Env e) {
    AST rez = stmts();
    if( rez == null )
      return ErrMsg.syntax(null,"Not a program?");
    if( skipWS() != -1 ) return ErrMsg.trailingjunk(null);
    // Walk for Nodes
    Root prog = new Root(rez);
    prog.nodes(e);
    // Close file scope; no more program text in this file, so no more fields to add.
    e._scope.stk().close();
    return null;
  }

  /** Parse a list of statements; final semicolon is optional.
   *  stmts= [tstmt or stmt] [; stmts]*[;]?
   */
  private AST stmts() {
    LetRec stmt = stmt(), last=null;
    while( stmt != null ) {
      if( !peek(';') ) return stmt;
      last = stmt;
      stmt = stmt();
      last.addBody(stmt);
      if( stmt == null ) {
        if( peek(';') ) { _x--; }   // Ignore empty statement
      }
      stmt = last;
    }
    return last;
  }

  /** A type-statement assigns a type to a type variable.  */
  private AST tstmt() {
    return null;
  }

  /** A statement is a list of variables to final-assign or re-assign... */
  private LetRec stmt() {
    if( peek('^') ) {           // Early function exit
      throw TODO();
    }

    // Gather ids in x = y = z = ....
    Ary<String> toks = new Ary<>(new String[1],0);
    Ary<Type  > ts   = new Ary<>(new Type  [1],0);
    Ary<ASTParse > badfs= new Ary<>(new ASTParse [1],0);
    Ary<ASTParse > badts= new Ary<>(new ASTParse [1],0);
    BitSet rs = new BitSet();
    boolean default_nil = false;
    while( true ) {
      skipWS();
      int oldx = _x;            // Unwind token parse point
      ASTParse badf = errMsg(); // Capture location in case of field error
      String tok = token();     // Scan for 'id = ...'
      if( tok == null ) break;  // Out of ids
      if( !isAlpha0((byte)tok.charAt(0)) ) { _x=oldx; break; } // not a "[id]* ->"
      int oldx2 = _x;           // Unwind assignment flavor point
      Type t = null;
      // x  =: ... type  assignment, handled before we get here
      // x  =  ... final assignment
      // x :=  ... var   assignment
      // x : type  = ... typed final assignment
      // x : type := ... typed var   assignment
      // x : nontype = ... error, missing type
      // p? x : nontype ... part of trinary
      ASTParse badt = errMsg();  // Capture location in case of type error
      if( peek(":=") ) _x=oldx2; // Avoid confusion with typed assignment test
      else if( peek(':') && (t=type())==null ) { // Check for typed assignment
        if( testIf() ) _x = oldx2; // Grammar ambiguity, resolve p?a:b from a:int
        else err_ctrl0("Missing type after ':'");
      }
      if( peek(":=") ) rs.set(toks._len);              // Re-assignment parse
      else if( !peek_not('=','=') ) {                  // Not any assignment
        // For structs, allow a bare id as a default def of nil
        if( false /*lookup_current_scope_only && ts.isEmpty() && (peek(';') || peek('}') ||
        // These next two tokens are syntactically invalid, but a semi-common error situation:
        //   @{ fld;fld;fld;...  fld );  // Incorrect closing paren.  Go ahead and allow a bare id.
                                                                  peek(']') || peek(')' )) */) {
          _x--;                 // Push back statement end
          default_nil=true;     // Shortcut def of nil
          rs.set(toks._len);    // Shortcut mutable
        } else {
          _x = oldx; // Unwind the token parse, and try an expression parse
          break;     // Done parsing assignment tokens
        }
      }

      toks .add(tok.intern());
      ts   .add(t);
      badfs.add(badf);
      badts.add(badt);
    }

    // Normal statement value parse
    AST ifex = ifex();         // Parse an expression for the statement value
    // Check for no-statement after start of assignment, e.g. "x = ;"
    if( ifex == null ) {        // No statement?
      if( toks._len == 0 ) return null;
      ifex = err_ctrl2("Missing ifex after assignment of '"+toks.last()+"'");
    }

    if( toks._len==0 ) return new LetRec(ifex);

    // Assign
    return new LetRec(toks,ifex);
  }

  // Ignore the half-scope inside of trinarys
  private boolean testIf() {
    return false;
  }




  /** Parse an if-expression, with lazy eval on the branches.  Assignments to
   *  new variables are allowed in either arm (as-if each arm is in a mini
   *  scope), and variables assigned on all live arms are available afterwards.
   *  ifex = expr [? stmt [: stmt]]
   */
  private AST ifex() {
    AST expr = apply();
    if( expr == null ) return null; // Expr is required, so missing expr implies not any ifex
    if( !peek('?') ) return expr;   // No if-expression
    throw TODO();
  }

  /** Parse a lisp-like function application.  To avoid the common bug of
   *  forgetting a ';', these must be on the same line.
      apply = expr
      apply = expr expr*
   */
  private AST apply() {
    AST expr = expr();
    if( expr == null ) return null;
    while( true ) {
      skipWS();
      int oldx = _x;
      AST arg = expr();
      if( arg==null ) return expr;
      expr = new Call(null,null,null,dynCall(),arg,expr);
    }
  }



  /** Parse an expression, a series of terms separated by binary operators.
   *  Precedence is encoded in the PrimNode.PRECEDENCE table, and reflects
   *  here by the expr# recursive calls.
   *    expr = term [binop term]*
   *  Calls out for the precedence, starting high and working down low.
   *    expr  = expr9 [binop9 expr9]
   *    expr9 = expr8 [binop8 expr8]
   *    ...
   *    expr2 = expr1 [binop2 expr1]
   *    expr1 = term  [binop1 term ]
   */
  private AST expr() {
    skipWS();         // Invariant: WS already skipped before & after each expr depth
    return _expr(1);
  }

  // Invariant: WS already skipped before & after each _expr depth
  private AST _expr(int prec) {
    int lhsx = _x;              // Invariant: WS already skipped
    AST lhs = _expr_higher(prec);
    if( lhs==null ) return null;
    while( true ) {             // Kleene star at this precedence
      // Look for a binop at this precedence level
      int opx = _x;             // Invariant: WS already skipped
      String tok = token0();
      Oper binop = Oper.bin_op(tok,prec);
      if( binop==null ) { _x=opx; return lhs; }
      throw TODO();
    }
  }
  // Get an expr at the next higher precedence, or a term, or null
  private AST _expr_higher( int prec ) {
    return prec+1 == Oper.MAX_PREC ? term() : _expr(prec+1);
  }


  /** Any number field-lookups or function applications, then an optional assignment
   *    term = id++ | id--
   *    term = uniop term
   *    term = bopen term bclose
   *    term = tfact [tuple | .field | [.field[:]=stmt | .field++ | .field-- | e]
   *    term = tfact bopen stmts bclose      // if bopen/bclose is arity-2 e.g. ary[idx]
   *    term = tfact bopen stmts bclose stmt // if bopen/bclose is arity-3 e.g. ary[idx]=val
   */
  // Invariant: WS already skipped before & after term
  private AST term() {
    AST n;
    int oldx = _x;

    // Check for id++ / id--
    // These are special forms (for now) because they side-effect.
    String tok = token();
    if( tok != null ) {
      if( peek("++") ) throw TODO();
      if( peek("--") ) throw TODO();
    }

    // Check for prefix ops; no leading expr and require a trailing expr;
    // balanced ops require a trailing balanced close.
    Oper op = Oper.pre_bal(tok,false);
    if( op != null ) {
      throw TODO();
    } else {
      // Normal leading term
      _x = oldx;                // Roll back and try again
      n = tfact();
      if( n == null ) return null;
    }

    // Repeat until not a term.  Binary expressions have precedence, parsed in expr()
    while( true ) {             // Repeated application or field lookup is fine
      skipWS();                 //
      if( peek('.') ) {         // Field?
        throw TODO();
      } else if( peek('(') ) {  // Attempt a function-call
        throw TODO();
      } else {
        // Check for balanced op with a leading term, e.g. "ary [ idx ]" or
        // "ary [ idx ]= val".
        oldx = _x;                         // Token start
        String tok0 = token0();
        if( tok0!=null && Oper.is_open(tok0) ) {
          throw TODO();
        }
      }
      // Not a field, not a function call, not a balanced op, so not a term
      _x = oldx;                // Roll back
      break;
    }

    return n;
  }

  /** Parse an optionally typed factor
   *  tfact = fact[:type]
   */
  private AST tfact() {
    AST fact = fact();
    if( fact==null ) return null;
    if( !peek(':') ) return fact;
    throw TODO();
  }

  /** Parse a factor, a leaf grammar token
   *  fact = num       // number
   *  fact = "string"  // string
   *  fact = (stmts)   // General statements parsed recursively
   *  fact = (tuple,*) // tuple; first comma required, trailing comma not required
   *  fact = balop+ stmts balop-           // Constructor with initial size
   *    Ex:    [      7      ]             // Array constructor
   *  fact = balop+ stmts[, stmts]* balop- // Constructor with initial elements
   *    Ex:    [      1   ,  2        ]    // Array constructor with initial elements'
   *  fact = {func}    // Anonymous function declaration
   *  fact = @{ stmts }// Anonymous struct declaration, assignments define fields
   *  fact = id        // variable lookup
   */
  private AST fact() {
    if( skipWS() == -1 ) return null;
    byte c = _buf[_x];
    if( isDigit(c) ) return number();
    if( '"' == c ) {
      throw TODO();
    }
    int oldx = _x;
    if( peek1(c,'(') ) {        // a nested statement or a tuple
      int first_arg_start = _x;
      AST s = stmts();
      if( s==null ) { _x = oldx; return null; } // A bare "()" pair is not a statement
      if( peek(')') ) return s;                 // A (grouped) statement
      if( !peek(',') ) return s;                // Not a tuple, probably a syntax error
      _x--;                                     // Reparse the ',' in tuple
      //return tuple(oldx,s,first_arg_start);     // Parse a tuple
      throw TODO();
    }
    // Anonymous function
    if( peek1(c,'{') )
      return func();

    // Anonymous struct
    if( peek2(c,"@{") )
      throw TODO(); // return struct();

    // Check for a valid 'id'
    String tok = token0();
    tok = tok==null ? null : tok.intern();
    if( tok == null || Util.eq("_",tok)) { _x = oldx; return null; }
    if( Util.eq(tok,"=") || Util.eq(tok,"^") )
      { _x = oldx; return null; } // Disallow '=' as a fact, too easy to make mistakes
    // Normal identifier
    return do_ident(tok, oldx);
  }

  private AST do_ident( String tok, int oldx ) {
    return new Ident(tok);
  }

  // A fact hardwired to "$dyn".
  private AST dynLoad() { return new Ident("$dyn");  }
  // Load a Call/Apply field out of a DynTable
  private AST dynCall() { return new AField(dynLoad()); }


  /** Parse an anonymous function; the opening '{' already parsed.  After the
   *  '{' comes an optional list of arguments and a '->' token, and then any
   *  number of statements separated by ';'.
   *  func = { [[id]* ->]? stmts }
   */
  private AST func() {
    int oldx = _x;              // Past opening '{'

    // Incrementally build up the formals, starting with the display
    Ary<Type  > formals= new Ary<>(new Type  []{null,null,null,null});
    Ary<ASTParse> bads = new Ary<>(new ASTParse[ARG_IDX+1]);
    Ary<String> ids    = new Ary<>(new String[]{null,null,"^","$dyn"});

    // Parse arguments
    while( true ) {
      skipWS();
      String tok = token();
      if( tok == null ) { _x=oldx; break; } // not a "[id]* ->"
      if( Util.eq((tok=tok.intern()),"->") ) break; // End of argument list
      if( !isAlpha0((byte)tok.charAt(0)) ) { _x=oldx; break; } // not a "[id]* ->"
      Type t = TypeNil.SCALAR; // Untyped, most generic type
      ASTParse bad = errMsg(); // Capture location in case of type error
      if( peek(':') &&         // Has type annotation?
          (t=type())==null ) { // Get type
        // If no type, might be "{ x := ...}" or "{ fun arg := ...}" which can
        // be valid stmts, hence this may be a no-arg function.
        if( bads._len-1 <= 2 ) { _x=oldx; break; }
        else {
          // Might be: "{ x y z:bad -> body }" which cannot be any stmt.  This
          // is an error in any case.  Treat as a bad type on a valid function.
          err_ctrl0(peek(',') ? "Bad type arg, found a ',' did you mean to use a ';'?" : "Missing or bad type arg");
          t = TypeNil.SCALAR;
          skipNonWS();         // Skip possible type sig, looking for next arg
        }
      }
      if( ids.find(tok) != -1 ) {
        ASTParse badp = errMsg(oldx); // Capture location in case of parameter error
        err_ctrl3("Duplicate parameter name '" + tok + "'", badp);
        tok = (tok+" dup").intern();
      }
      ids.push(tok);
      formals.push(t); // Accumulate args
      bads.add(bad);
    }
    // If this is a no-arg function, we may have parsed 1 or 2 tokens as-if
    // args, and then reset.  Also reset to just the mem & display args.
    if( _x == oldx ) { formals.set_len(ARG_IDX+1);  ids.set_len(ARG_IDX+1); bads.set_len(ARG_IDX+1); }

    // Parse function body
    AST rez = stmts();          // Parse function body
    if( rez == null ) rez = err_ctrl2("Missing function body");
    require('}',oldx-1);      // Matched with opening {}

    return new Lambda(ids,rez);
  }

  // ------------ ERROR RECORDING -----------------------------------------------

  // Make a private clone just for delayed error messages
  private ASTParse( ASTParse P ) {
    _src  = P._src;
    _prog = P._prog;
    _buf  = P._buf;
    _x    = P._x;
  }
  // Delayed error message, just record line/char index and share code buffer
  ASTParse errMsg() { return errMsg(_x); }
  ASTParse errMsg(int x) { ASTParse P = new ASTParse(this); P._x=x; return P; }

  private void err_ctrl0(String s) { err_ctrl3(s,errMsg()); }
  private AST  err_ctrl2( String msg ) { throw TODO(); }
  private void err_ctrl3(String s, ASTParse open) {
    throw TODO();
  }

  // ------------ LEXER -----------------------------------------------

  private String token() { skipWS();  return token0(); }
  // Lexical tokens.  Any alpha, followed by any alphanumerics is a alpha-
  // token; alpha-tokens end with WS or any operator character.  Any collection
  // of the classic operator characters are a token, except that they will break
  // un-ambiguously.
  private String token0() {
    if( _x >= _buf.length ) return null;
    byte c=_buf[_x];  int x = _x;
    if( Oper.isOp0(c) || (c=='_' && _x+1 < _buf.length && Oper.isOp0(_buf[_x+1])) )
      while( _x < _buf.length && Oper.isOp1(_buf[_x]) ) _x++;
    else if( isAlpha0(c) )
      while( _x < _buf.length && isAlpha1(_buf[_x]) ) _x++;
    else return null; // Not a token; specifically excludes e.g. all bytes >= 128, or most bytes < 32
    if( (c==':' || c==',') && _x-x==1 ) // Disallow bare ':' as a token; ambiguous with ?: and type annotations; same for ','
      { _x=x; return null; } // Unwind, not a token
    if( c=='-' && _x-x>2 && _buf[x+1]=='>' ) // Disallow leading "->", confusing with function parameter list end; eg "not={x->!x}"
      _x=x+2;                                // Just return the "->"
    return new String(_buf,x,_x-x);
  }
  static boolean isOp(String s) {
    if( s==null || s.isEmpty() ) return false;
    byte c = (byte)s.charAt(0);
    if( !Oper.isOp0(c) && (c!='_' || !Oper.isOp0((byte)s.charAt(1))) ) return false;
    for( int i=1; i<s.length(); i++ )
      if( !Oper.isOp1((byte)s.charAt(i)) ) return false;
    return true;
  }

  // Parse a number; WS already skipped and sitting at a digit.  Relies on
  // Javas number parsing.
  private AST number() {
    _pp.setIndex(_x);
    Number n = _nf.parse(_prog,_pp);
    _x = _pp.getIndex();
    if( n instanceof Long   ) {
      if( _buf[_x-1]=='.' ) _x--; // Java default parser allows "1." as an integer; pushback the '.'
      long l = n.longValue();
      return con(l==0 ? TypeNil.NIL : TypeInt.con(l));
    }
    if( n instanceof Double ) return con(TypeFlt.con(n.doubleValue()));
    throw new RuntimeException(n.getClass().toString()); // Should not happen
  }

  private AST con( TypeNil t ) {
    return new Const(PrimNode.wrap(t));
  }

  // Parse a small positive integer; WS already skipped and sitting at a digit.
  private int field_number() {
    byte c = _buf[_x];
    if( !isDigit(c) ) return -1;
    _x++;
    int sum = c-'0';
    while( _x < _buf.length && isDigit(c=_buf[_x]) ) {
      _x++;
      sum = sum*10+c-'0';
    }
    return sum;
  }

  Type type() { return null; }


  // Require a closing character (after skipping WS) or polite error
  private void require( char c, int oldx ) {
    if( peek(c) ) return;
    ASTParse bad = errMsg();    // Generic error
    bad._x = oldx;              // Opening point
    err_ctrl3("Expected closing '"+c+"' but "+(_x>=_buf.length?"ran out of text":"found '"+(char)(_buf[_x])+"' instead"),bad);
  }

  // Skip WS, return true&skip if match, false & do not skip if miss.
  private boolean peek( char c ) { return peek1(skipWS(),c); }
  private boolean peek_noWS( char c ) { return peek1(_x >= _buf.length ? -1 : _buf[_x],c); }
  // Already skipped WS & have character;
  // return true & skip if a match, false& do not skip if a miss.
  private boolean peek1( byte c0, char c ) {
    assert c0==-1 || c0== _buf[_x];
    if( c0!=c ) return false;
    _x++;                       // Skip peeked character
    return true;
  }
  // Already skipped WS & have character;
  // return true&skip if match, false & do not skip if miss.
  private boolean peek2( byte c0, String s2 ) {
    if( c0 != s2.charAt(0) ) return false;
    if( _x+1 >= _buf.length || _buf[_x+1] != s2.charAt(1) ) return false;
    _x+=2;                      // Skip peeked characters
    return true;
  }
  private boolean peek( String s ) {
    if( !peek(s.charAt(0)) ) return false;
    if( !peek_noWS(s.charAt(1)) ) {  _x--; return false; }
    return true;
  }
  // Peek 'c' and NOT followed by 'no'
  private boolean peek_not( char c, char no ) {
    byte c0 = skipWS();
    if( c0 != c || (_x+1 < _buf.length && _buf[_x+1] == no) ) return false;
    _x++;
    return true;
  }
  // Match any of these, and return the match or null
  private String peek(String[] toks) {
    for( String tok : toks ) if( peek1(tok) ) return tok;
    return null;
  }
  private boolean peek1(String tok) {
    for( int i=0; i<tok.length(); i++ )
      if( _x+i >= _buf.length || _buf[_x+i] != tok.charAt(i) )
        return false;
    return true;
  }

  /** Advance parse pointer to the first non-whitespace character, and return
   *  that character, -1 otherwise.  */
  private byte skipWS() {
    int oldx = _x;
    while( _x < _buf.length ) {
      byte c = _buf[_x];
      if( c=='/' && _x+1 < _buf.length && _buf[_x+1]=='/' ) { skipEOL()  ; continue; }
      if( c=='/' && _x+1 < _buf.length && _buf[_x+1]=='*' ) { skipBlock(); continue; }
      if( !isWS(c) )
        return c;
      _x++;
    }
    return -1;
  }
  private void skipEOL  () { while( _x < _buf.length && _buf[_x] != '\n' ) _x++; }
  private void skipBlock() { throw TODO(); }
  // Advance parse pointer to next WS.  Used for parser syntax error recovery.
  private void skipNonWS() {
    while( _x < _buf.length && !isWS(_buf[_x]) ) _x++;
  }

  /** Return true if `c` passes a test */
  private static boolean isWS    (byte c) { return c == ' ' || c == '\t' || c == '\n' || c == '\r'; }
  private static boolean isAlpha0(byte c) { return ('a'<=c && c <= 'z') || ('A'<=c && c <= 'Z') || (c=='_'); }
  private static boolean isAlpha1(byte c) { return isAlpha0(c) || ('0'<=c && c <= '9'); }
  private static boolean isJava  (byte c) { return isAlpha1(c) || (c=='$') || (c=='.'); }
  public  static boolean isDigit (byte c) { return '0' <= c && c <= '9'; }

}
