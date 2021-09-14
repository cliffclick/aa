package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.util.*;
import org.jetbrains.annotations.NotNull;

import java.text.NumberFormat;
import java.text.ParsePosition;
import java.util.*;

import static com.cliffc.aa.AA.*;
import static com.cliffc.aa.type.TypeFld.Access;

/** an implementation of language AA
 *
 *  GRAMMAR:
 *  prog = stmts END
 *  stmts= [tstmt|stmt][; stmts]*[;]? // multiple statements; final ';' is optional
 *  tstmt= tvar = :type            // type variable assignment
 *  stmt = [id[:type] [:]=]* ifex  // ids are (re-)assigned, and are available in later statements
 *  stmt = ^ifex                   // Early function exit
 *  ifex = apply [? stmt [: stmt]] // trinary short-circuit logic; missing ":stmt" will default to 0
 *  apply= expr  | expr expr*      // Lisp-like application-as-adjacent
 *  expr = term [binop term]*      // gather all the binops and sort by precedence
 *  term = uniop term              // Any number of prefix uniops
 *  term = id++ | id--             //   then postfix update ops
 *  term = tfact bop+ stmts bop-      // Balanced/split operator arity-2, e.g. array lookup, ary [ idx ]
 *  term = tfact bop+ stmts bop- stmt // Balanced/split operator arity-2, e.g. array assign, ary [ idx ]:= val
 *  term = tfact post              //   A term is a tfact and some more stuff...
 *  post = empty                   // A term can be just a plain 'tfact'
 *  post = (tuple) post            // Application argument list
 *  post = .field post             // Field and tuple lookup
 *  post = .field [:]= stmt        // Field (re)assignment.  Plain '=' is a final assignment
 *  post = .field++ | .field--     // Allowed anytime a := is allowed
 *  post = :type post              // TODO: Add this, remove 'tfact'
 *  tfact= fact[:type]             // Typed fact
 *  fact = id                      // variable lookup
 *  fact = num                     // number
 *  fact = "string"                // string
 *  fact = bop+ stmts bop-         // Balanced/split operator, arity-1, e.g. array decl with size: [ 17 ]
 *  fact = bop+ [stmts,[stmts,]*] bop-  // Balanced/split operator, arity-N, e.g. array decl with elements: [ "Cliff", "John", "Lisa" ]
 *  fact = (stmts)                 // General statements parsed recursively
 *  fact = (tuple)                 // Tuple builder
 *  fact = func                    // Anonymous function declaration
 *  fact = @{ stmts }              // Anonymous struct declaration, assignments define fields
 *  tuple= (stmts,[stmts,])        // Tuple; final comma is optional, first comma is required
 *  binop= +-*%&|/<>!= [ ]=        // etc; primitive lookup; can determine infix binop at parse-time
 *  uniop= -!~# a                  // etc; primitive lookup; can determine infix uniop at parse-time
 *  bop+ = [                       // Balanced/split operator open
 *  bop- = ] ]= ]:=                // Balanced/split operator close
 *  func = { [id[:type]* ->]? stmts} // Anonymous function declaration, if no args then the -> is optional
 *                                 // Pattern matching: 1 arg is the arg; 2+ args break down a (required) tuple
 *  str  = [.\%]*                  // String contents; \t\n\r\% standard escapes
 *  str  = %[num]?[.num]?fact      // Percent escape embeds a 'fact' in a string; "name=%name\n"
 *  type = tcon | tvar | tfun[?] | tstruct[?] | ttuple[?] // Types are a tcon or a tfun or a tstruct or a type variable.  A trailing ? means 'nilable'
 *  tcon = int, int[1,8,16,32,64], flt, flt[32,64], real, str[?]
 *  tfun = {[[type]* ->]? type }   // Function types mirror func declarations
 *  ttuple = ( [[type],]* )        // Tuple types are just a list of optional types;
                                   // the count of commas dictates the length, zero commas is zero length.
                                   // Tuples are always final.
 *  tmod = := | = | ==             // ':=' or '' is r/w, '=' is final, '==' is r/o
 *  tstruct = @{ [id [tmod [type?]];]*}  // Struct types are field names with optional types.
 *  tvar = id                      // Type variable lookup
 */

public class Parse implements Comparable<Parse> {
  private final boolean _prims; // Source allows direct java names
  private final String _src;    // Source for error messages; usually a file name
  private Env _e;    // Lookup context; pushed and popped as scopes come and go
  private final byte[] _buf;    // Bytes being parsed
  private int _x;               // Parser index
  private int _lastNWS;         // Index of last non-white-space char
  private final AryInt _lines;  // char offset of each line
  public final GVNGCM _gvn;     // Pessimistic types

  // Fields strictly for Java number parsing
  private final NumberFormat _nf;
  private final ParsePosition _pp;
  private final String _str;

  Parse( String src, boolean prims, Env env, String str ) {
    _prims = prims;
    _src = src;
    _e   = env;
    _buf = str.getBytes();
    _x   = 0;

    // Set fields strictly for Java number parsing
    _nf = NumberFormat.getInstance();
    _nf.setGroupingUsed(false);
    _pp = new ParsePosition(0);
    _str = str;           // Keep a complete string copy for java number parsing
    _lines = new AryInt();//
    _lines.push(0);       // Line 0 at offset 0
    _gvn = Env.GVN;       // Pessimistic during parsing
  }
  String dump() { return scope().dump(99); }// debugging hook
  String dumprpo() { return Env.START.dumprpo(false,false); }// debugging hook

  /** Parse a top-level:
   *  prog = stmts END */
  public ErrMsg prog() {
    _gvn._opt_mode = GVNGCM.Mode.Parse;
    Node res = stmts();
    if( res == null ) res = con(Type.ANY);
    scope().set_rez(res);  // Hook result
    if( skipWS() != -1 ) return ErrMsg.trailingjunk(this);
    return null;
  }

  /** Parse a list of statements; final semi-colon is optional.
   *  stmts= [tstmt or stmt] [; stmts]*[;]?
   */
  private Node stmts() { return stmts(false); }
  private Node stmts(boolean lookup_current_scope_only) {
    Node stmt = tstmt(), last = null;
    if( stmt == null ) stmt = stmt(lookup_current_scope_only);
    while( stmt != null ) {
      if( !peek(';') ) return stmt;
      last = stmt.keep();
      stmt = tstmt();
      if( stmt == null ) stmt = stmt(lookup_current_scope_only);
      Env.GVN.add_flow(last.unkeep());
      if( stmt == null ) {
        if( peek(';') ) { _x--; stmt=last; }   // Ignore empty statement
      } else if( !last.is_dead() && stmt != last) kill(last); // prior expression result no longer alive in parser
    }
    return last;
  }

  /** A type-statement assigns a type to a type variable.  Type variable
   *  assignments are always final, and can not exist before assignment (hence
   *  a variable cannot have a normal value and be re-assigned as a type
   *  variable).  In addition to allowing 'tvar' to appear in a type expression
   *  a pair of type constructor functions are made: one taking the base type
   *  and returning the same value as the named type, and the other for Structs
   *  taking the unpacked struct fields and returning the named type.  The
   *  ':type' is the type being assigned; a space is allowed between '= :type'.
   *
   *  tstmt = tvar = :type
   */
  private Node tstmt() {
    int oldx = _x;
    String tvar = token();      // Scan for tvar
    if( tvar == null || !peek('=') || !peek(':') ) { _x = oldx; return null; }
    tvar = tvar.intern();
    // Must be a type-variable assignment
    Type t = typev();
    if( t==null ) return err_ctrl2("Missing type after ':'");
    if( peek('?') ) return err_ctrl2("Named types are never nil");
    if( lookup(tvar) != null ) return err_ctrl2("Cannot re-assign val '"+tvar+"' as a type");
    Parse bad = errMsg();
    // Single-inheritance & vtables & RTTI:
    //            "Objects know thy Class"
    // Which means a TypeObj knows its Name.  It's baked into the vtable.
    // Which means TypeObj is named and not the pointer-to-TypeObj.
    // "Point= :@{x,y}" declares "Point" to be a type Name for "@{x,y}".
    Type named = t.set_name((tvar+":").intern()); // Add a name
    ConTypeNode tn = _e.lookup_type(tvar);
    if( tn == null ) {
      // If this is a primitive type, there is no recursion and
      // no special issues.  Make a constructor and be done.
      if( !(t instanceof TypeObj) ) {
        // Make a ConType with a named Type
        tn = (ConTypeNode)gvn(new ConTypeNode(tvar,named,scope()));
        _e.add_type(tvar,tn); // Add a type mapping
        PrimNode cvt = PrimNode.convertTypeName(t,named,bad);
        return _e.add_fun(bad,tvar,gvn(cvt.as_fun(_gvn)));
      }

      // Always wrap Objs with a TypeMemPtr and a unique alias.
      TypeMemPtr tmp = TypeMemPtr.make(BitsAlias.type_alias(BitsAlias.REC),(TypeObj)named);
      // Make a ConType with a named Type
      tn = (ConTypeNode)gvn(new ConTypeNode(tvar,tmp,scope()));
      _e.add_type(tvar,tn); // Add a type mapping
    }

    // A forward-ref ConTypeNode.  Close the cycle.
    tn.def_fref(named,_e);

    // Add a copy of constructor functions.

    // Build a constructor taking a pointer-to-TypeObj - and the associated
    // memory state, i.e.  takes a ptr-to-@{x,y} and returns a ptr to
    // Named:@{x,y}.  This stores a v-table ptr into an object.  The alias#
    // does not change, but a TypeMem[alias#] would now map to the Named
    // variant.
    TypeStruct ts = (TypeStruct)((TypeMemPtr)tn._val)._obj;
    FunPtrNode epi1 = IntrinsicNode.convertTypeName(ts,bad,_gvn);
    Node rez = _e.add_fun(bad,tvar,epi1); // Return type-name constructor
    // Add a second constructor taking an expanded arg list
    FunPtrNode epi2 = IntrinsicNode.convertTypeNameStruct(ts, tn.alias(), errMsg());
    _e.add_fun(bad,tvar,epi2); // type-name constructor with expanded arg list

    return rez;
  }

  /** A statement is a list of variables to final-assign or re-assign, and an
   *  ifex for the value.  The variables are available in all later statements.
   *  Final-assigned variables can never be assigned again.  Forward references
   *  must be defined in the same scope (or higher) as the outermost pending def.
   *  This is the same as a lambda calc LetRec expression: "let id = def in ..."
   *
   *  stmt = [id[:type] [:]=]* ifex
   *  stmt = id     // Implicit variable creation with nil
   *  stmt = ^ifex  // Early function exit
   *
   *  Note the syntax difference between:
   *    stmt = id := val  //    re-assignment
   *    stmt = id  = val  // final assignment
   *   tstmt = id =:type  // type variable decl, type assignment
   *
   *  The ':=' is the re-assignment token, no spaces allowed.
   */
  private Node stmt(boolean lookup_current_scope_only) {
    if( peek('^') ) {           // Early function exit
      Node ifex = ifex();
      if( ifex==null ) ifex=con(Type.XNIL);
      if( _e._par._par==null )
        return err_ctrl1(ErrMsg.syntax(this,"Function exit but outside any function"));
      return _e.early_exit(this,ifex);
    }

    // Gather ids in x = y = z = ....
    Ary<String> toks = new Ary<>(new String[1],0);
    Ary<Type  > ts   = new Ary<>(new Type  [1],0);
    Ary<Parse > badfs= new Ary<>(new Parse [1],0);
    Ary<Parse > badts= new Ary<>(new Parse [1],0);
    BitSet rs = new BitSet();
    boolean default_nil = false;
    _e.nongen_push(_e);
    while( true ) {
      skipWS();
      int oldx = _x;            // Unwind token parse point
      Parse badf = errMsg();    // Capture location in case of field error
      String tok = token();     // Scan for 'id = ...'
      if( tok == null ) break;  // Out of ids
      int oldx2 = _x;           // Unwind assignment flavor point
      Type t = null;
      // x  =: ... type  assignment, handled before we get here
      // x  =  ... final assignment
      // x :=  ... var   assignment
      // x : type  = ... typed final assignment
      // x : type := ... typed var   assignment
      // x : nontype = ... error, missing type
      // p? x : nontype ... part of trinary
      Parse badt = errMsg();    // Capture location in case of type error
      if( peek(":=") ) _x=oldx2; // Avoid confusion with typed assignment test
      else if( peek(':') && (t=type())==null ) { // Check for typed assignment
        if( scope().test_if() ) _x = oldx2; // Grammar ambiguity, resolve p?a:b from a:int
        else err_ctrl0("Missing type after ':'");
      }
      if( peek(":=") ) rs.set(toks._len);              // Re-assignment parse
      else if( !peek_not('=','=') ) {                  // Not any assignment
        // For structs, allow a bare id as a default def of nil
        if( lookup_current_scope_only && ts.isEmpty() && (peek(';') || peek('}') ||
        // These next two tokens are syntactically invalid, but a semi-common error situation:
        //   @{ fld;fld;fld;...  fld );  // Incorrect closing paren.  Go ahead and allow a bare id.
                                                          peek(']') || peek(')' ))) {
          _x--;                                        // Push back statement end
          default_nil=true;                            // Shortcut def of nil
          rs.set(toks._len);                           // Shortcut mutable
        } else {
          _x = oldx; // Unwind the token parse, and try an expression parse
          break;     // Done parsing assignment tokens
        }
      }

      toks .add(_e._nongen.add_var(tok.intern(),TV2.make_leaf_ns(null,"Env.add_var")));
      ts   .add(t  );
      badfs.add(badf);
      badts.add(badt);
    }

    // Normal statement value parse
    Node ifex = default_nil ? con(Type.XNIL) : ifex(); // Parse an expression for the statement value
    // Check for no-statement after start of assignment, e.g. "x = ;"
    if( ifex == null ) {        // No statement?
      if( toks._len == 0 ) return _e.nongen_pop(null);
      ifex = err_ctrl2("Missing ifex after assignment of '"+toks.last()+"'");
    }
    // Honor all type requests, all at once, by inserting type checks on the ifex.
    for( int i=0; i<ts._len; i++ )
      ifex = typechk(ifex,ts.at(i),mem(),badts.at(i));
    ifex.keep();

    // Assign tokens to value
    for( int i=0; i<toks._len; i++ ) {
      String tok = toks.at(i);               // Token being assigned
      Access mutable = rs.get(i) ? Access.RW : Access.Final;  // Assignment is mutable or final
      // Find scope for token.  If not defining struct fields, look for any
      // prior def.  If defining a struct, tokens define a new field in this scope.
      ScopeNode scope = lookup_scope(tok,lookup_current_scope_only);
      if( scope==null ) {                    // Token not already bound at any scope
        if( ifex instanceof FunPtrNode && !ifex.is_forward_ref() )
          ((FunPtrNode)ifex).bind(tok); // Debug only: give name to function
        create(tok,con(Type.XNIL),Access.RW);  // Create at top of scope as undefined
        scope = scope();                // Scope is the current one
        scope.def_if(tok,mutable,true); // Record if inside arm of if (partial def error check)
      }
      // Handle re-assignments and forward referenced function definitions.
      Node n = scope.stk().get(tok); // Get prior direct binding
      if( n.is_forward_ref() ) {     // Prior is a f-ref
        assert !scope.stk().is_mutable(tok) && scope == scope();
        if( ifex instanceof FunPtrNode )
          ((FunPtrNode)n).merge_ref_def(tok,(FunPtrNode)ifex,scope.stk());
        else ; // Can be here if already in-error

      } else { // Store into scope/NewObjNode/display

        // Assign into display, changing an existing def
        Node ptr = get_display_ptr(scope); // Pointer, possibly loaded up the display-display
        StoreNode st = new StoreNode(mem(),ptr,ifex,mutable,tok,badfs.at(i));
        scope().replace_mem(st);
        scope.def_if(tok,mutable,false); // Note 1-side-of-if update
      }
    }

    return _e.nongen_pop(ifex.unkeep());
  }

  /** Parse an if-expression, with lazy eval on the branches.  Assignments to
   *  new variables are allowed in either arm (as-if each arm is in a mini
   *  scope), and variables assigned on all live arms are available afterwards.
   *  ifex = expr [? stmt [: stmt]]
   */
  private Node ifex() {
    Node expr = apply();
    if( expr == null ) return null; // Expr is required, so missing expr implies not any ifex
    if( !peek('?') ) return expr;   // No if-expression

    scope().push_if();            // Start if-expression tracking new defs
    Node ifex = init(new IfNode(ctrl(),expr));
    set_ctrl(gvn(new CProjNode(ifex,1))); // Control for true branch
    Node old_mem = mem().keep(2);         // Keep until parse false-side
    Node tex = stmt(false);               // Parse true expression
    if( tex == null ) tex = err_ctrl2("missing expr after '?'");
    tex.keep(2);                   // Keep until merge point
    Node t_ctrl= ctrl().keep(2);   // Keep until merge point
    Node t_mem = mem ().keep(2);   // Keep until merge point

    scope().flip_if();          // Flip side of tracking new defs
    Env.GVN.add_work_all(ifex.unkeep(2));
    set_ctrl(gvn(new CProjNode(ifex,0))); // Control for false branch
    Env.GVN.add_reduce(ifex);
    set_mem(old_mem.unkeep(2));    // Reset memory to before the IF
    Node fex = peek(':') ? stmt(false) : con(Type.XNIL);
    if( fex == null ) fex = err_ctrl2("missing expr after ':'");
    fex.keep(2);                   // Keep until merge point
    Node f_ctrl= ctrl().keep(2);   // Keep until merge point
    Node f_mem = mem ().keep(2);   // Keep until merge point

    Parse bad = errMsg();
    t_mem = scope().check_if(true ,bad,_gvn,t_ctrl,t_mem); // Insert errors if created only 1 side
    f_mem = scope().check_if(false,bad,_gvn,f_ctrl,f_mem); // Insert errors if created only 1 side
    scope().pop_if();         // Pop the if-scope
    RegionNode r = set_ctrl(init(new RegionNode(null,t_ctrl.unkeep(2),f_ctrl.unkeep(2))));
    r._val = Type.CTRL;
    _gvn.add_reduce(t_ctrl);
    _gvn.add_reduce(f_ctrl);
    if( t_ctrl._val==Type.XCTRL ) _gvn.add_flow(t_mem);
    if( f_ctrl._val==Type.XCTRL ) _gvn.add_flow(f_mem);
    set_mem(   gvn(new PhiNode(TypeMem.FULL,bad,r        ,t_mem.unkeep(2),f_mem.unkeep(2))));
    Node rez = gvn(new PhiNode(Type.SCALAR ,bad,r.unkeep(2),tex.unkeep(2),  fex.unkeep(2))) ; // Ifex result
    _gvn.add_work_all(r);
    return rez;
  }

  /** Parse a lisp-like function application.  To avoid the common bug of
   *  forgetting a ';', these must be on the same line.
      apply = expr
      apply = expr expr*
   */
  private Node apply() {
    Node expr = expr();
    if( expr == null ) return null;
    while( true ) {
      skipWS();
      int oldx = _x;
      int old_last = _lastNWS;
      expr.keep(2);             // Keep alive across argument parse
      Node arg = expr();
      if( arg==null ) return expr.unkeep(2);
      // To avoid the common bug of forgetting a ';', these must be on the same line.
      int line_last = _lines.binary_search(old_last);
      int line_now  = _lines.binary_search(_x);
      if( line_last != line_now ) {
        _x = oldx;  _lastNWS = old_last;  expr.unhook();
        return err_ctrl2("Lisp-like function application split between lines "+line_last+" and "+line_now+", but must be on the same line; possible missing semicolon?");
      }
      expr = do_call(errMsgs(oldx,oldx),args(expr.unkeep(2),arg)); // Pass the 1 arg
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
  private Node expr() {
    skipWS();         // Invariant: WS already skipped before & after each expr depth
    return _expr(1);
  }

  // Invariant: WS already skipped before & after each _expr depth
  private Node _expr(int prec) {
    int lhsx = _x;              // Invariant: WS already skipped
    Node lhs = _expr_higher(prec,null);
    if( lhs==null ) return null;
    while( true ) {             // Kleene star at this precedence
      // Look for a binop at this precedence level
      int opx = _x;             // Invariant: WS already skipped
      String bintok = peek(PrimNode.PRIM_TOKS);
      if( !_good_prec_tok(prec,bintok) ) return lhs; // No token at this precedence
      _x += bintok.length();
      skipWS();
      int rhsx = _x;            // Invariant: WS already skipped
      lhs.keep();
      // Get the matching FunPtr (or Unresolved).
      // This is a primitive lookup and always returns a FRESH copy (see HM.Ident).
      UnOrFunPtrNode op = _e.lookup_filter_2(bintok.intern()); // BinOp, or null
      assert op!=null;          // Since found valid token, must find matching primnode
      FunNode sfun = op.funptr().fun();
      assert sfun._op_prec == prec;
      // Check for Thunking the RHS
      if( sfun._thunk_rhs ) {
        lhs = _short_circuit_expr(lhs.unkeep(),prec,bintok,op,opx,lhsx,rhsx);
      } else {                  // Not a thunk!  Eager evaluation of RHS
        op.keep();
        Node rhs = _expr_higher_require(prec,bintok,lhs.unkeep());
        // Emit the call to both terms
        // LHS in unhooked prior to optimizing/replacing.
        lhs = do_call(errMsgs(opx,lhsx,rhsx), args(op.unkeep(),lhs,rhs));
      }
      // Invariant: LHS is unhooked
    }
  }

  // Get an expr at the next higher precedence, or a term, or null
  private Node _expr_higher( int prec, Node lhs ) {
    if( lhs != null ) lhs.keep();
    Node rhs = prec+1 == PrimNode.PREC_TOKS.length ? term() : _expr(prec+1);
    if( lhs != null ) lhs.unkeep();
    return rhs;
  }
  private Node _expr_higher_require( int prec, String bintok, Node lhs ) {
    Node rhs = _expr_higher(prec,lhs);
    return rhs==null ? err_ctrl2("Missing term after '"+bintok+"'") : rhs;
  }
  // Check that this token is valid for this precedence level
  private boolean _good_prec_tok(int prec, String bintok) {
    if( bintok==null ) return false;
    for( String tok : PrimNode.PREC_TOKS[prec] ) if( Util.eq(bintok,tok) ) return true;
    return false;
  }

  // Short-circuit 'thunks' the RHS operator and passes it to a thunk-aware
  // primitive.  The primitive is required to fully inline & optimize out the
  // Thunk before we exit here.  However, the primitive can do pretty much what
  // it wants with the Thunk (currently nil-check LHS, then optionally Call the
  // thunk).
  private Node _short_circuit_expr(Node lhs, int prec, String bintok, Node op, int opx, int lhsx, int rhsx) {
    // Capture state so we can unwind after parsing delayed execution
    NewObjNode stk = scope().stk(); // Display
    Node old_ctrl = ctrl().keep(2);
    Node old_mem  = mem ().keep(2);
    op.keep(2);
    TypeStruct old_ts = stk._ts;
    Ary<Node> old_defs = stk._defs.deepCopy();
    lhs.keep(2);

    // Insert a thunk header to capture the delayed execution
    ThunkNode thunk = (ThunkNode)gvn(new ThunkNode(mem()));
    set_ctrl(thunk);
    set_mem (gvn(new ParmNode(MEM_IDX,"mem",thunk.keep(2),TypeMem.MEM,Env.DEFMEM,null)));

    // Delayed execution parse of RHS
    Node rhs = _expr_higher_require(prec,bintok,lhs);

    // Insert thunk tail, unwind memory state
    ThretNode thet = gvn(new ThretNode(ctrl(),mem(),rhs,Env.GVN.add_flow(thunk.unkeep(2)))).keep(2);
    set_ctrl(old_ctrl.unkeep(2));
    set_mem (old_mem .unkeep(2));
    for( int i=0; i<old_defs._len; i++ )
      assert old_defs.at(i)==stk._defs.at(i); // Nothing peeked thru the Thunk & updated outside

    // Emit the call to both terms.  Both the emitted call and the thunk MUST
    // inline right now.
    lhs = do_call(errMsgs(opx,lhsx,rhsx), args(op.unkeep(2),lhs.unkeep(2),thet.unkeep(2)));
    assert thunk.is_dead() && thet.is_dead(); // Thunk, in fact, inlined

    // Extra variables in the thunk not available after the thunk.
    // Set them to Err.
    if( stk._ts != old_ts ) {
      lhs.keep(2);
      for( int i=old_defs._len; i<stk._defs._len; i++ ) {
        // TODO: alignment between old_defs and struct fields
        String fname = stk._ts.fld_idx(i)._fld;
        String msg = "'"+fname+"' not defined prior to the short-circuit";
        Parse bad = errMsg(rhsx);
        Node err = gvn(new ErrNode(ctrl(),bad,msg));
        set_mem(gvn(new StoreNode(mem(),scope().ptr(),err,Access.Final,fname,bad)));
      }
      lhs.unkeep(2);
    }
    return lhs;
  }

  /** Any number field-lookups or function applications, then an optional assignment
   *    term = id++ | id--
   *    term = uniop term
   *    term = tfact [tuple | .field | [.field[:]=stmt | .field++ | .field-- | e]
   *    term = tfact bopen stmts bclose      // if bopen/bclose is arity-2 e.g. ary[idx]
   *    term = tfact bopen stmts bclose stmt // if bopen/bclose is arity-3 e.g. ary[idx]=val
   */
  // Invariant: WS already skipped before & after term
  private Node term() {
    int oldx = _x;

    // Check for id++ / id--
    // These are special forms (for now) because they side-effect.
    String tok = token();
    if( tok != null ) {
      Node n;
      if( peek("++") && (n=inc(tok, 1))!=null ) return n;
      if( peek("--") && (n=inc(tok,-1))!=null ) return n;
    }

    // Check for uniops.  These are normal identifiers with a trailing '_'
    // flagged as an operator.
    if( tok != null ) {
      UnOrFunPtrNode unifun = _e.lookup_filter_uni(tok); // UniOp, or null
      if( unifun != null ) {
        FunPtrNode ptr = unifun.funptr();
        // Token might have been longer than the filtered name; happens if a
        // bunch of operator characters are adjacent but we can make an operator
        // out of the first few.
        _x = oldx+ptr._name.length();
        unifun.keep();
        Node term = term();
        if( term==null ) { unifun.unhook(); _x = oldx; return null; }
        unifun.unkeep();
        return do_call(errMsgs(0,oldx),args(unifun,term));
      }
    }

    _x = oldx;

    // Normal term expansion
    Node n = tfact();
    if( n == null ) return null;
    while( true ) {             // Repeated application or field lookup is fine
      if( peek('.') ) {         // Field?
        skipWS();               //
        int fld_start=_x;       // Get field start
        String fld = token0();  // Field name
        if( fld == null ) {     // Not a token, check for a field number
          int fldnum = field_number();
          if( fldnum == -1 ) return err_ctrl2("Missing field name after '.'");
          fld = ""+fldnum;      // Convert to a field name
        }
        fld=fld.intern();

        Node castnn = gvn(new CastNode(ctrl(),n,TypeMemPtr.ISUSED)); // Remove nil choice

        // Store or load against memory
        if( peek(":=") || peek_not('=','=')) {
          Access fin = _buf[_x-2]==':' ? Access.RW : Access.Final;
          Node stmt = stmt(false);
          if( stmt == null ) n = err_ctrl2("Missing stmt after assigning field '."+fld+"'");
          else scope().replace_mem( new StoreNode(mem(),castnn,n=stmt.keep(),fin,fld ,errMsg(fld_start)));
          skipWS();
          return n.unkeep();
        } else {
          n = gvn(new LoadNode(mem(),castnn,fld,errMsg(fld_start)));
        }

      } else if( peek('(') ) {  // Attempt a function-call
        oldx = _x;              // Just past paren
        skipWS();               // Skip to start of 1st arg
        n.keep();               // Keep alive across arg parse
        int first_arg_start = _x;
        Node arg = tuple(oldx-1,stmts(),first_arg_start); // Parse argument list
        if( arg == null )       // tfact but no arg is just the tfact
          { _x = oldx; return n.unkeep(); }
        Type tn = n._val;
        boolean may_fun = tn.isa(TypeFunPtr.GENERIC_FUNPTR);
        if( !may_fun && arg.op_prec() >= 0 ) { _x=oldx; return n.unkeep(); }
        if( !may_fun &&
            // Notice the backwards condition: n was already tested for !(tn instanceof TypeFun).
            // Now we test the other way: the generic function can never be an 'n'.
            // Only if we cannot 'isa' in either direction do we bail out early
            // here.  Otherwise, e.g. 'n' might be an unknown function argument
            // and during GCP be 'lifted' to a function; if we bail out now we
            // may disallow a legal program with function arguments.  However,
            // if 'n' is a e.g. Float there's no way it can 'lift' to a function.
            !TypeFunPtr.GENERIC_FUNPTR.isa(tn) ) {
          kill(arg);
          n.unhook();
          n = err_ctrl2("A function is being called, but "+tn+" is not a function");
        } else {
          Parse[] badargs = ((NewObjNode)arg.in(0))._fld_starts; // Args from tuple
          badargs[0] = errMsg(oldx-1); // Base call error reported at the opening paren
          n = do_call0(false,badargs,args(n.unkeep(),arg)); // Pass the tuple
        }

      } else {
        // Check for balanced op
        String bop = bal_open(); // Balanced op read
        if( bop==null ) break;   // Not a balanced op
        oldx = _x-bop.length();  // Token start

        n.keep();
        skipWS();
        int oldx2 = _x;
        Node idx = stmts();     // Index expression
        if( idx==null ) { n.unhook(); return err_ctrl2("Missing stmts after '"+bop+"'"); }
        tok = token();
        if( tok==null ) { n.unhook(); return err_ctrl2("Missing close after '"+bop+"'"); }

        // Need to find which balanced op close.  Find the longest matching name
        UnOrFunPtrNode unr = _e.lookup_filter_bal(bop,tok);
        if( unr==null ) { n.unhook(); return err_ctrl2("No such operation '_"+bop+"_"+tok+"'"); }

        //FunPtrNode fptr=null;
        //UnresolvedNode unr = ((UnOrFunPtrNode)bfun.unkeep()).unk();
        //if( unr!=null ) {       // Unresolved of balanced ops?
        //  for( Node def : unr._defs ) {
        //    FunPtrNode def0 = (FunPtrNode)def;
        //    if( tok.startsWith(def0.fun()._bal_close) &&
        //        (fptr==null || fptr.fun()._bal_close.length() < def0.fun()._bal_close.length()) )
        //      fptr = def0;      // Found best match
        //  }
        //  Env.GVN.add_dead(Env.GVN.add_reduce(bfun)); // Dropping any new FreshNode, and replacing with this one
        //  idx.keep();
        //  bfun = (UnOrFunPtrNode)gvn(new FreshNode(_e._nongen,fptr));
        //} else fptr = bfun.funptr(); // Just the one balanced op
        //FunNode fun = fptr.fun();
        //require(fun._bal_close,oldx);
        //if( fun.nargs()==ARG_IDX+2 ) { // array, index
        //  n = do_call(errMsgs(0,oldx,oldx2),args(bfun,n.unkeep(),idx.unkeep()));
        //} else {
        //  assert fun.nargs()==ARG_IDX+3; // array, index, value
        //  skipWS();
        //  int oldx3 = _x;
        //  bfun.keep();
        //  Node val = stmt(false);
        //  if( val==null ) { n.unhook(); return err_ctrl2("Missing stmt after '"+fun._bal_close+"'"); }
        //  n = do_call(errMsgs(0,oldx,oldx2,oldx3),args(bfun.unkeep(),n.unkeep(),idx.unkeep(),val));
        //}
        throw unimpl();
      }
    }
    return n;
  }

  // Handle post-increment/post-decrement operator.
  // Does not define a field in structs: "@{ x++; y=2 }" - syntax error, no such field x
  // Skips trailing WS
  private Node inc(String tok, int d) {
    skipWS();
    ScopeNode scope = lookup_scope(tok=tok.intern(),false); // Find prior scope of token
    // Need a load/call/store sensible options
    Node n;
    if( scope==null ) {         // Token not already bound to a value
      create(tok,con(Type.XNIL),Access.RW);
      scope = scope();
    } else {                    // Check existing token for mutable
      if( !scope.is_mutable(tok) )
        return err_ctrl2("Cannot re-assign final val '"+tok+"'");
    }

    // Scope is discovered by walking lexical display stack.
    // Pointer to the proper display is found via ptr-walking live display stack.
    // Now properly load from the display.
    // This does a HM.Ident lookup, producing a FRESH tvar every time.
    Node ptr = get_display_ptr(scope);
    n = gvn(new LoadNode(mem(),ptr,tok,null));
    if( n.is_forward_ref() )    // Prior is actually a forward-ref
      return err_ctrl1(ErrMsg.forward_ref(this,((FunPtrNode)n)));
    // Do a full lookup on "+", and execute the function
    n.keep();
    // This is a primitive lookup and always returns a FRESH copy (see HM.Ident).
    Node plus = _e.lookup_filter_2("+");
    Node sum = do_call(errMsgs(0,_x,_x),args(plus,n,con(TypeInt.con(d))));
    // Active memory for the chosen scope, after the call to plus
    scope().replace_mem(new StoreNode(mem(),ptr,sum,Access.RW,tok,errMsg()));
    return n.unkeep();          // Return pre-increment value
  }


  /** Parse an optionally typed factor
   *  tfact = fact[:type]
   */
  private Node tfact() {
    Node fact = fact();
    if( fact==null ) return null;
    int oldx = _x;
    Parse bad = errMsg();
    if( !peek(':') ) { _x = oldx; return fact; }
    Type t = type();
    if( t==null ) { _x = oldx; return fact; } // No error for missing type, because can be ?: instead
    return typechk(fact,t,mem(),bad);
  }


  /** Parse a factor, a leaf grammar token
   *  fact = num       // number
   *  fact = "string"  // string
   *  fact = (stmts)   // General statements parsed recursively
   *  fact = (tuple,*) // tuple; first comma required, trailing comma not required
   *  fact = balop+ stmts balop-           // Constructor with initial size
   *    Ex:    [      7      ]             // Array constructor
   *  fact = balop+ stmts[, stmts]* balop- // Constructor with initial elements
   *    Ex:    [      1   ,  2        ]    // Array constructor with initial elements
   *  fact = {func}    // Anonymous function declaration
   *  fact = id        // variable lookup
   */
  private Node fact() {
    if( skipWS() == -1 ) return null;
    byte c = _buf[_x];
    if( isDigit(c) ) return con(number());
    if( '"' == c ) {
      Node str = string();
      return str==null ? err_ctrl2("Unterminated string") : str;
    }
    int oldx = _x;
    if( peek1(c,'(') ) {        // a nested statement or a tuple
      int first_arg_start = _x;
      Node s = stmts();
      if( s==null ) { _x = oldx; return null; } // A bare "()" pair is not a statement
      if( peek(')') ) return s;                 // A (grouped) statement
      if( !peek(',') ) return s;                // Not a tuple, probably a syntax error
      _x --;                                    // Reparse the ',' in tuple
      return tuple(oldx,s,first_arg_start);     // Parse a tuple
    }
    // Anonymous function
    if( peek1(c,'{') ) return func(); // Anonymous function

    // Anonymous struct
    if( peek2(c,"@{") ) return struct();

    // Check for a valid 'id'
    String tok = token0();
    if( tok == null ) { _x = oldx; return null; }
    tok = tok.intern();
    if( Util.eq(tok,"=") || Util.eq(tok,"^") )
      { _x = oldx; return null; } // Disallow '=' as a fact, too easy to make mistakes
    ScopeNode scope = lookup_scope(tok,false);
    if( scope == null ) { // Assume any unknown id is a forward-ref of a recursive function
      // Ops cannot be forward-refs, so are just 'not a fact'.  Cannot declare
      // them as a undefined forward-ref right now, because the op might be the
      // tail-half of a balanced-op, which is parsed by term() above.
      if( isOp(tok) ) { _x = oldx; return null; }
      // Must be a forward reference
      Env fref_env = _e.lookup_fref(tok=tok.intern());
      if( fref_env==null ) fref_env = _e;
      Node fref = gvn(FunPtrNode.forward_ref(_gvn,tok,errMsg(oldx),fref_env));
      // Place in nearest enclosing closure scope, this will keep promoting until we find the actual scope
      fref_env._scope.stk().create(tok,fref,Access.Final);
      return fref;
    }

    // Else must load against most recent display update.  Get the display to
    // load against.  If the scope is local, we load against it directly,
    // otherwise the display is passed in as a hidden argument.
    // This does a HM.Ident lookup, producing a FRESH tvar every time.
    Node ptr = get_display_ptr(scope);
    return gvn(new LoadNode(mem(),ptr,tok.intern(),null));
  }


  /** Parse a tuple; first stmt but not the ',' parsed.
   *  tuple= (stmts,[stmts,])     // Tuple; final comma is optional
   */
  private Node tuple(int oldx, Node s, int first_arg_start) {
    Parse bad = errMsg(first_arg_start);
    Ary<Parse> bads = new Ary<>(new Parse[1],1);
    Ary<Node > args = new Ary<>(new Node [1],0);
    while( s!= null ) {         // More args
      bads.push(bad);           // Collect arg & arg start
      args.push(s.keep());
      if( !peek(',') ) break;   // Final comma is optional
      skipWS();                 // Skip to arg start before recording arg start
      bad = errMsg();           // Record arg start
      s=stmts();                // Parse arg
    }
    require(')',oldx);          // Balanced closing paren

    // Build the tuple from gathered args
    NewObjNode nn = new NewObjNode(false,TypeStruct.open(TypeMemPtr.NO_DISP),Env.ANY);
    for( int i=0; i<args._len; i++ )
      nn.create_active((""+i).intern(),args.at(i).unkeep(),Access.Final);
    nn._fld_starts = bads.asAry();
    nn.no_more_fields();
    init(nn);
    nn.xval();

    // NewNode returns a TypeMem and a TypeMemPtr (the reference).
    set_mem( Env.DEFMEM.make_mem_proj(nn,mem()) );
    return gvn(new ProjNode(nn.unkeep(2),REZ_IDX));
  }


  /** Parse anonymous struct; the opening "@{" already parsed.  A lexical scope
   *  is made and new variables are defined here.  Next comes statements, with
   *  each assigned value becoming a struct member, then the closing "}".
   *  struct = \@{ stmts }
   */
  private Node struct() {
    int oldx = _x-1; Node ptr;  // Opening @{
    try( Env e = new Env(_e, false, ctrl(), mem()) ) { // Nest an environment for the local vars
      _e = e;                   // Push nested environment
      stmts(true);              // Create local vars-as-fields
      require('}',oldx);        // Matched closing }
      assert ctrl() != e._scope;
      e._scope.stk().update("^",Access.Final,Env.ANY);
      ptr = e._scope.ptr().keep();    // A pointer to the constructed object
      e._par._scope.set_ctrl(ctrl()); // Carry any control changes back to outer scope
      e._par._scope.set_mem (mem ()); // Carry any memory  changes back to outer scope
      _e = e._par;                    // Pop nested environment
    } // Pop lexical scope around struct
    return ptr.unkeep();
  }

  /** Parse an anonymous function; the opening '{' already parsed.  After the
   *  '{' comes an optional list of arguments and a '->' token, and then any
   *  number of statements separated by ';'.
   *  func = { [[id]* ->]? stmts }
   */
  private static final Access args_are_mutable=Access.Final; // Args mutable or r/only by default
  private Node func() {
    int oldx = _x;              // Past opening '{'

    // Push an extra hidden display argument.  Similar to java inner-class ptr
    // or when inside of a struct definition: 'this'.
    Node parent_display = scope().ptr();
    TypeMemPtr tpar_disp = (TypeMemPtr) parent_display._val; // Just a TMP of the right alias
    Node fresh_disp = gvn(new FreshNode(_e._nongen,ctrl(),parent_display)).keep();

    // Incrementally build up the formals
    TypeStruct formals = TypeStruct.make("",false,true,
                                         TypeFld.make(" mem",TypeMem.MEM,MEM_IDX),
                                         TypeFld.make("^",tpar_disp,DSP_IDX));
    TypeStruct no_args_formals = formals;
    Ary<Parse> bads= new Ary<>(new Parse[1],0);

    // Parse arguments
    while( true ) {
      String tok = token();
      if( tok == null ) { _x=oldx; break; } // not a "[id]* ->"
      if( Util.eq((tok=tok.intern()),"->") ) break; // End of argument list
      if( !isAlpha0((byte)tok.charAt(0)) ) { _x=oldx; break; } // not a "[id]* ->"
      Type t = Type.SCALAR;    // Untyped, most generic type
      Parse bad = errMsg();    // Capture location in case of type error
      if( peek(':') &&         // Has type annotation?
          (t=type())==null ) { // Get type
        // If no type, might be "{ x := ...}" or "{ fun arg := ...}" which can
        // be valid stmts, hence this may be a no-arg function.
        if( bads._len-1 <= 2 ) { _x=oldx; break; }
        else {
          // Might be: "{ x y z:bad -> body }" which cannot be any stmt.  This
          // is an error in any case.  Treat as a bad type on a valid function.
          err_ctrl0(peek(',') ? "Bad type arg, found a ',' did you mean to use a ';'?" : "Missing or bad type arg");
          t = Type.SCALAR;
          skipNonWS();         // Skip possible type sig, looking for next arg
        }
      }
      formals = formals.add_fld(tok,Access.Final,t,ARG_IDX+bads._len); // Accumulate args
      bads.add(bad);
    }
    // If this is a no-arg function, we may have parsed 1 or 2 tokens as-if
    // args, and then reset.  Also reset to just the mem & display args.
    if( _x == oldx ) { formals = no_args_formals;  bads.set_len(ARG_IDX); }

    try( GVNGCM.Build<Node> X = _gvn.new Build<>()) { // Nest an environment for the local vars
      // Build the FunNode header
      FunNode fun = (FunNode)X.xform(new FunNode(formals.close()).add_def(_prims ? Env.ALL_CTRL : gvn(new CEProjNode(Env.FILE._scope))));
      // Record H-M VStack in case we clone
      fun.set_nongens(_e._nongen.compact());
      // Build Parms for system incoming values
      Node rpc = X.xform(new ParmNode(CTL_IDX," rpc",fun,Env.ALL_CALL,null));
      Node mem = X.xform(new ParmNode(MEM_IDX," mem",fun,TypeMem.MEM,Env.DEFMEM,null));
      Node clo = X.xform(new ParmNode(DSP_IDX,"^"   ,fun,tpar_disp,parent_display/*con(tpar_disp)*/,null));

      // Increase scope depth for function body.
      try( Env e = new Env(_e, true, fun, mem) ) { // Nest an environment for the local vars
        _e = e;                   // Push nested environment
        // Display is special: the default is simply the outer lexical scope.
        // But here, in a function, the display is actually passed in as a hidden
        // extra argument and replaces the default.
        NewObjNode stk = e._scope.stk();
        if( !_prims ) stk.update("^",Access.Final,clo);

        // Parms for all arguments
        Parse errmsg = errMsg();  // Lazy error message
        for( TypeFld fld : formals.flds() ) { // User parms start
          if( fld._order <= DSP_IDX ) continue;// Already handled
          Node parm = X.xform(new ParmNode(fld,fun,Env.ALL_PARM,errmsg));
          e._nongen.add_var(fld._fld,parm.tvar());
          create(fld._fld,parm, args_are_mutable);
        }
        for( TypeFld fld : formals.flds() ) { // User parms start
          if( fld._order <= DSP_IDX ) continue;// Already handled
          if( fld._t != Type.SCALAR )
            throw unimpl();     // Add a arg type check
        }

        // Parse function body
        Node rez = stmts();       // Parse function body
        if( rez == null ) rez = err_ctrl2("Missing function body");
        require('}',oldx-1);      // Matched with opening {}

        // Merge normal exit into all early-exit paths
        if( e._scope.is_closure() ) rez = merge_exits(rez);
        // Standard return; function control, memory, result, RPC.  Plus a hook
        // to the function for faster access.
        RetNode ret = (RetNode)X.xform(new RetNode(ctrl(),mem(),rez,rpc,fun));
        (_prims ? Env.TOP : Env.FILE)._scope.add_def(ret);
        // The FunPtr builds a real display; any up-scope references are passed in now.
        Node fptr = X.xform(new FunPtrNode(null,ret,fresh_disp.unhook()));

        _e = e._par;            // Pop nested environment; pops nongen also
        return (X._ret=fptr);   // Return function; close-out and DCE 'e'
      }
    }
  }

  private Node merge_exits(Node rez) {
    rez.keep();
    ScopeNode s = scope();
    Node ctrl = s.early_ctrl();
    Node mem  = s.early_mem ();
    Node val  = s.early_val ();
    s.early_kill();
    if( ctrl == null ) return rez.unkeep(); // No other exits to merge into
    try(GVNGCM.Build<Node> X = _gvn.new Build<>()) {
      ctrl = ctrl.add_def(ctrl()).unkeep();
      ctrl._val = Type.CTRL;
      set_ctrl(ctrl=X.init(ctrl));
      mem.unkeep().set_def(0,ctrl);
      val.unkeep().set_def(0,ctrl);
      Node mem2 = X.xform(mem.add_def(mem()));
      Node val2 = X.xform(val.add_def(rez.unkeep()));
      set_mem(mem2);
      return (X._ret=val2);
    }
  }

  // Merge this early exit path into all early exit paths being recorded in the
  // current Env/Scope.
  Node do_exit( ScopeNode s, Node rez ) {
    Node ctrl = s.early_ctrl();
    Node mem  = s.early_mem ();
    Node val  = s.early_val ();
    if( ctrl == null ) {
      s.set_def(4,ctrl=new RegionNode((Node)null).keep()); ctrl._val=Type.CTRL;
      s.set_def(5,mem =new PhiNode(TypeMem.MEM, null,(Node)null).keep());
      s.set_def(6,val =new PhiNode(Type.SCALAR, null,(Node)null).keep());
    }
    ctrl.add_def(ctrl());
    mem .add_def(mem ());
    val .add_def(rez   );
    set_ctrl(Env.XCTRL);
    set_mem (con(TypeMem.XMEM));
    return con(Type.XNIL);
  }

  /** A balanced operator as a fact().  Any balancing token can be used.
   *  bterm = [ stmts ]              // size  constructor
   *  bterm = [ stmts, [stmts,]* ]   // tuple constructor
   */
  Node bfact(int oldx, UnOrFunPtrNode bfun) {
    skipWS();
    int oldx2 = _x;             // Start of stmts
    Node s = stmts();
    if( s==null ) { _x = oldx; return null; } // A bare "()" pair is not a statement
    if( peek(',') ) {
      _x --;                    // Reparse the ',' in tuple
      throw unimpl();
    }
    require(bfun.funptr().fun()._bal_close,oldx);
    return do_call(errMsgs(oldx,oldx2),args(bfun,s));
  }

  // If this token can be a balanced-operator open token
  String bal_open() {
    int oldx = _x;
    String bal = token();
    if( bal==null ) return null;
    String xbal = _e.lookup_filter_bal(bal.intern());
    if( xbal==null ) { _x=oldx; return null; }
    // Actual minimal length op might be smaller than the parsed token
    // (greedy algo vs not-greed)
    _x = oldx+xbal.length();
    return xbal;
  }

  // Add a typecheck into the graph, with a shortcut if trivially ok.
  private Node typechk(Node x, Type t, Node mem, Parse bad) {
    return t == null || x._val.isa(t) ? x : gvn(new AssertNode(mem,x,t,bad,_e));
  }

  private String token() { skipWS();  return token0(); }
  // Lexical tokens.  Any alpha, followed by any alphanumerics is a alpha-
  // token; alpha-tokens end with WS or any operator character.  Any collection
  // of the classic operator characters are a token, except that they will break
  // un-ambiguously.
  private String token0() {
    if( _x >= _buf.length ) return null;
    byte c=_buf[_x];  int x = _x;
    if( isOp0(c) || (c=='_' && isOp0(_buf[_x+1])) ) while( _x < _buf.length && isOp1   (_buf[_x]) ) _x++;
    else if( isAlpha0(c) )                          while( _x < _buf.length && isAlpha1(_buf[_x]) ) _x++;
    else return null; // Not a token; specifically excludes e.g. all bytes >= 128, or most bytes < 32
    if( (c==':' || c==',') && _x-x==1 ) // Disallow bare ':' as a token; ambiguous with ?: and type annotations; same for ','
      { _x=x; return null; } // Unwind, not a token
    if( c=='-' && _x-x>2 && _buf[x+1]=='>' ) // Disallow leading "->", confusing with function parameter list end; eg "not={x->!x}"
      _x=x+2;                                // Just return the "->"
    return new String(_buf,x,_x-x);
  }
  static boolean isOp(String s) {
    if( !isOp0((byte)s.charAt(0)) ) return false;
    for( int i=1; i<s.length(); i++ )
      if( !isOp1((byte)s.charAt(i)) ) return false;
    return true;
  }

  // Parse a number; WS already skipped and sitting at a digit.  Relies on
  // Javas number parsing.
  private Type number() {
    _pp.setIndex(_x);
    Number n = _nf.parse(_str,_pp);
    _x = _pp.getIndex();
    if( n instanceof Long   ) return n.longValue()==0 ? Type.XNIL : TypeInt.con(n.  longValue());
    if( n instanceof Double ) return TypeFlt.con(n.doubleValue());
    throw new RuntimeException(n.getClass().toString()); // Should not happen
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

  /** Parse a String; _x is at '"'.
   *  str  = [.\%]*               // String contents; \t\n\r\% standard escapes
   *  str  = %[num]?[.num]?fact   // Percent escape embeds a 'fact' in a string; "name=%name\n"
   */
  private Node string() {
    int oldx = ++_x;
    byte c;
    while( (c=_buf[_x++]) != '"' ) {
      if( c=='%' ) throw unimpl();
      if( c=='\\' ) throw unimpl();
      if( _x == _buf.length ) return null;
    }
    String str = new String(_buf,oldx,_x-oldx-1).intern();
    // Convert to ptr-to-constant-memory-string
    NewNode nnn = (NewNode)gvn( new NewStrNode.ConStr(str) );
    if( Env.DEFMEM._defs.atX(nnn._alias)==null )
      set_mem(Env.DEFMEM.make_mem_proj(nnn,mem()));
    return gvn( new ProjNode(nnn,REZ_IDX));
  }

  /** Parse a type or return null
   *  type = tcon | tfun | tary | tstruct | ttuple | tvar  // Type choices
   *  tcon = int, int[1,8,16,32,64], flt, flt[32,64], real, str[?]
   *  tary = '[' type? ']'                 // Cannot specify type for array size
   *  tfun = {[[type]* ->]? type }         // Function types mirror func decls
   *  tmod = = | := | ==                   // '=' is r/final, ':=' is r/w, '==' is read-only
   *  tstruct = @{ [id [tmod [type?]];]*}  // Struct types are field names with optional types.
   *  ttuple = ([type?] [,[type?]]*)       // List of types, trailing comma optional
   *  tvar = A previously declared type variable
   *
   *  Unknown tokens when type_var is false are treated as not-a-type.  When
   *  true, unknown tokens are treated as a forward-ref new type.
   */
  private Type type() { return typep(false); }
  // Returning a type variable assignment result or null.  Flag to allow
  // unknown type variables as forward-refs.
  private Type typev() {
    Type t = type0(true);
    // Type.ANY is a flag for '->' which is not a type.
    return t==Type.ANY ? null : t;
  }
  // TypeObjs get wrapped in a pointer, and the pointer is returned instead.
  private Type typep(boolean type_var) {
    Type t = type0(type_var);
    if( t instanceof TypeMemPtr ) return typeq(t); // Named type is already a TMP
    if( !(t instanceof TypeObj) ) return t; // Primitives are not wrapped
    // Automatically convert unnamed structs to refs.
    // Make a reasonably precise alias.
    int type_alias = t instanceof TypeStruct ? BitsAlias.REC : (t instanceof TypeStr ? BitsAlias.STR : BitsAlias.AARY);
    TypeMemPtr tmp = TypeMemPtr.make(type_alias,(TypeObj)t);
    return typeq(tmp);          // And check for null-ness
  }
  // Wrap in a nullable if there is a trailing '?'.  No spaces allowed
  private Type typeq(Type t) { return peek_noWS('?') ? t.meet_nil(Type.XNIL) : t; }

  // No mod is r/w.  ':=' is read-write, '=' is final.
  // Currently '-' is ambiguous with function arrow ->.
  private Access tmod() {
    if( peek_not('=','=') ) { _x--; return Access.Final   ; } // final     , leaving trailing '='
    if( peek(":="       ) ) { _x--; return Access.RW      ; } // read-write, leaving trailing '='
    if( peek("=="       ) ) { _x--; return Access.ReadOnly; } // read-only , leaving trailing '='
    // Default for unnamed field mod
    return Access.RW;
  }

  // Type or null or Type.ANY for '->' token
  private Type type0(boolean type_var) {
    if( peek('{') ) {           // Function type
      TypeStruct formals = TypeStruct.make("",false,true,
                                           TypeFld.make_tup(TypeMem.ALLMEM,MEM_IDX),
                                           TypeFld.make_tup(TypeMemPtr.DISP_SIMPLE,DSP_IDX));
      TypeStruct no_args_formals = formals;  Type t; // Collect arg types
      while( (t=typep(type_var)) != null && t != Type.ANY  )
        formals = formals.add_tup(t,formals.len()-2+ARG_IDX);
      Type ret;
      if( t==Type.ANY ) {       // Found ->, expect return type
        ret = typep(type_var);
        if( ret == null ) return null; // should return TypeErr missing type after ->
      } else {                  // Allow no-args and simple return type
        if( formals.len()-2 != 1 ) return null; // should return TypeErr missing -> in tfun
        ret = formals.fld_idx(ARG_IDX); // e.g. { int } Get single return type
        formals = no_args_formals;
      }
      if( !peek('}') ) return null;
      return typeq(TypeFunSig.make(formals,TypeTuple.make_ret(ret)));
    }

    if( peek("@{") ) {          // Struct type
      Ary<TypeFld> flds = new Ary<>(new TypeFld[]{TypeMemPtr.DISP_FLD});
      while( true ) {
        String tok = token();            // Scan for 'id'
        if( tok == null ) break;         // end-of-struct-def
        final String itok = tok.intern(); // Only 1 copy
        Type t = Type.SCALAR;            // Untyped, most generic field type
        Access tmodf = tmod();           // Field access mod; trailing '=' left for us
        if( peek('=') &&                 // Has type annotation?
            (t=typep(type_var)) == null) // Parse type, wrap ptrs
          t = Type.SCALAR;               // No type found, assume default
        if( flds.find(fld -> Util.eq(fld._fld,itok) ) != -1 ) throw unimpl(); // cannot use same field name twice
        flds.add(TypeFld.make(itok,t,tmodf,flds._len-1+ARG_IDX));
        if( !peek(';') ) break; // Final semi-colon is optional
      }
      return peek('}') ? TypeStruct.make("",false,true,flds) : null;
    }

    // "()" is the zero-entry tuple
    // "(   ,)" is a 1-entry tuple
    // "(int )" is a 1-entry tuple (optional trailing comma)
    // "(int,)" is a 1-entry tuple (optional trailing comma)
    // "(,int)" is a 2-entry tuple
    // "(, , )" is a 2-entry tuple
    if( peek('(') ) { // Tuple type
      Ary<TypeFld> flds = new Ary<>(new TypeFld[]{TypeMemPtr.DISP_FLD});
      byte c;
      while( (c=skipWS()) != ')' ) { // No more types...
        Type t = Type.SCALAR;    // Untyped, most generic field type
        if( c!=',' &&            // Has type annotation?
            (t=typep(type_var)) == null) // Parse type, wrap ptrs
          return null;                   // not a type
        flds.add(TypeFld.make_tup(t,ARG_IDX+flds._len-1));
        if( !peek(',') ) break; // Final comma is optional
      }
      return peek(')') ? TypeStruct.make("",false,true,flds) : null;
    }

    if( peek('[') ) {
      Type e = typep(type_var);
      if( e==null ) e=Type.SCALAR;
      return peek(']') ? TypeAry.make(TypeInt.INT64,e,TypeObj.OBJ) : null;
    }

    // Primitive type
    int oldx = _x;
    String tok = token();
    if( tok==null ) return null;
    tok = tok.intern();
    if( Util.eq(tok,"->") ) return Type.ANY; // Found -> return sentinel
    ConTypeNode t = _e.lookup_type(tok);
    if( t==null ) {              // Not a known type var
      if( lookup(tok) != null || // Yes a known normal var; resolve as a normal var
          !type_var ) {          // Or not inside a type-var assignment
        _x = oldx;               // Unwind if not a known type var
        return null;             // Not a type
      }
      // Make a forward-ref ConType and return its type
      int alias = BitsAlias.type_alias(BitsAlias.REC);
      TypeMemPtr tmp = TypeMemPtr.make(alias,(TypeObj)TypeObj.ISUSED.set_name((tok+":").intern()));
      _e.add_type(tok,(ConTypeNode)gvn(new ConTypeNode(tok,tmp,scope())));
      return tmp;
    }
    return t._val;
  }

  // Require a closing character (after skipping WS) or polite error
  private void require( char c, int oldx ) {
    if( peek(c) ) return;
    Parse bad = errMsg();       // Generic error
    bad._x = oldx;              // Openning point
    err_ctrl3("Expected closing '"+c+"' but "+(_x>=_buf.length?"ran out of text":"found '"+(char)(_buf[_x])+"' instead"),bad);
  }
  private void require( String s, int oldx ) {
    for( int i=0; i<s.length(); i++ )
      require(s.charAt(i),oldx);
  }

  // Skip WS, return true&skip if match, false & do not skip if miss.
  private boolean peek( char c ) { return peek1(skipWS(),c); }
  private boolean peek_noWS( char c ) { return peek1(_x >= _buf.length ? -1 : _buf[_x],c); }
  // Already skipped WS & have character;
  // return true & skip if match, false& do not skip if miss.
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
      if( c=='\n' && _x+1 > _lines.last() ) _lines.push(_x+1);
      if( !isWS(c) ) {
        if( oldx-1 > _lastNWS && !isWS(_buf[oldx-1]) ) _lastNWS = oldx-1;
        return c;
      }
      _x++;
    }
    return -1;
  }
  private void skipEOL  () { while( _x < _buf.length && _buf[_x] != '\n' ) _x++; }
  private void skipBlock() { throw unimpl(); }
  // Advance parse pointer to next WS.  Used for parser syntax error recovery.
  private void skipNonWS() {
    while( _x < _buf.length && !isWS(_buf[_x]) ) _x++;
  }

  /** Return true if `c` passes a test */
  private static boolean isWS    (byte c) { return c == ' ' || c == '\t' || c == '\n' || c == '\r'; }
  private static boolean isAlpha0(byte c) { return ('a'<=c && c <= 'z') || ('A'<=c && c <= 'Z') || (c=='_'); }
  private static boolean isAlpha1(byte c) { return isAlpha0(c) || ('0'<=c && c <= '9'); }
  private static boolean isOp0   (byte c) { return "!#$%*+,-.=<>^[]~/&|".indexOf(c) != -1; }
  private static boolean isOp1   (byte c) { return isOp0(c) || ":?_".indexOf(c) != -1; }
  public  static boolean isDigit (byte c) { return '0' <= c && c <= '9'; }

  // Utilities to shorten code for common cases
  public Node gvn (Node n) { return n==null ? null : _gvn.xform(n); }
  private <N extends Node> N init( N n ) { return n==null ? null : _gvn.init(n); }
  private void kill( Node n ) {
    if( n._uses._len==0 ) n.kill();
  }
  public Node ctrl() { return scope().ctrl(); }
  // Set and return a new control
  private <N extends Node> N set_ctrl(N n) { return scope().set_ctrl(n); }
  private Node mem() { return scope().mem(); }
  private void set_mem( Node n) { scope().set_mem(n); }

  private @NotNull ConNode con( Type t ) { return (ConNode)Node.con(t); }

  // Lookup & extend scopes
  public  Node lookup( String tok ) { return _e.lookup(tok); }
  private ScopeNode lookup_scope( String tok, boolean lookup_current_scope_only ) { return _e.lookup_scope(tok,lookup_current_scope_only); }
  public  ScopeNode scope( ) { return _e._scope; }
  private void create( String tok, Node n, Access mutable ) { scope().stk().create(tok,n,mutable); }

  // Get the display pointer.  The function call
  // passed in the display as a hidden argument which we return here.
  private Node get_display_ptr( ScopeNode scope ) {
    // Issue Loads against the Display, until we get the correct scope.  The
    // Display is a linked list of displays, and we already checked that token
    // exists at scope up in the display.
    Env e = _e;
    Node ptr = e._scope.ptr();
    Node fptr = gvn(new FreshNode(e._nongen,ctrl(),ptr));
    Node mmem = mem();
    while( true ) {
      if( scope == e._scope ) return ptr;
      ptr = gvn(new LoadNode(mmem,ptr,"^",null)); // Gen linked-list walk code, walking display slot
      assert ptr.sharptr(mmem).is_display_ptr();
      e = e._par;                                 // Walk linked-list in parser also
    }
  }

  // Wiring for call arguments
  private Node[] args(Node a0, Node a1                  ) { return _args(new Node[]{null,null,a0,a1,a0}); }
  private Node[] args(Node a0, Node a1, Node a2         ) { return _args(new Node[]{null,null,a0,a1,a2,a0}); }
  private Node[] args(Node a0, Node a1, Node a2, Node a3) { return _args(new Node[]{null,null,a0,a1,a2,a3,a0}); }
  private Node[] _args(Node[] args) {
    for( int i=ARG_IDX; i<args.length; i++ ) args[i].keep(); // Hook all args before reducing display
    args[CTL_IDX] = ctrl();     // Always control
    args[MEM_IDX] = mem();      // Always memory
    throw unimpl(); // Calling unkeep on the FDX passed in the DSP_IDX?
    //for( int i=ARG_IDX; i<args.length; i++ ) {
    //  args[i].unkeep();
    //  // Generally might want this in unkeep(), except for cost
    //  if( args[i]._val.is_con() ) Env.GVN.add_reduce(args[i]);
    //}
    //return args;
  }

  // Insert a call, with memory splits.  Wiring happens later, and when a call
  // is wired it picks up projections to merge at the Fun & Parm nodes.
  private Node do_call( Parse[] bads, Node... args ) { return do_call0(true,bads,args); }
  private Node do_call0( boolean unpack, Parse[] bads, Node... args ) {
    CallNode call0 = new CallNode(unpack,bads,args);
    CallNode call = (CallNode)gvn(call0);
    // Call Epilog takes in the call which it uses to track wireable functions.
    // CallEpi internally tracks all wired functions.

    CallEpiNode cepi = (CallEpiNode)gvn(new CallEpiNode(call,Env.DEFMEM));
    Node ctrl = gvn(new CProjNode(cepi.keep()));
    if( ctrl.is_copy(0)!=null ) ctrl = ctrl.is_copy(0); // More aggressively fold, so Thunks can more aggressively assert
    set_ctrl(ctrl);
    set_mem(gvn(new MProjNode(cepi))); // Return memory from all called functions
    // As soon as CEPI is unkeep, a whole lotta things are allowed, including
    // e.g. inlining
    if( !cepi._is_copy ) {
      Env.GVN.add_work_all(cepi);
      for( int i = 0; i < cepi.nwired(); i++ )
        Env.GVN.add_inline(cepi.wired(i).fun());
    } else Env.GVN.add_flow(cepi);
    return gvn(new ProjNode(cepi.unkeep(),REZ_IDX));
  }

  // Whack current control with a syntax error
  private ErrNode err_ctrl1( ErrMsg msg ) { return init(new ErrNode(Env.START,msg)); }
  private ErrNode err_ctrl2( String msg ) { return init(new ErrNode(ctrl(),errMsg(),msg)).unkeep(); }
  private void err_ctrl0(String s) { err_ctrl3(s,errMsg()); }
  private void err_ctrl3(String s, Parse open) {
    set_ctrl(gvn(new ErrNode(ctrl(),open,s)));
  }

  // Make a private clone just for delayed error messages
  private Parse( Parse P ) {
    _prims= P._prims;
    _src  = P._src;
    _buf  = P._buf;
    _x    = P._x;
    _lines= P._lines;
    _gvn  = P._gvn;
    _lastNWS = P._lastNWS;
    _e    = null;  _nf  = null;  _pp  = null;  _str = null;
  }
  // Delayed error message, just record line/char index and share code buffer
  Parse errMsg() { return errMsg(_x); }
  Parse errMsg(int x) { Parse P = new Parse(this); P._x=x; return P; }
  Parse[] errMsgs(int... xs) {
    Parse[] Ps = new Parse[xs.length];
    for( int i=0; i<xs.length; i++ )
      Ps[i] = xs[i]==0 ? null : errMsg(xs[i]);
    return Ps;
  }

  // Build a string of the given message, the current line being parsed,
  // and line of the pointer to the current index.
  public String errLocMsg(String s) {
    if( s.charAt(0)=='\n' ) return s;
    // find line start
    int a=_x;
    while( a > 0 && _buf[a-1] != '\n' ) --a;
    if( _buf[a]=='\r' ) a++; // do not include leading \n or \n\r
    // find line end
    int b=_x;
    while( b < _buf.length && _buf[b] != '\n' ) b++;
    if( b < _buf.length ) b--; // do not include trailing \n or \n\r
    // Find line number.  Bin-search returns the insertion-point, which is the NEXT
    // line unless _x is exactly a line start.
    int line = _lines.binary_search(_x); // Find zero-based line insertion point
    if( line == _lines._len ||  _lines.at(line)>_x ) line--;
    // error message using 1-based line
    SB sb = new SB().p(_src).p(':').p(line+1).p(':').p(s).nl();
    sb.p(new String(_buf,a,b-a)).nl();
    int line_start = a;
    for( int i=line_start; i<_x; i++ )
      sb.p(' ');
    return sb.p('^').nl().toString();
  }
  // Handy for the debugger to print

  @Override public String toString() { return new String(_buf,_x,_buf.length-_x); }
  @Override public boolean equals(Object loc) {
    if( this==loc ) return true;
    if( !(loc instanceof Parse) ) return false;
    Parse p = (Parse)loc;
    return _x==p._x && _src.equals(p._src);
  }
  @Override public int hashCode() {
    return _src.hashCode()+_x;
  }
  @Override public int compareTo(Parse loc) {
    int x = _src.compareTo(loc._src);
    if( x!=0 ) return x;
    return _x - loc._x;
  }
}
