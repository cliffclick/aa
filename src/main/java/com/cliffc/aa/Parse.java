package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;
import org.jetbrains.annotations.NotNull;

import java.lang.reflect.Field;
import java.text.NumberFormat;
import java.text.ParsePosition;
import java.util.BitSet;

import static com.cliffc.aa.AA.*;
import static com.cliffc.aa.type.TypeFld.Access;
import static com.cliffc.aa.type.TypeStruct.CANONICAL_INSTANCE;

/*** an implementation of language AA
 *
 *  GRAMMAR:
 *  prog = stmts END
 *  stmts= [tstmt|stmt][; stmts]*[;]? // multiple statements; final ';' is optional
 *  tstmt= tid = :type             // type identifier assignment
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
 *  post = ->field                 // deref an alloc
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
 *  struct=@{ stmts }              // Anonymous struct declaration, assignments define fields
 *  fact = struct                  // A fact is also a struct
 *  tuple= (stmts,[stmts,])        // Tuple; final comma is optional, first comma is required
 *  alloc= * [ tuple, struct ]     // Stuff a struct/tuple into memory and get a pointer
 *  binop= +-*%&|/<>!= [ ]=        // etc; primitive lookup; can determine infix binop at parse-time
 *  uniop= -!~# a                  // etc; primitive lookup; can determine infix uniop at parse-time
 *  bop+ = [                       // Balanced/split operator open
 *  bop- = ] ]= ]:=                // Balanced/split operator close
 *  func = { [id[:type]* ->]? stmts} // Anonymous function declaration, if no args then the -> is optional
 *                                 // Pattern matching: 1 arg is the arg; 2+ args break down a (required) tuple
 *  str  = [.\%]*                  // String contents; \t\n\r\% standard escapes
 *  str  = %[num]?[.num]?fact      // Percent escape embeds a 'fact' in a string; "name=%name\n"
 *
 *  type = tcon | tid | tvar | [?!]tptr | [?]tfun // "?" is nilable-ref, "!" is not-nil ref, missing is value-type
 *  tptr = tary | tstruct | ttuple
 *  tid  = type identifier         // NOT all-upper-case; LHS of type assignment
 *  tvar = HM type variable        // ALL upper-case; scoped this type expr only
 *  tcon = = ifex                  // Noticed extra '=', must bake down to a constant; usually for fcns
 *  tfun = { [[type]* -> ]? type } // Mirrors func decls; ie. map=: {{A->B} [A] -> [B]}
 *  tary = [type]                  // Array types
 *  ttuple = ( [[type],]* )        // Tuple types are just a list of optional types;
 *                                 // the count of commas dictates the length, zero commas is zero length.
 *                                 // Tuple fields are always final.
 *  tstruct= [tid:]@{ [tfld;]* };  // Optional named type to extend, list of fields
 *  tfld = id [:type | tcon]       // Field name, option type or const-expr
 *

 *
 * Structs and Types:
 *
 * Structs are a collection of fields; fields name other values.  All fields
 * can be optionally typed; the types can be forward references.  Missing types
 * are inferred.
 *
 * The same struct syntax is used in 4 cases: A normal object allocation, an
 * anonymous type struct, a named value-type, and a named reference type.
 *
 * Normal values (e.g. primitives) have no memory identity, are not allocated
 * and the "==" test is deep: each field is tested via "==" and this is a
 * bitwise test.  Hence simple primitive ints and flts are just tested via a
 * simple bit test.
 *
 * Value types (Vals) are a collection of normal values; the aggregate is
 * itself a value; it has no memory identity (pointer), is not allocated, is
 * not freed, is pass-by-value and does not allow side-effects on members.
 * Under the hood optimizations may do, e.g. COW optimizations.
 *
 * Anonymous struct declarations have fields and field modifiers, but do not
 * allow any exprs.  They are a type, not a value.
 *
 * Normal objects have a memory identity (pointer), require allocation and
 * lifetime management.  The "==" test is via ref/pointer only.  They have
 * mutable fields and allow side-effects.  The construction allows expressions
 * which are executed as the struct is built.
 *
 * Vals and Refs (reference) types are top-level named type assignments.  They
 * make a constructor; a Val constructor makes values and a Ref constructor
 * makes normal objects.  Constructors are always automatically defined; if you
 * want a classic C++ or Java constructor, make a factory function instead.
 *
 * All fields can be marked mutable or not; the default varies.
 *
 * All fields require initialization; if an expr is not provided either a 0 or
 * an argument will be used in the constructor.  This varies from Vals vs Refs.
 *
 * If an expression is a constant, it is precomputed and moved into a prototype
 * object (i.e. a C++ or Java "class" object), will be fetched on demand and
 * takes no space in object instances.  This is the common case for instance
 * functions and global constants.
 *
 *      Syntax             Obj         Val           Ref       Anon
 *  fld [:type]     ;   r/w  ,  0   final, arg    r/w,    0    r/w     // arg in ValType, 0   elsewhere
 *  fld [:type]  =  ;   final,  0   final, arg    final, arg   final   //  0  in ObjType, arg elsewhere
 *  fld [:type] :=  ;   r/w  ,  0   error         r/w,    0    r/w     // err in ValType; no mutable fields
 *  fld [:type]  =e0;   final, e0   final, e0     final, e0    error   //                                    error in Anon, no value
 *  fld [:type] :=e0;   r/w  , e0   error         r/w,   e0    error   // err in ValType; no mutable fields; error in Anon, no value
 *
 *
 * The Display
 *
 * The Parser builds an IR presentation of the program semantics, which has
 * some subtleties.  See FunNode and CallNode for how function headers adnd
 * call sites are represented.  See FunPtrNode for a discussion on the "fat"
 * function pointers AA uses.  Included in function pointer is the Display, or
 * "Environment" variable - a hidden extra variable representing the accessible
 * call-stack of non-local variables.  AA supports full closures, and a full
 * closure requires its stack to be heap allocated.  Hence the display might be
 * implemented as a non-local stack offset or it might be a heap object.
 * Keeping this explicit in the IR allows me to clone an outer function with a
 * escaping display without requiring cloning all the escaping inner functions.

 * Example:  Simple function to generate a private counter:
 *    gen = { cnt; ({cnt},{cnt++}) };
 *    (cntA,incA) = gen();  // Generate A counter, with a getter and incrementer
 *    (cntB,incB) = gen();  // Generate B counter, with a getter and incrementer
 *    incA(); incA(); incB();       // Now counter A=2 and B=1
 *    assert cntA()==2 && cntB==1;  // Assert counters are independent
 *
 * Here the variable 'cnt' escapes the lifetime of 'gen' and gen's display must
 * be stack allocated.
 *
 * Example: Same, except the inner functions are brought out at the top-level:
 *    _cnt = { cnt  } // Direct access to 'gen.cnt'
 *    _inc = { cnt++} // Direct access to 'gen.cnt'
 *    gen = { cnt; ( _cnt, _inc ) }
 * And then we clone 'gen':
 *    gen2 = { cnt; ( _cnt, _inc ) }
 * But _cnt and _inc refer to the original 'gen' counter and not the new one.
 *
 * Example: Same, except the display is explicit:
 *    _cnt = { dsp -> dsp.cnt  } // Code, not fptr, needs display
 *    _inc = { dsp -> dsp.cnt++} // Code, not fptr, needs display
 *    gen  = { dsp  = @{cnt}; ( (_cnt,dsp ), (_inc,dsp ) ) }
 * And cloning gen:
 *    gen2 = { dsp2 = @{cnt}; ( (_cnt,dsp2), (_inc,dsp2) ) }
 * Here the two 'gen's can share their inner functions but use different displays.
 *
 *
 * The Display is also available during @{} structure initialization, as a
 * default argument to nested functions.
 *
 * Example:
 *   circle = @{ r=1.0; area = { -> 2*math.pi*r } }  // Uses 'r'
 *   square = @{ x=1.2; area = { -> x*x } }          // Uses 'x'
 *
 * Each following init code is allowed to use all the fields that came before
 * it (plus itself for recursive functions), and is treated like a function
 * taking a hidden display argument of the structure itself.
 *
 * Example: x = @{ fld1=init1; fld2=init2; ... }
 * Becomes: x = @{ fld1=0; fld2=0; ... }; x.fld1=init1(x); x.fld2=init2(x);...
 * Except the init1 does not get to use any x fields, the init2 call can only
 * use fld1 and so forth.  The init codes can change mutable fields as well.
 *
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
  String dumprpo() { return Env.ROOT.dumprpo(false,false,false); }// debugging hook

  /** Parse a top-level:
   *  prog = stmts END */
  public ErrMsg prog() {
    Node res = stmts();
    if( res == null ) res = Env.ANY;
    scope().set_rez(res);  // Hook result
    // Close file scope; no more program text in this file, so no more fields to add.
    scope().stk().close();
    return skipWS() == -1 ? null : ErrMsg.trailingjunk(this);
  }

  /** Parse a list of statements; final semicolon is optional.
   *  stmts= [tstmt or stmt] [; stmts]*[;]?
   */
  private Node stmts() { return stmts(false); }
  private Node stmts(boolean lookup_current_scope_only) {
    Node stmt = tstmt(), last=null;
    if( stmt == null ) stmt = stmt(lookup_current_scope_only);
    while( stmt != null ) {
      if( !peek(';') ) return stmt;
      int idx = stmt.push();
      stmt = tstmt();
      if( stmt == null ) stmt = stmt(lookup_current_scope_only);
      last = Node.pop(idx);
      if( stmt == null ) {
        if( peek(';') ) { _x--; stmt=last; }   // Ignore empty statement
      } else if( !last.is_dead() && stmt != last) kill(last); // prior expression result no longer alive in parser
    }
    return last;
  }

  /** A type-statement assigns a type to a type variable.  Type variable
   *  assignments are always final, and can not exist before assignment (hence
   *  a variable cannot have a normal value and be re-assigned as a type
   *  variable).
   *
   *  tstmt = tvar = : type  // Value type
   *
   *  Value types are final-assigned; all fields are final and immutable.
   *  Fields not otherwise assigned are required by the constructor.  The
   *  constructor wraps the fields with a simple name; the result is not
   *  allocated (compiler lifetime managed), has no identity, and uses bit-wise
   *  comparisons.  Value types support field lookups on structs, with fields
   *  set with constant expressions being moved to the prototype object (i.e.
   *  "class" object).
   *
   *
   *  tstmt = tvar = : [?!]type // Reference type
   *
   *  Reference types are mutable-assigned; fields are mutable by default and
   *  mutable fields are not filled in by the constructor.  The constructors do
   *  allocation; the result has an identity, an explicit lifetime needing
   *  management, and uses pointer-comparison.  As with value types, fields set
   *  with final constant expressions are moved to the prototype.
   */
  private Node tstmt() {
    int oldx = _x;
    String tok = token();      // Scan for tvar
    if( tok == null || !peek('=') || !peek(':') )
      { _x=oldx; return null; } // Not a type assignment
    byte c = skipWS();
    if( c == -1 ) return null;  // No next character
    tok = tok.intern();
    String tname = (tok+":").intern(); // As a type name
    boolean is_val = !(c=='?' || c=='!'); // Value vs reference type

    // Types are forward-defined in two contexts, so either or both might
    // already have happened: as a type (in a type annotation) and as a
    // standard fref in a fact() (probably as a constructor call).
    // Look for a prior type assignment, from e.g. a type annotation

    // Make a forward-ref constructor, if not one already
    UnresolvedNode construct = (UnresolvedNode)_e.lookup(tok);
    if( construct==null ) construct = val_fref(tok,errMsg());
    else if( !construct.is_forward_ref() )
      return err_ctrl2("Cannot re-assign val '"+tok+"' as a type");
    construct.scoped();

    // Make a forward-ref type, if not one already
    StructNode typenode  = _e.lookup_type(tname);
    if( typenode == null ) typenode = type_fref(tname,is_val); // None, so create
    else throw unimpl(); // Double-define error

    // Nest an environment for parsing named type contents, usually const-expr initializers
    int pidx;
    try( Env e = new Env(_e, null, false, ctrl(), mem(), _e._scope.stk(), typenode) ) {
      _e = e;                   // Push nested environment

      Type newtype = type(false,typenode);
      if( newtype==null ) return err_ctrl2("Missing type after ':'");

      // Value or reference type
      if( newtype instanceof TypeMemPtr ) {
        typenode.close();
        typenode.define();                           // No longer a forward ref
        if( is_val ) {
          //// Build a default constructor, add to the pile of constructors
          //construct.add_def(typenode.defalt().fill());
          //construct.define();     // Value type is defined
          //Env.GVN.add_flow(construct);
          if( true ) throw unimpl();
        } else
          throw unimpl();         // Reference type

      } else {
        // Other types?  e.g. defining a named function-type needs a breakdown of
        // the returned function to make a TypeFunSig.  No constructor in this
        // case, but can be used in type-checks.
        // TODO: Need to toss the un-needed typenodeb
        throw unimpl();
      }

      e._par._scope.set_ctrl(ctrl()); // Carry any control changes back to outer scope
      e._par._scope.set_mem (mem ()); // Carry any memory  changes back to outer scope
      _e = e._par;                    // Pop nested environment
      pidx = construct.push();        // A pointer to the constructed object
    } // Pop lexical scope around type parse

    return Node.pop(pidx);
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
      if( ifex==null ) ifex=con(TypeNil.NIL);
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
    while( true ) {
      skipWS();
      int oldx = _x;            // Unwind token parse point
      Parse badf = errMsg();    // Capture location in case of field error
      String tok = token();     // Scan for 'id = ...'
      if( tok == null ) break;  // Out of ids
      int oldx2 = _x;           // Unwind assignment flavor point
      Type t = TypeNil.SCALAR;
      // x  =: ... type  assignment, handled before we get here
      // x  =  ... final assignment
      // x :=  ... var   assignment
      // x : type  = ... typed final assignment
      // x : type := ... typed var   assignment
      // x : nontype = ... error, missing type
      // p? x : nontype ... part of trinary
      Parse badt = errMsg();    // Capture location in case of type error
      if( peek(":=") ) _x=oldx2; // Avoid confusion with typed assignment test
      else if( peek(':') && (t=type(true,null))==null ) { // Check for typed assignment
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
          _x--;                 // Push back statement end
          default_nil=true;     // Shortcut def of nil
          rs.set(toks._len);    // Shortcut mutable
        } else {
          _x = oldx; // Unwind the token parse, and try an expression parse
          break;     // Done parsing assignment tokens
        }
      }

      toks .add(tok.intern());
      ts   .add(t  );
      badfs.add(badf);
      badts.add(badt);
    }

    // Normal statement value parse
    Node ifex = default_nil ? Env.XNIL : ifex(); // Parse an expression for the statement value
    // Check for no-statement after start of assignment, e.g. "x = ;"
    if( ifex == null ) {        // No statement?
      if( toks._len == 0 ) return null;
      ifex = err_ctrl2("Missing ifex after assignment of '"+toks.last()+"'");
    }

    // Assign tokens to value
    for( int i=0; i<toks._len; i++ ) {
      String tok = toks.at(i);               // Token being assigned
      Access mutable = rs.get(i) ? Access.RW : Access.Final;  // Assignment is mutable or final
      ScopeNode scope = lookup_scope(tok,lookup_current_scope_only);
      ifex = do_store(scope,ifex,mutable,tok,badfs.at(i),ts.at(i),badts.at(i));
    }

    return ifex;
  }

  // Assign into display, changing an existing def
  private Node do_store(ScopeNode scope, Node ifex, Access mutable, String tok, Parse badf, Type t, Parse badt ) {
    if( ifex instanceof FunPtrNode fptr )
      fptr.bind(tok);           // Debug only: give name to function
    final int iidx = ifex.push();
    // Find scope for token.  If not defining struct fields, look for any
    // prior def.  If defining a struct, tokens define a new field in this scope.
    boolean create = scope==null;
    if( create ) {              // Token not already bound at any scope
      scope = scope();          // Create in the current scope
      StructNode stk = scope.stk();
      TypeFld fld = TypeFld.make(tok,t,Access.RW);
      stk.add_fld(fld, con(TypeNil.NIL),badf); // Create at top of scope as undefined
      scope.def_if(tok,mutable,true); // Record if inside arm of if (partial def error check)
    }
    Node ptr = get_display_ptr(scope); // Pointer, possibly loaded up the display-display
    Node mem = mem();
    Node stk = gvn(new LoadNode(mem,ptr,badf));
    Node stk2 = gvn(new SetFieldNode(tok,mutable,stk,Node.peek(iidx),badf));
    StoreNode st = new StoreNode(mem,ptr,stk2,badf);
    scope.replace_mem(st);
    if( !create )               // Note 1-side-of-if update
      scope.def_if(tok,mutable,false);
    if( mutable==Access.Final ) Oper.make(tok);
    return Node.pop(iidx);
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

    scope().push_if();          // Start if-expression tracking new defs
    int omem_x = mem().push();  // Keep until parse false-side
    Node ifex = init(new IfNode(ctrl(),expr));
    int ifex_x = ifex.push();   // Keep until parse false-side
    set_ctrl(gvn(new CProjNode(ifex,1))); // Control for true branch
    Node t_exp = stmt(false);               // Parse true expression
    if( t_exp == null ) t_exp = err_ctrl2("missing expr after '?'");
    ifex      = Node.pop(ifex_x);
    Node omem = Node.pop(omem_x); // Unstack the two
    int t_exp_x = t_exp .push();  // Keep until merge point
    int t_ctl_x = ctrl().push();  // Keep until merge point
    int t_mem_x = mem ().push();  // Keep until merge point

    scope().flip_if();       // Flip side of tracking new defs
    set_mem(omem);           // Reset memory to before the IF for the other arm
    set_ctrl(gvn(new CProjNode(ifex,0))); // Control for false branch
    Node f_exp = peek(':') ? stmt(false) : con(TypeNil.NIL);
    if( f_exp == null ) f_exp = err_ctrl2("missing expr after ':'");
    Node f_ctl = ctrl();
    Node f_mem = mem ();

    Node t_mem = Node.pop(t_mem_x);
    Node t_ctl = Node.pop(t_ctl_x);
    t_exp      = Node.pop(t_exp_x);

    Node ptr = get_display_ptr(scope()); // Pointer, possibly loaded up the display-display
    Parse bad = errMsg();
    t_mem = scope().check_if(true ,ptr,bad,t_ctl,t_mem); // Insert errors if created only 1 side
    f_mem = scope().check_if(false,ptr,bad,f_ctl,f_mem); // Insert errors if created only 1 side
    scope().pop_if();         // Pop the if-scope

    // Merge results
    RegionNode r = set_ctrl(init(new RegionNode(null,t_ctl,f_ctl)));
    set_mem(   init(new PhiNode(TypeMem.ALLMEM,bad,r,t_mem,f_mem)));
    Node rez = init(new PhiNode(TypeNil.SCALAR,bad,r,t_exp,f_exp)) ; // Ifex result

    Env.GVN.add_work_new(f_exp);
    Env.GVN.add_work_new(t_exp);
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
      int eidx = expr.push();   // Keep alive across argument parse
      Node arg = expr();
      if( arg==null ) return Node.pop(eidx);
      // To avoid the common bug of forgetting a ';', these must be on the same line.
      int line_last = _lines.binary_search(old_last);
      int line_now  = _lines.binary_search(_x);
      if( line_last != line_now ) {
        _x = oldx;  _lastNWS = old_last;  expr.unhook();
        return err_ctrl2("Lisp-like function application split between lines "+line_last+" and "+line_now+", but must be on the same line; possible missing semicolon?");
      }
      expr = do_call(errMsgs(oldx,oldx),args(Node.pop(eidx),arg)); // Pass the 1 arg
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
    Node lhs = _expr_higher(prec);
    if( lhs==null ) return null;
    while( true ) {             // Kleene star at this precedence
      // Look for a binop at this precedence level
      int opx = _x;             // Invariant: WS already skipped
      String tok = token0();
      Oper binop = Oper.bin_op(tok,prec);
      if( binop==null ) { _x=opx; return lhs; }
      _x -= binop.adjustx(tok); // Chosen op can be shorter than tok
      skipWS();
      int rhsx = _x;            // Invariant: WS already skipped
      // Get the oper function to call
      Node opfun = gvn(new FieldNode(lhs,binop._name));
      int fidx = opfun.push();
      Node rhs = _expr_higher_require(binop);
      // Emit the call to both terms
      // LHS in unhooked prior to optimizing/replacing.
      lhs = do_call(errMsgs(opx,lhsx,rhsx), args(Node.pop(fidx),rhs));
      // Invariant: LHS is unhooked
    }
  }

  // Get an expr at the next higher precedence, or a term, or null
  private Node _expr_higher( int prec ) {
    return prec+1 == Oper.MAX_PREC ? term() : _expr(prec+1);
  }
  private Node _expr_higher_require( Oper op ) {
    Node rhs = _expr_higher(op._prec);
    return rhs==null ? err_ctrl2("Missing term after '"+op._name+"'") : rhs;
  }

  // Short-circuit 'thunks' the RHS operator and passes it to a thunk-aware
  // primitive.  The primitive is required to fully inline & optimize out the
  // Thunk before we exit here.  However, the primitive can do pretty much what
  // it wants with the Thunk (currently nil-check LHS, then optionally Call the
  // thunk).
  private Node _short_circuit_expr(Node lhs, int prec, String bintok, Node op, int opx, int lhsx, int rhsx) {
    // Capture state so we can unwind after parsing delayed execution
    StructNode stk = scope().stk(); // Display
    Node old_ctrl = ctrl().keep(2);
    Node old_mem  = mem ().keep(2);
    op.keep(2);
    //TypeStruct old_ts = stk._ts;
    //Ary<Node> old_defs = stk._defs.deepCopy();
    //lhs.keep(2);

    // TODO: Drop thunk/thret.  Use "lazy arg" flag model.  Normal calls.

    // Insert a thunk header to capture the delayed execution
    //ThunkNode thunk = (ThunkNode)gvn(new ThunkNode(mem()));
    //set_ctrl(thunk);
    //set_mem (gvn(new ParmNode(MEM_IDX,"mem",thunk.keep(2),TypeMem.MEM,Env.DEFMEM,null)));
    //
    //// Delayed execution parse of RHS
    //Node rhs = _expr_higher_require(prec,bintok,lhs);
    //
    //// Insert thunk tail, unwind memory state
    //ThretNode thet = gvn(new ThretNode(ctrl(),mem(),rhs,Env.GVN.add_flow(thunk.unkeep(2)))).keep(2);
    //set_ctrl(old_ctrl.unkeep(2));
    //set_mem (old_mem .unkeep(2));
    //for( int i=0; i<old_defs._len; i++ )
    //  assert old_defs.at(i)==stk._defs.at(i); // Nothing peeked thru the Thunk & updated outside
    //
    //// Emit the call to both terms.  Both the emitted call and the thunk MUST
    //// inline right now.
    //lhs = do_call(errMsgs(opx,lhsx,rhsx), args(op.unkeep(2),lhs.unkeep(2),thet.unkeep(2)));
    //assert thunk.is_dead() && thet.is_dead(); // Thunk, in fact, inlined
    //
    //// Extra variables in the thunk not available after the thunk.
    //// Set them to Err.
    //if( stk._ts != old_ts ) {
    //  lhs.keep(2);
    //  for( int i=old_defs._len; i<stk._defs._len; i++ ) {
    //    // TODO: alignment between old_defs and struct fields
    //    String fname = stk._ts.fld_idx(i)._fld;
    //    String msg = "'"+fname+"' not defined prior to the short-circuit";
    //    Parse bad = errMsg(rhsx);
    //    Node err = gvn(new ErrNode(ctrl(),bad,msg));
    //    set_mem(gvn(new StoreNode(mem(),scope().ptr(),err,Access.Final,fname,bad)));
    //  }
    //  lhs.unkeep(2);
    //}
    //return lhs;
    throw unimpl();
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
  private Node term() {
    Node n;
    int oldx = _x;

    // Check for id++ / id--
    // These are special forms (for now) because they side-effect.
    String tok = token();
    if( tok != null ) {
      if( peek("++") && (n=inc(tok, 1))!=null ) return n;
      if( peek("--") && (n=inc(tok,-1))!=null ) return n;
    }

    // Check for prefix ops; no leading expr and require a trailing expr;
    // balanced ops require a trailing balanced close.
    Oper op = Oper.pre_bal(tok,_prims);
    if( op != null ) {
      _x -= op.adjustx(tok); // Chosen op can be shorter than tok
      Node e0 = term();
      if( e0 == null ) { return err_ctrl2("Missing term after operator '"+op+"'"); } // Parsed a valid leading op but missing trailing expr
      if( op.is_open() ) throw unimpl(); // Parse the close
      if( op._nargs!=1 ) throw unimpl(); // No binary/trinary allowed here
      // Load field e0.op2_ as TFP, and instance call.
      Node fun = gvn(new FieldNode(e0,op._name));
      n = do_call(errMsgs(0,oldx),args(fun));
    } else {
      // Normal leading term
      _x=oldx;
      n = tfact();
      if( n == null ) return null;
    }

    // Repeat until not a term.  Binary expressions have precedence, parsed in expr()
    while( true ) {             // Repeated application or field lookup is fine
      skipWS();                 //
      if( peek('.') ) {         // Field?
        if( peek('(') ) throw unimpl(); // Start of e0.( e1 ) syntax, TODO: bind instance fcn e1 with 'self' e0, producing a bound TFP
        int fld_start=_x;       // Get field start
        String fld = token0();  // Field name
        if( fld == null ) {     // Not a token, check for a field number
          int fldnum = field_number();
          if( fldnum == -1 ) {
            if( n._uses._len==0 ) n.kill();
            return err_ctrl2("Missing field name after '.'");
          }
          fld = ""+fldnum;      // Convert to a field name
        }
        fld=fld.intern();

        Node castnn = gvn(new CastNode(ctrl(),n,TypeMemPtr.ISUSED)); // Remove nil choice

        // Store or load against memory
        if( peek(":=") || peek_not('=','=')) {
          Access fin = _buf[_x-2]==':' ? Access.RW : Access.Final;
          Node stmt = stmt(false);
          if( stmt == null ) n = err_ctrl2("Missing stmt after assigning field '."+fld+"'");
          //else scope().replace_mem( new StoreNode(mem(),castnn,n=stmt.keep(),fin,fld ,errMsg(fld_start)));
          //skipWS();
          //return n.unkeep();
          throw unimpl();       // SetField before Store
        } else {
          Node st = gvn(new LoadNode(mem(),castnn,errMsg(fld_start)));
          n = gvn(new FieldNode(st,fld));
        }

      } else if( peek('(') ) {  // Attempt a function-call
        oldx = _x;              // Just past paren
        skipWS();               // Skip to start of 1st arg
        int first_arg_start = _x;
        int nidx = n.push();    // Keep alive across arg parse
        StructNode arg = tuple(oldx-1,stmts(),first_arg_start); // Parse argument list
        n = Node.pop(nidx);     // Function
        if( arg == null )       // tfact but no arg is just the tfact not a function call
          { _x = oldx; return n; }
        Parse[] badargs = arg.fld_starts(); // Args from tuple
        badargs[0] = errMsg(oldx-1); // Base call error reported at the opening paren
        n = do_call0(false,badargs,args(n,arg)); // Pass the tuple

      } else {
        // Check for balanced op with a leading term, e.g. "ary [ idx ]" or
        // "ary [ idx ]= val".
        oldx = _x;                         // Token start
        String tok0 = token0();
        if( tok0==null || !Oper.is_open(tok0) ) { _x=oldx; break;} // Not a balanced op

        int nidx = n.push();    // Preserve leading expr
        skipWS();               // Skip to start of stmts
        int oldx2 = _x;         // Statement start
        Node idx = stmts();     // Index expression
        if( idx==null ) { Node.pop(nidx); return err_ctrl2("Missing stmts after '"+tok0+"'"); }

        String tok1 = token0();
        Oper bcl = Oper.balanced(tok0,tok1);
        if( bcl==null ) { n.unhook(); return err_ctrl2("Missing close after '"+tok0+"'"); }

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
    if( scope==null ) {         // Token not already bound to a value
      do_store(null,con(TypeNil.NIL),Access.RW,tok,null,TypeNil.SCALAR,null);
      scope = scope();
    } else {                    // Check existing token for mutable
      if( !scope.is_mutable(tok) )
        return err_ctrl2("Cannot re-assign final val '"+tok+"'");
    }

    // Scope is discovered by walking lexical display stack.
    // Pointer to the proper display is found via ptr-walking live display stack.
    // Now properly load from the display.
    Node ptr = get_display_ptr(scope);
    Node ld = gvn(new LoadNode(mem(),ptr,null));
    Node n = gvn(new FieldNode(ld,tok));
    if( n.is_forward_ref() )    // Prior is actually a forward-ref
      return err_ctrl1(ErrMsg.forward_ref(this,((FunPtrNode)n)));
    // Do a full lookup on "+", and execute the function
    int nidx = n.push();
    Node plus = gvn(new FieldNode(n,"_+_"));
    Node inc = con(TypeStruct.make_int(TypeInt.con(d)));
    Node sum = do_call(errMsgs(0,_x,_x), args(plus,inc));
    Parse bad = errMsg();
    Node stf = gvn(new SetFieldNode(tok,Access.RW,ld,sum,bad));
    // Active memory for the chosen scope, after the call to plus
    scope().replace_mem(new StoreNode(mem(),ptr,stf,bad));
    return Node.pop(nidx);      // Return pre-increment value
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
    Type t = type(false,null);
    if( t==null ) { _x = oldx; return fact; } // No error for missing type, because can be ?: instead
    return typechk(fact,t,mem(),bad);
  }
  // Add a typecheck into the graph, with a shortcut if trivially ok.
  private Node typechk(Node x, Type t, Node mem, Parse bad) {
    return t == null || x._val.isa(t) ? x : gvn(new AssertNode(mem,x,t,bad,_e));
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
   *  fact = $$java_class
   */
  private Node fact() {
    if( skipWS() == -1 ) return null;
    byte c = _buf[_x];
    if( isDigit(c) ) return number();
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
    if( peek1(c,'{') ) return func();

    // Anonymous struct
    if( peek2(c,"@{") ) return struct();

    // Primitive parsing only, directly get a Java intrinsic implementation
    if( _prims && peek2(c,"$$") ) return java_class_node();

    // Check for a valid 'id'
    String tok = token0();
    tok = tok==null ? null : tok.intern();
    if( tok == null || Util.eq("_",tok)) { _x = oldx; return null; }
    if( Util.eq(tok,"=") || Util.eq(tok,"^") )
      { _x = oldx; return null; } // Disallow '=' as a fact, too easy to make mistakes
    ScopeNode scope = lookup_scope(tok,false);
    if( scope == null ) { // Assume any unknown id is a forward-ref of a recursive function
      // Ops cannot be forward-refs, so are just 'not a fact'.  Cannot declare
      // them as a undefined forward-ref right now, because the op might be the
      // tail-half of a balanced-op, which is parsed by term() above.
      if( isOp(tok) ) { _x = oldx; return null; }
      // Must be a forward reference
      return val_fref(tok,errMsg(oldx));
    }

    // Must load against most recent display update, in case some prior store
    // is in-error.  Directly loading against the display would bypass the
    // (otherwise alive) error store.
    Node ld = gvn(new LoadNode(mem(),get_display_ptr(scope),null));
    Node fd = gvn(new FieldNode(ld,tok));
    // If in the middle of a definition (e.g. a HM Let, or recursive assign)
    // then no Fresh per normal HM rules.  If loading from a struct or from
    // normal Lambda arguments, again no Fresh per normal HM rules.
    return ld.is_forward_ref() || !scope.stk()._is_closure
      ? fd
      : gvn(new FreshNode(_e._fun,fd));
  }


  /** Parse a tuple; first stmt but not the ',' parsed.
   *  tuple= (stmts,[stmts,])     // Tuple; final comma is optional
   */
  private StructNode tuple(int oldx, Node s, int first_arg_start) {
    StructNode nn = new StructNode(false,false);
    // First stmt is parsed already
    Parse bad = errMsg(first_arg_start);
    while( s!= null ) {         // More args
      TypeFld fld = TypeFld.make((""+(nn.len())).intern(),TypeNil.SCALAR,Access.Final);
      nn.add_fld(fld,s,bad);
      if( !peek(',') ) break;   // Final comma is optional
      skipWS();                 // Skip to arg start before recording arg start
      bad = errMsg();           // Record arg start
      s = stmts();              // Parse arg
    }
    require(')',oldx);          // Balanced closing paren
    return init(nn.close());    // No more field, init and return
  }


  /** Parse anonymous struct; the opening "@{" already parsed.  A lexical scope
   *  is made and new variables are defined here.  Next comes statements, with
   *  each assigned value becoming a struct member, then the closing "}".
   *    struct = \@{ stmts }
   *  Field syntax:
   *    id [:type] [amod [expr]]  // missing amod defaults to "id := 0"; missing expr defaults to "0"
   */
  private Node struct() {
    int oldx = _x-1, pidx;      // Opening @{
    try( Env e = new Env(_e, null, false, ctrl(), mem(), _e._scope.stk(), null) ) { // Nest an environment for the local vars
      _e = e;                   // Push nested environment
      stmts(true);              // Create local vars-as-fields
      require('}',oldx);        // Matched closing }
      assert ctrl() != e._scope;
      StructNode stk = e._scope.stk();
      stk.close();
      e._par._scope.set_ctrl(ctrl()); // Carry any control changes back to outer scope
      e._par._scope.set_mem (mem ()); // Carry any memory  changes back to outer scope
      _e = e._par;                    // Pop nested environment
      pidx = stk.push();              // A pointer to the constructed object
    } // Pop lexical scope around struct
    return Node.pop(pidx);
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
    // or when inside a struct definition: 'this'.
    StructNode par_stk = scope().stk();
    Node dsp = par_stk;

    //// Incrementally build up the formals
    //TypeStruct formals = TypeStruct.make("",false, TypeFld.make_dsp(par_stk._tptr));
    //TypeStruct no_args_formals = formals;
    //Ary<Parse> bads= new Ary<>(new Parse[1],0);
    //
    //// Parse arguments
    //while( true ) {
    //  skipWS();
    //  Parse badp = errMsg();   // Capture location in case of parameter error
    //  String tok = token();
    //  if( tok == null ) { _x=oldx; break; } // not a "[id]* ->"
    //  if( Util.eq((tok=tok.intern()),"->") ) break; // End of argument list
    //  if( !isAlpha0((byte)tok.charAt(0)) ) { _x=oldx; break; } // not a "[id]* ->"
    //  Type t = Type.SCALAR;    // Untyped, most generic type
    //  Parse bad = errMsg();    // Capture location in case of type error
    //  if( peek(':') &&         // Has type annotation?
    //      (t=type(true,null))==null ) { // Get type
    //    // If no type, might be "{ x := ...}" or "{ fun arg := ...}" which can
    //    // be valid stmts, hence this may be a no-arg function.
    //    if( bads._len-1 <= 2 ) { _x=oldx; break; }
    //    else {
    //      // Might be: "{ x y z:bad -> body }" which cannot be any stmt.  This
    //      // is an error in any case.  Treat as a bad type on a valid function.
    //      err_ctrl0(peek(',') ? "Bad type arg, found a ',' did you mean to use a ';'?" : "Missing or bad type arg");
    //      t = Type.SCALAR;
    //      skipNonWS();         // Skip possible type sig, looking for next arg
    //    }
    //  }
    //  if( formals.get(tok) != null ) err_ctrl3("Duplicate parameter name '" + tok + "'", badp);
    //  else formals = formals.add_fldx(TypeFld.make(tok,t,args_are_mutable)); // Accumulate args
    //  bads.add(bad);
    //}
    //// If this is a no-arg function, we may have parsed 1 or 2 tokens as-if
    //// args, and then reset.  Also reset to just the mem & display args.
    //if( _x == oldx ) { formals = no_args_formals;  bads.set_len(ARG_IDX); }
    //
    //// Build the FunNode header
    //FunNode fun = (FunNode)init(new FunNode(formals.nargs()).add_def(Env.ALL_CTRL));
    //int fun_idx = fun.push();
    //
    //// Record H-M VStack in case we clone
    ////fun.set_nongens(_e._nongen.compact());
    //// Build Parms for system incoming values
    //int rpc_idx = init(new ParmNode(CTL_IDX,fun,null,TypeRPC.ALL_CALL,Env.ALL_CALL)).push();
    //int clo_idx = init(new ParmNode(DSP_IDX,fun,null,par_stk._tptr   ,dsp         )).push();
    //Node mem    = init(new ParmNode(MEM_IDX,fun,null,TypeMem.ALLMEM  ,Env.DEF_MEM ));
    //
    //// Increase scope depth for function body.
    //int fidx;
    //try( Env e = new Env(_e, fun, true, fun, mem, par_stk, null) ) { // Nest an environment for the local vars
    //  _e = e;                   // Push nested environment
    //  // Display is special: the default is simply the outer lexical scope.
    //  // But here, in a function, the display is actually passed in as a hidden
    //  // extra argument and replaces the default.
    //  StructNode stk = e._scope.stk();
    //  stk.set_fld(TypeFld.make_dsp(par_stk._tptr),Node.pop(clo_idx));
    //  Env.GVN.revalive(stk,stk.mem());
    //
    //  // Parms for all arguments
    //  Parse errmsg = errMsg();  // Lazy error message
    //  assert fun==_e._fun && fun==_e._scope.ctrl();
    //  for( int i=ARG_IDX; i<formals.len(); i++ ) { // User parms start
    //    TypeFld fld = formals.get(i);
    //    //Node parm = gvn(new ParmNode(i,fld,fun,Env.ALL_PARM,errmsg));
    //    //scope().stk().add_fld(fld,parm,bads.at(i-ARG_IDX));
    //    throw unimpl(); // TODO: TypeFld has no order but formals and Parms do
    //  }
    //  stk.set_nargs(formals.nargs());
    //
    //  // Parse function body
    //  Node rez = stmts();       // Parse function body
    //  if( rez == null ) rez = err_ctrl2("Missing function body");
    //  require('}',oldx-1);      // Matched with opening {}
    //  stk.close();
    //
    //  // Merge normal exit into all early-exit paths
    //  assert e._scope.is_closure();
    //  rez = merge_exits(rez);
    //  // Standard return; function control, memory, result, RPC.  Plus a hook
    //  // to the function for faster access.
    //  Node xrpc = Node.pop(rpc_idx);
    //  Node xfun = Node.pop(fun_idx); assert xfun == fun;
    //  RetNode ret = (RetNode)gvn(new RetNode(ctrl(),mem(),rez,xrpc,fun));
    //  // Hook the function at the TOP scope, because it may yet have unwired
    //  // CallEpis which demand memory.  This hook is removed as part of doing
    //  // the Combo pass which computes a real Call Graph and all escapes.
    //  Env.SCP_0.add_def(ret);
    //  // The FunPtr builds a real display; any up-scope references are passed in now.
    //  //Node fptr = gvn(new FunPtrNode(null,ret,par_stk._is_val ? Env.ALL : par_stk));
    //  //
    //  //_e = e._par;            // Pop nested environment; pops nongen also
    //  //fidx = fptr.push();     // Return function; close-out and DCE 'e'
    //}
    //return Node.pop(fidx);
    throw unimpl();
  }

  private Node merge_exits(Node rez) {
    int ridx = rez.push();
    ScopeNode s = scope();
    Node ctrl = s.early_ctrl();
    Node mem  = s.early_mem ();
    Node val  = s.early_val ();
    s.early_kill();
    if( ctrl == null ) return Node.pop(ridx); // No other exits to merge into
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
      s.set_def(5,mem =new PhiNode(TypeMem.ALLMEM, null,(Node)null).keep());
      s.set_def(6,val =new PhiNode(TypeNil.SCALAR, null,(Node)null).keep());
    }
    ctrl.add_def(ctrl());
    mem .add_def(mem ());
    val .add_def(rez   );
    set_ctrl(Env.XCTRL);
    set_mem (con(TypeMem.ANYMEM));
    return con(TypeNil.NIL);
  }

  /** A balanced operator as a fact().  Any balancing token can be used.
   *  bterm = [ stmts ]              // size  constructor
   *  bterm = [ stmts, [stmts,]* ]   // tuple constructor
   */
  Node bfact(int oldx, Node bfun) {
    skipWS();
    int oldx2 = _x;             // Start of stmts
    Node s = stmts();
    if( s==null ) { _x = oldx; return null; } // A bare "()" pair is not a statement
    if( peek(',') ) {
      _x --;                    // Reparse the ',' in tuple
      throw unimpl();
    }
    //require(bfun.funptr().fun()._bal_close,oldx);
    //return do_call(errMsgs(oldx,oldx2),args(bfun,s));
    throw unimpl();
  }

  // Must be a valid java class name on the current class path that subclasses
  // Node.  Must have a no-arg constructor.  Returned node must be valid in the
  // aa context.
  @SuppressWarnings("unchecked")
  private Node java_class_node() throws RuntimeException {
    int x = _x;
    while( isJava(_buf[_x]) ) _x++;
    String str = "com.cliffc.aa.node."+new String(_buf,x,_x-x);
    try {
      Class clazz = Class.forName(str);
      Node n = (Node)clazz.getConstructor().newInstance();

      // Common primitive shortcut: if followed by a '(' assume a full normal
      // function call, which will just normally inlines to a direct prim use.
      // Go ahead and directly build the primitive.  Only works if the
      // primitive does return memory.
      skipWS();
      int oldx = _x;
      if( peek('(') ) {
        PrimNode p = (PrimNode)n;
        int nargs = p._tfp.nargs();
        boolean  read_mem = false; //np != null && np._reads;
        boolean write_mem = false; //np!=null;
        int nidx = Env.GVN.add_flow(n).push();
        n.add_def(null);        // No control
        n.add_def(read_mem ? mem() : null);
        for( int i=DSP_IDX; i<nargs; i++ ) {
          n.add_def(stmts());
          if( i<nargs-1 ) require(',',oldx);
        }
        Node xn = Env.GVN.add_flow(Node.pop(nidx));
        assert xn==n;
        if( write_mem ) {
          //set_mem(init(new MrgProjNode((NewNode)n,mem())));
          //n = init(new ProjNode(n,REZ_IDX));
          throw unimpl();
        }
        require(')',oldx);
        return n;
      }

      // Else build a function which calls the primitive, and return a
      // FunPtrNode - which must be in a valid aa context for a fptr.
      return n.clazz_node();
    } catch( Exception e ) {
      System.err.println("Did not find a public no-arg constructor in a public class for "+str);
      throw new RuntimeException(e); // Unrecoverable
    }
  }

  // Must be a valid java class name on the current class path with the named
  // Field of type "Type".  Returns the field contents.
  private Type java_class_type() throws RuntimeException {
    int x = _x;
    while( isJava(_buf[_x]) ) _x++;
    String[] strs = new String(_buf,x,_x-x).split("\\$");
    String sclz = "com.cliffc.aa.type."+strs[0];
    String sfld = strs[1];
    try {
      Class clazz = Class.forName(sclz);
      Field f = clazz.getDeclaredField(sfld);
      return (Type)f.get(null);
    } catch( Exception e ) { throw new RuntimeException(e); } // Unrecoverable
  }


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
  static boolean isOp(String s, boolean prims) {
    if( s==null || s.isEmpty() ) return false;
    byte c = (byte)s.charAt(0);
    if( prims && c=='$' ) return false; // Disallow $$ operator during prim parsing; ambiguous with $$java_class_name
    if( !Oper.isOp0(c) && (c!='_' || !Oper.isOp0((byte)s.charAt(1))) ) return false;
    for( int i=1; i<s.length(); i++ )
      if( !Oper.isOp1((byte)s.charAt(i)) ) return false;
    return true;
  }

  // Allows '+' and includes '_+_'
  boolean isOp(String s) { return isOp(s,_prims); }

  // Parse a number; WS already skipped and sitting at a digit.  Relies on
  // Javas number parsing.
  private Node number() {
    _pp.setIndex(_x);
    Number n = _nf.parse(_str,_pp);
    _x = _pp.getIndex();
    if( n instanceof Long   ) {
      if( _buf[_x-1]=='.' ) _x--; // Java default parser allows "1." as an integer; pushback the '.'
      return con(PrimNode.make_int(n.longValue()));
    }
    if( n instanceof Double ) return con(PrimNode.make_flt(n.doubleValue()));
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
    //NewNode nnn = (NewNode)gvn( new NewStrNode.ConStr(str) );
    //set_mem(gvn(new MrgProjNode(nnn,mem())));
    //return gvn( new ProjNode(nnn,REZ_IDX));
    throw unimpl();
  }

  /*
   *  type = tcon | tid | tvar | [?!]tptr | [?]tfun // "?" is nilable-ref, "!" is not-nil ref, missing is value-type
   *  tptr = tary | tstruct | ttuple
   *  tid  = type identifier         // NOT all-upper-case; LHS of type assignment
   *  tvar = HM type variable        // ALL upper-case; scoped this type expr only
   *  tcon = = ifex                  // Noticed extra '=', must bake down to a constant; usually for fcns
   *  tfun = { [[type]* -> ]? type } // Mirrors func decls; ie. map=: {{A->B} [A] -> [B]}
   *  tary = [type]                  // Array types
   *  ttuple = ( [[type],]* )        // Tuple types are just a list of optional types;
   *                                 // the count of commas dictates the length, zero commas is zero length.
   *                                 // Tuple fields are always final.
   *  tstruct= [tid:]@{ [tfld;]* };  // Optional named type to extend, list of fields
   *  tfld = id [:type | tcon]       // Field name, option type or const-expr
   */
  private Type type(boolean allow_fref, StructNode proto) {
    if( _prims && peek("$#") ) return java_class_type();

    // First character to split type out:
    return switch( skipWS() ) {
    case '{' -> throw unimpl(); // Function parse
    case '@' -> tstruct(proto); // Struct parse
    case '[' -> throw unimpl(); // Array parse
    case '(' -> ttuple();       // Tuple parse
    case '=' -> throw unimpl(); // Const ifex parse
    case '?' -> throw unimpl(); //     Nilable-ref parse
    case '!' -> throw unimpl(); // Not-nilable-ref parse
    default  -> tid(allow_fref);// TID/TVAR parse
    };
  }

  // Parse a struct type.  Side-effect constant fields into proto.
  // Disallows 'x := expr'
  private TypeMemPtr tstruct(StructNode proto) {
    if( !peek("@{") ) return null;
    // Parse fields
    while( true ) {
      // Parse a field token
      String tok = token();
      if( tok==null ) break;
      tok = tok.intern();
      // Parse the field type
      Node val;  Type t;   Access access;
      if( peek('=') ) {
        access = Access.Final;
        val = tcon();           // Arbitrary AA const-expr, not a type
        t = val._val;           // Type from the parse-time node type.
        Oper.make(tok);
        if( val instanceof FunPtrNode fptr )
          fptr.bind(tok);       // Debug only: give name to function
      } else {
        access = Access.RW;     // Arbitrary AA type, not const-expr
        t = peek(':') ? type(true,null) : TypeNil.SCALAR;
        val = con(t);
      }
      // Insert the field into the structure.
      // FunPtrs are allowed to stack, if the signatures do not overlap.
      TypeFld tfld = TypeFld.make(tok.intern(),t,access);
      if( val instanceof FunPtrNode fptr ) proto.add_fun(tok ,access,fptr,null);
      else                                 proto.add_fld(tfld       , val,null);
      if(  peek('}') ) break;          // End of struct,  no trailing semicolon?
      if( !peek(';') ) throw unimpl(); // Not a type
      if(  peek('}') ) break;          // End of struct, yes trailing semicolon?
    }
    return (TypeMemPtr)proto._val;
  }

  // Parse an const ifex.
  private Node tcon() {
    Node n = ifex();
    if( n==null ) throw unimpl(); // Missing ifex expecting a const-expr
    if( !n._val.is_con() ) throw unimpl(); // Not a const expr
    return n;
  }

  // Parse a tuple type.
  private Type ttuple() {
    int oldx = _x;
    peek('(');
    TypeStruct ts = TypeStruct.malloc("",false,TypeFlds.EMPTY);
    while(true) {
      Type t = type(false,null);
      if( t==null ) { _x=oldx; return ts.free(null); }
      throw unimpl();
    }
  }


  // Type-id or type-var parse
  private Type tid(boolean allow_fref) {
    String tok = token();
    if( tok==null ) return null;
    if( Util.isUpperCase(tok) )
      throw unimpl();           // Reserved for type variables
    // Shortcut for the two primitive types
    String tname = (tok+":").intern();
    StructNode nnn = _e.lookup_type(tname);
    if( nnn == null ) {
      if( !allow_fref ) // Forward-refs not allowed in this context
        return null;    // SO no type here
      nnn = type_fref(tname,false); // None, so create
    }
    // Clazzes have a canonical worse-case instance
    return nnn.get(CANONICAL_INSTANCE)._t;
  }

  // Create a value forward-reference.  Must turn into a function call later.
  // Called when seeing a name for the first time, in a function-call context,
  // OR when defining a type constructor.  Not allowed to forward-ref normal
  // variables, so this is a function variable, not yet defined.  Use an
  // Unresolved until it gets defined.
  private UnresolvedNode val_fref(String tok, Parse bad) {
    UnresolvedNode fref = init(UnresolvedNode.forward_ref(tok,bad));
    // Place in nearest enclosing closure scope, this will keep promoting until we find the actual scope
    StructNode stk = scope().stk();
    TypeFld fld = TypeFld.make(tok,TypeNil.SCALAR,Access.Final);
    stk.add_fld(fld,fref,null);
    return fref;
  }
  // Create a type forward-reference.  Must be type-defined later.  Called when
  // seeing a name in a type context for the first time.  Builds an empty type
  // NewNode and returns it.
  private StructNode type_fref(String tname, boolean is_val) {
    //NewNode tn = new NewNode(false,true,tname,BitsAlias.new_alias());
    //tn._val = tn.value();
    //_gvn.add_work_new(tn);
    //_e.add_type(tname,tn);
    //assert tn.is_forward_type();
    //return tn;
    throw unimpl(); // TODO: is_val
  }

  // --------------------------------------------------------------------------
  // Require a closing character (after skipping WS) or polite error
  private void require( char c, int oldx ) {
    if( peek(c) ) return;
    Parse bad = errMsg();       // Generic error
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
  private static boolean isJava  (byte c) { return isAlpha1(c) || (c=='$') || (c=='.'); }
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
  //private void create( String tok, Node n, Access mutable ) { scope().stk().create(tok,n,mutable); }

  // Get the display.  The function call passed in the display as a hidden
  // argument which we return here.
  private Node get_display_ptr( ScopeNode scope ) {
    // Issue Loads against the Display, until we get the correct scope.  The
    // Display is a linked list of displays, and we already checked that token
    // exists at scope up in the display.
    Env e = _e;
    ProjNode ptr = e._scope.ptr();
    Node mmem = mem();
    while( true ) {
      if( scope == e._scope ) return ptr;
      StructNode dsp = (StructNode)gvn(new LoadNode(mmem,ptr,null)); // Gen linked-list walk code, walking display slot
      ptr = (ProjNode)gvn(new FieldNode(dsp,"^"));
      e = e._par;                                 // Walk linked-list in parser also
    }
  }

  // Wiring for call arguments
  private Node[] args(Node a0                           ) { return _args(new Node[]{null,null,a0}); }
  private Node[] args(Node a0, Node a1                  ) { return _args(new Node[]{null,null,a0,a1}); }
  private Node[] args(Node a0, Node a1, Node a2         ) { return _args(new Node[]{null,null,a0,a1,a2}); }
  //private Node[] args(Node a0, Node a1, Node a2, Node a3) { return _args(new Node[]{null,null,a0,a1,a2,a3}); }
  private Node[] _args(Node[] args) {
    args[CTL_IDX] = ctrl();     // Always control
    args[MEM_IDX] = mem();      // Always memory
    return args;
  }

  // Insert a call, with memory splits.  Wiring happens later, and when a call
  // is wired it picks up projections to merge at the Fun & Parm nodes.
  private Node do_call( Parse[] bads, Node... args ) { return do_call0(true,bads,args); }
  private Node do_call0( boolean unpack, Parse[] bads, Node... args ) {
    CallNode call = (CallNode)gvn(new CallNode(unpack,bads,args));
    CallEpiNode cepi = (CallEpiNode)gvn(new CallEpiNode(call));
    int cidx = cepi.push();
    Node ctrl = gvn(new CProjNode(cepi));
    set_ctrl(ctrl);
    set_mem(gvn(new MProjNode(Node.peek(cidx)))); // Return memory from all called functions
    // As soon as CEPI is unkeep, a whole lotta things are allowed, including
    // e.g. inlining
    if( cepi._is_copy ) Env.GVN.add_flow(cepi);

    return gvn(new ProjNode(Node.pop(cidx),REZ_IDX));
  }

  // Whack current control with a syntax error
  private ErrNode err_ctrl1( ErrMsg msg ) { return init(new ErrNode(ctrl(),msg)); }
  private ErrNode err_ctrl2( String msg ) { return init(new ErrNode(ctrl(),errMsg(),msg)); }
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
