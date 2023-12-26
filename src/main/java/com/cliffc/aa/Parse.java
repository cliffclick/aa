package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;

import java.text.NumberFormat;
import java.text.ParsePosition;
import java.util.BitSet;

import static com.cliffc.aa.AA.*;
import static com.cliffc.aa.type.TypeFld.Access;

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
 *  tuple= (stmts,[stmts,])        // Tuple; final comma is optional, first comma is required
// In progress ideas
// *  fact = struct                  // A fact is also a struct
// *  fact = tuple                   // A fact is also a tuple
// *  fact = ptr                     // A fact is a ptr
// *  ptr  = &tuple, &struct         // Allocation; stuff a struct/tuple into memory and get a pointer
// *  fact = *ptr                    // Prefix ptr-deref; produces a LHS...
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
  private final String _src;    // Source for error messages; usually a file name
  private Env _e;    // Lookup context; pushed and popped as scopes come and go
  private final byte[] _buf;    // Bytes being parsed
  private int _x;               // Parser index
  private int _lastNWS;         // Index of last non-white-space char
  private final AryInt _lines;  // char offset of each line

  // List of Nodes mid-construction, not allowed to peephole away (yet)
  private final Ary<Node> _keeps;
  
  // Fields strictly for Java number parsing
  private final NumberFormat _nf;
  private final ParsePosition _pp;
  private final String _str;

  Parse( String src, Env env, String str ) {
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
    _keeps = new Ary<>(Node.class);
  }

  // Debugging hook
  String p() { return NodePrinter.prettyPrint(_keeps); }

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
      int bal = _keeps._len;    // Balanced keep-alives
      last = keep(stmt);
      stmt = tstmt();
      if( stmt == null ) stmt = stmt(lookup_current_scope_only);
      if( stmt == null ) {
        if( peek(';') ) { _x--; stmt=last; }   // Ignore empty statement
      }
      if( unkeep(last) != stmt && last.nUses()==0 )
        last.kill(); // prior expression result no longer alive in parser
      assert bal == _keeps._len; // Balanced keep-alives
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

    //// Make a forward-ref constructor, if not one already
    //ForwardRefNode construct = (ForwardRefNode)_e.lookup(tok);
    //if( construct==null ) construct = val_fref(tok,errMsg());
    //else if( !construct.is_forward_ref() )
    //  return err_ctrl2("Cannot re-assign val '"+tok+"' as a type");
    //construct.scoped();
    //
    //// Make a forward-ref type, if not one already
    //StructNode typenode  = _e.lookup_type(tname);
    //if( typenode == null ) typenode = type_fref(tname,is_val); // None, so create
    //else throw TODO(); // Double-define error
    //
    //// Nest an environment for parsing named type contents, usually const-expr initializers
    //int pidx;
    //try( Env e = new Env(_e, null, false, ctrl(), mem(), _e._scope.stk(), typenode) ) {
    //  _e = e;                   // Push nested environment
    //
    //  Type newtype = type(typenode);
    //  if( newtype==null ) return err_ctrl2("Missing type after ':'");
    //
    //  // Value or reference type
    //  if( newtype instanceof TypeMemPtr ) {
    //    typenode.close();
    //    typenode.define();                           // No longer a forward ref
    //    if( is_val ) {
    //      //// Build a default constructor, add to the pile of constructors
    //      //construct.add_def(typenode.defalt().fill());
    //      //construct.define();     // Value type is defined
    //      //Env.GVN.add_flow(construct);
    //      if( true ) throw TODO();
    //    } else
    //      throw TODO();         // Reference type
    //
    //  } else {
    //    // Other types?  e.g. defining a named function-type needs a breakdown of
    //    // the returned function to make a TypeFunSig.  No constructor in this
    //    // case, but can be used in type-checks.
    //    // TODO: Need to toss the un-needed typenodeb
    //    throw TODO();
    //  }
    //
    //  e._par._scope.ctrl(ctrl()); // Carry any control changes back to outer scope
    //  e._par._scope.mem (mem ()); // Carry any memory  changes back to outer scope
    //  _e = e._par;                    // Pop nested environment
    //  pidx = construct.push();        // A pointer to the constructed object
    //} // Pop lexical scope around type parse
    //
    //return Node.pop(pidx);
    throw TODO();
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
      if( ifex==null ) ifex = Env.NIL;
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
      Parse badt = errMsg();    // Capture location in case of type error
      if( peek(":=") ) _x=oldx2; // Avoid confusion with typed assignment test
      else if( peek(':') && (t=type())==null ) { // Check for typed assignment
        if( _e.test_if() ) _x = oldx2; // Grammar ambiguity, resolve p?a:b from a:int
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
      ts   .add(t);
      badfs.add(badf);
      badts.add(badt);
    }

    // Normal statement value parse
    Node ifex = default_nil ? Env.NIL : ifex(); // Parse an expression for the statement value
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

  // Assign into display, changing an existing def.
  // The scope of the assignment is 'scope', or null to create in the local scope.
  private Node do_store(ScopeNode scope, Node ifex, Access mutable, String tok, Parse badf, Type t, Parse badt ) {
    Node debug = ifex instanceof BindFPNode bind ? bind.fp() : ifex;
    if( debug instanceof FunPtrNode fptr )
      fptr.bind(tok);           // Debug only: give name to function
    // Find scope for token.  If not defining struct fields, look for any
    // prior def.  If defining a struct, tokens define a new field in this scope.
    boolean create = scope==null;
    if( create ) {              // Token not already bound at any scope
      scope = scope();          // Create in the current scope
      StructNode stk = scope.stk();
      // Here we make a private Env.ANY copy, so Combo gets a private Leaf for
      // each initial variable set.  If we somehow skipped this setting
      // (e.g. using null for ANY), then Combo could figure out not to unify
      // unrelated variables.
      stk.add_fld (tok,Access.RW, Node.con(Type.ANY),badf); // Create at top of scope as undefined
    }
    
    // Assert type if asked for
    if( t!=null )
      ifex = new AssertNode(mem(), ifex, t, badf).peep();

    // See if assigning over a forward-ref.
    int idx = scope().stk().find(tok);
    if( idx != -1 && scope().stk().in(idx) instanceof ForwardRefNode fref ) {
      fref.assign( ifex, tok ); // Define & assign the forward-ref
      return ifex; // No need to re-assign; was already assigned at initial ref point
    }

    // Save across display load
    int bal = _keeps._len;    // Balanced keep-alives
    keep(ifex);

    // Load the display/stack-frame for the defining scope.
    Node ptr = get_display_ptr(scope); // Pointer, possibly loaded up the display-display
    // Store into the defining scope (not necessarily local scope)
    mem( new StoreNode(mem(),ptr,ifex,tok,mutable,badf) );
    if( mutable==Access.Final ) Oper.make(tok,false);
    ifex = unkeep(ifex).peep();
    assert bal == _keeps._len;  // Balanced keep-alives
    return ifex;
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

    int bal = _keeps._len;      // Balanced keep-alives

    Node omem = keep(mem());    // Keep until parse false-side
    // KEEP: {MEM}
    Node ifex = keep(new IfNode(ctrl(),expr).peep());
    // KEEP: {MEM, IFEX}
    ctrl(new CProjNode(ifex,1).peep()); // Control for true branch
    
    // True side
    try( Env e = _e = new Env(_e, null, -1, ctrl(), mem(), scope().ptr(), null) ) { // Nest an environment for the local vars
      // TODO: Insert cast
      Node t_exp = stmt(false); // Parse true expression
      if( t_exp == null ) t_exp = err_ctrl2("missing expr after '?'");
      scope().stk().close();
      scope().setDef(REZ_IDX,t_exp);
      // KEEP: {MEM, IFEX}
      _e = e._par;            // Pop nested environment
    }
    
    // Shuffle lifetimes for the true/false flip
    ScopeNode t_scope = scope();
    // KEEP:{MEM, IFEX}
    unkeep(ifex);
    // KEEP:{MEM}
    unkeep(omem);
    // KEEP:{}
    keep(t_scope);
    // KEEP:{TSCOPE}
    mem(omem);           // Reset memory to before the IF for the other arm
    ctrl(new CProjNode(ifex,0).peep()); // Control for false branch    

    // False side
    try( Env e = _e = new Env(_e, null, -1, ctrl(), mem(), scope().ptr(), null) ) { // Nest an environment for the local vars
      // TODO: Insert cast
      Node f_exp = peek(':') ? stmt(false) : con(TypeNil.NIL);
      if( f_exp == null ) f_exp = err_ctrl2("missing expr after ':'");
      scope().stk().close();
      scope().setDef(REZ_IDX,f_exp);
      // KEEP:{TSCOPE}
      _e = e._par;            // Pop nested environment
    };

    // Find common set of new names
    ScopeNode f_scope = scope();
      // KEEP:{TSCOPE}
    unkeep(t_scope);
      // KEEP:{}
    StructNode f_stk = f_scope.stk();
    StructNode t_stk = t_scope.stk();
    Parse bad = errMsg();
    
    // Merge results.
    // KEEP: NO PEEPS ON REGION -- vvvvvvvvvvvvvvvvvvvv
    ctrl(new RegionNode(null,t_scope.ctrl(),f_scope.ctrl()).init());

    // Walk both sides and introduce error stores on 1-sided defs
    for( int i=1; i<f_stk.len(); i++ ) {
      String fld = f_stk.fld(i);
      scope().stk().add_fld(fld,Access.RW,Env.ANY,null); // Promote name to top level
      if( t_stk.find(fld)== -1 ) {
        Node err = new ErrNode(f_scope.ctrl(),bad,"'"+fld+"' not defined on "+true+" arm of trinary").init();
        t_scope.mem(new StoreNode(t_scope.mem(),t_scope.ptr(),err,fld,Access.RW,bad).init());        
      }
    }

    for( int i=1; i<t_stk.len(); i++ ) {
      String fld = t_stk.fld(i);
      if( t_stk.find(fld)== -1 ) {
        scope().stk().add_fld(fld,Access.RW,Env.ANY,null); // Promote name to top level
        Node err = new ErrNode(t_scope.ctrl(),bad,"'"+fld+"' not defined on "+false+" arm of trinary").init();
        f_scope.mem(new StoreNode(f_scope.mem(),f_scope.ptr(),err,fld,Access.RW,bad).init());        
      }
    }

    mem(       new PhiNode(TypeMem.ALLMEM,null,ctrl(),t_scope.mem (),f_scope.mem ()).peep());
    Node rez = new PhiNode(TypeNil.SCALAR,bad ,ctrl(),t_scope.rez (),f_scope.rez ()).peep() ;
    // KEEP: NO PEEPS ON REGION -- ^^^^^^^^^^^^^^^^^^^^
    keep(rez);
    // KEEP: {REZ}

    //Env.GVN.add_unuse(f_scope);
    //Env.GVN.add_unuse(t_scope);
    f_scope.kill();
    t_scope.kill();

    unkeep(rez);
    // KEEP: {}
    assert bal == _keeps._len;  // Balanced keep-alives
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
      int bal = _keeps._len;    // Balanced keep-alives
      skipWS();
      int oldx = _x;
      int old_last = _lastNWS;
      keep(expr);               // Keep alive across argument parse
      Node arg = expr();
      if( arg==null ) return unkeep(expr).peep();
      // To avoid the common bug of forgetting a ';', these must be on the same line.
      int line_last = _lines.binary_search(old_last);
      int line_now  = _lines.binary_search(_x);
      if( line_last != line_now ) {
        _x = oldx;  _lastNWS = old_last;
        return err_ctrl2("Lisp-like function application split between lines "+line_last+" and "+line_now+", but must be on the same line; possible missing semicolon?");
      }
      keep(arg);
      Node dsp = new FP2DSPNode(expr,errMsg(oldx)).peep();
      expr = do_call0(true,errMsgs(oldx,oldx),args(dsp,unkeep(arg),unkeep(expr))); // Pass the 1 arg
      assert bal == _keeps._len; // Balanced keep-alives
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
      int bal = _keeps._len;    // Balanced keep-alives
      // Look for a binop at this precedence level
      int opx = _x;             // Invariant: WS already skipped
      String tok = token0();
      Oper binop = Oper.bin_op(tok,prec);
      if( binop==null ) { _x=opx; return lhs; }
      _x -= binop.adjustx(tok); // Chosen op can be shorter than tok
      skipWS();
      int rhsx = _x;            // Invariant: WS already skipped
      keep(lhs);
      Parse err = errMsg(opx);
      // Load against LHS pointer.  If this is a primitive, the Load loads
      // against the primitive clazz.
      Node over= new LoadNode(mem(),lhs,binop._name,err).peep();
      // Resolve the set of primitive choices
      Node fun = new DynLoadNode(mem(),over,err).peep();
      // Bind the LHS to the function
      Node bind= keep(new BindFPNode(fun,lhs,false).peep());
      // Parse the RHS operand
      Node rhs = binop._lazy
        ? _lazy_expr(binop)
        : _expr_higher_require(binop);
      // Emit the call to both terms
      bind = unkeep(bind).peep();
      lhs = unkeep(lhs);
      // LHS in unhooked prior to optimizing/replacing.
      lhs = do_call(errMsgs(opx,lhsx,rhsx), args(lhs,rhs,bind));
      // Invariant: LHS is unhooked
      assert bal == _keeps._len; // Balanced keep-alives
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

  // Parse a RHS operand into a 'thunk', a zero-arg function.
  // Function takes in memory, display
  private Node _lazy_expr(Oper op) {
    int bal = _keeps._len;      // Balanced keep-alives
    int rhsx = _x;
    FunNode fun = new FunNode(ARG_IDX); // ctrl, mem, display
    keep(fun);                          // Keep alive
    fun.xval();
    NewNode outer_dsp = scope().ptr();
    
    // Build Parms for system incoming values
    Node rpc = new ParmNode(CTL_IDX,fun,null,TypeRPC.ALL_CALL).init();
    Node dsp = new ParmNode(DSP_IDX,fun,null,outer_dsp._tptr ).init();
    Node mem = new ParmNode(MEM_IDX,fun,null,TypeMem.ALLMEM  ).init();
    Node bind;
    try( Env e = new Env(_e, fun, 1, fun, mem, dsp, null) ) { // Nest an environment for the local vars
      _e = e;                   // Push nested environment
      // Display is special: the default is simply the outer lexical scope.
      // But here, in a function, the display is actually passed in as a hidden
      // extra argument and replaces the default.
      StructNode frame = e._scope.stk();
      assert fun==_e._fun && fun==_e._scope.ctrl();
      // Parse body
      Node rez = _expr_higher_require(op);
      if( rez==null ) throw TODO();
      // Normal exit 
      frame.close();

      // Merge normal exit into all early-exit paths.
      // TODO: this exits from the thunk, not the whole function
      assert frame.is_closure();
      rez = merge_exits(rez);
      
      // Standard return; function control, memory, result, RPC.  Plus a hook
      // to the function for faster access.
      unkeep(fun);
      RetNode ret = (RetNode)new RetNode(ctrl(),mem(),rez,fun.parm(CTL_IDX),fun).peep();

      _e = e._par;            // Pop nested environment
      Node fptr = new FunPtrNode(ret).peep();
      // The Bind builds a real display; any up-scope references are passed in now.
      bind = keep(new BindFPNode(fptr,scope().ptr(),false).peep());

      // Extra variables in the short-circuit are not available afterwards.
      // Set them to Err.
      for( int i=1; i<frame.len(); i++ ) {
        String fname = frame.fld(i);
        String msg = "'"+fname+"' not defined prior to the short-circuit";
        Parse bad = errMsg(rhsx);
        Node err = new ErrNode(ctrl(),bad,msg).peep();
        do_store(null,err,Access.Final,fname,bad,null,bad);
      }
    }
    bind = unkeep(bind);
    assert bal == _keeps._len; // Balanced keep-alives
    return bind;
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
    Oper op = Oper.pre_bal(tok,false);
    if( op != null ) {
      _x -= op.adjustx(tok); // Chosen op can be shorter than tok
      Node e0 = term();
      if( e0 == null ) { return err_ctrl2("Missing term after operator '"+op+"'"); } // Parsed a valid leading op but missing trailing expr
      if( op.is_open() ) throw TODO(); // Parse the close
      if( op._nargs!=1 ) throw TODO(); // No binary/trinary allowed here
      int bal = _keeps._len;      // Balanced keep-alives
      keep(e0);
      Parse err = errMsg(oldx);
      // Load against e0 pointer.  If e0 is a primitive, the Load is a no-op;
      // otherwise this converts a reference to a value.
      Node over= new LoadNode(mem(),e0,op._name,err).peep();
      // Resolve the correct function from the overload choices
      Node fun = new DynLoadNode(mem(),over,err).peep();
      // Call the operator
      n = do_call(errMsgs(oldx,oldx),args(unkeep(e0).peep(),fun));
      assert bal == _keeps._len; // Balanced keep-alives
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
        if( peek('(') ) throw TODO(); // Start of e0.( e1 ) syntax, TODO: bind instance fcn e1 with 'self' e0, producing a bound TFP
        int fld_start=_x;       // Get field start
        tok = token0();         // Field name
        if( tok == null ) {     // Not a token, check for a field number
          int fldnum = field_number();
          if( fldnum == -1 ) {
            if( n.nUses()==0 ) n.kill();
            return err_ctrl2("Missing field name after '.'");
          }
          tok = ""+fldnum;      // Convert to a field name
        }
        tok=tok.intern();

        // Store or load against memory
        if( peek(":=") || peek_not('=','=')) {
          Access fin = _buf[_x-2]==':' ? Access.RW : Access.Final;
          Node val = stmt(false);
          if( val == null )
            return err_ctrl2("Missing stmt after assigning field '."+tok+"'");
          Parse bad = errMsg(fld_start);
          mem( new StoreNode(mem(),n,keep(val),tok,fin,bad));
          return unkeep(val); // Return the value stored
        } else {
          Parse bad = errMsg(fld_start);          
          Node adr = keep(n);   // Save address for bind
          if( Util.eq(tok,"_") ) {
            // Using a plain underscore for the field name is a Resolving field.
            n = new DynLoadNode(mem(),n,    bad).peep();
          } else {
            // Normal non-oper load
            n = new    LoadNode(mem(),n,tok,bad).peep();
          }
          // Bind after load
          n = new BindFPNode(n, unkeep(adr), false).peep();
        }

      } else if( peek('(') ) {  // Attempt a function-call
        oldx = _x;              // Just past paren
        Parse err = errMsg(_x-1);// Error at the openning paren
        skipWS();               // Skip to start of 1st arg past "this"
        int first_arg_start = _x;
        keep(n);                // Keep alive across arg parse
        Node dsp = new FP2DSPNode(n,err).peep();
        // Argument tuple, with "this" or display first arg
        StructNode args = new StructNode(0,false,err );
        args.add_fld("0",Access.Final,dsp,err); // TODO: get the display start for errors
        keep(args);
        Node arg1 = stmts();
        // Parse rest of arguments
        _tuple(oldx-1,arg1,errMsg(first_arg_start),args,1); // Parse argument list
        Node x = unkeep(args).peep(); assert x==args;
        unkeep(n);                                // Function
        Parse[] badargs = args.fld_starts();      // Args from tuple
        n = do_call0(false,badargs,args(args,n)); // Pass the tuple

      } else {
        // Check for balanced op with a leading term, e.g. "ary [ idx ]" or
        // "ary [ idx ]= val".
        oldx = _x;                         // Token start
        String tok0 = token0();
        if( tok0==null || !Oper.is_open(tok0) ) { _x=oldx; break;} // Not a balanced op

        //int nidx = n.push();    // Preserve leading expr
        //skipWS();               // Skip to start of stmts
        //int oldx2 = _x;         // Statement start
        //Node idx = stmts();     // Index expression
        //if( idx==null ) { Node.pop(nidx); return err_ctrl2("Missing stmts after '"+tok0+"'"); }
        //
        //String tok1 = token0();
        //Oper bcl = Oper.balanced(tok0,tok1);
        //if( bcl==null ) return err_ctrl2("Missing close after '"+tok0+"'");
        //
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
        throw TODO();
      }
    }
    return n;
  }

  // Handle post-increment/post-decrement operator.
  // Does not define a field in structs: "@{ x++; y=2 }" - syntax error, no such field x
  // Skips trailing WS.
  private Node inc(String tok, int d) {
    // More-or-less expands as:
    // If x not defined yet
    //    x0 := 0;  // define x as mutable NIL
    // x1 = x0 + 1; // add
    // newmem = oldmem.put("x",x1);
    // x0           // Fresh ref of 'x' is returned
    skipWS();
    ScopeNode scope = lookup_scope(tok=tok.intern(),false); // Find prior scope of token
    // Need a load/call/store sensible options
    if( scope==null ) {         // Token not already bound to a value
      do_store(null,con(TypeNil.NIL),Access.RW,tok,null,null,null);
      scope = scope();
    } else {                    // Check existing token for mutable
      if( !scope.is_mutable(tok) )
        return err_ctrl2("Cannot re-assign final val '"+tok+"'");
    }

    // Scope is discovered by walking lexical display stack.
    // Pointer to the proper display is found via ptr-walking live display stack.
    // Now properly load from the display.
    Parse bad = errMsg();
    Node ptr = get_display_ptr(scope);
    Node fd = new LoadNode(mem(),ptr,tok,bad).peep();
    if( fd.is_forward_ref() )    // Prior is actually a forward-ref
      return err_ctrl1(ErrMsg.forward_ref(this,(FunPtrNode)fd));
    Node n = new FreshNode(fd,_e).peep();
    keep(n);
    // Do a full lookup on "+", and execute the function
    // Get the overloaded operator field, always late binding
    Node overplus = new LoadNode(mem(),n,"_+_",bad).peep();
    // Resolve primitive choices
    Node plus = new DynLoadNode(mem(),overplus,bad).peep();
    Node inc = con(TypeInt.con(d));
    // Add
    Node sum = do_call0(true,errMsgs(_x-2,_x,_x), args(n,inc,plus));
    // Store result back
    mem(new StoreNode(mem(),ptr,sum,tok,Access.RW,bad));
    return unkeep(n);      // Return pre-increment post-fresh value
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
  // Add a typecheck into the graph, with a shortcut if trivially ok.
  private Node typechk(Node x, Type t, Node mem, Parse bad) {
    return t == null || x._val.isa(t) ? x : new AssertNode(mem,x,t,bad).peep();
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

    // Check for a valid 'id'
    String tok = token0();
    tok = tok==null ? null : tok.intern();
    if( tok == null || Util.eq("_",tok)) { _x = oldx; return null; }
    if( Util.eq(tok,"=") || Util.eq(tok,"^") )
      { _x = oldx; return null; } // Disallow '=' as a fact, too easy to make mistakes
    ScopeNode scope = lookup_scope(tok,false);
    Parse bad = errMsg(oldx);
    if( scope == null ) { // Assume any unknown id is a forward-ref of a recursive function
      // Ops cannot be forward-refs, so are just 'not a fact'.  Cannot declare
      // them as a undefined forward-ref right now, because the op might be the
      // tail-half of a balanced-op, which is parsed by term() above.
      if( isOp(tok) ) { _x = oldx; return null; }
      // Must be a forward reference
      return val_fref(tok,bad);
    }

    // Must load against most recent display update, in case some prior store
    // is in-error.  Directly loading against the display would bypass the
    // (otherwise alive) error store.

    // Display/struct/scope containing the field
    Node dsp = get_display_ptr(scope);
    
    // Load the resolve field from the display/scope structure
    Node fd = new LoadNode(mem(),dsp,tok, bad).peep();

    // If in the middle of a definition (e.g. a HM Let, or recursive assign)
    // then no Fresh per normal HM rules.  If loading from normal Lambda
    // arguments, again no Fresh per normal HM rules.
    Node frsh = fd.is_forward_ref() || scope.stk().is_nongen(tok)
      ? fd
      : new FreshNode(fd,_e).peep();
    return frsh;
  }


  /** Parse a tuple; first stmt but not the ',' parsed.
   *  tuple= (stmts,[stmts,])     // Tuple; final comma is optional
   */
  private Node tuple(int oldx, Node s, int first_arg_start) {
    // First stmt is parsed already
    StructNode nn = new StructNode(0,false,errMsg(oldx) ).init();
    Parse bad = errMsg(first_arg_start);
    keep(nn);
    nn.add_fld(TypeFld.CLZ,Access.Final, PrimNode.PCLZ, null);
    _tuple(oldx,s,bad,nn,0);
    Node ptr = new NewNode().peep();
    Node nn0 = unkeep(nn).peep(); assert nn0==nn;
    mem(new StoreXNode(mem(),keep(ptr),nn0,bad));
    return unkeep(ptr);
  }
  private void _tuple(int oldx, Node s, Parse bad, StructNode nn, int fnum) {
    keep(nn);
    while( s!= null ) {         // More args
      nn.add_fld((""+fnum++).intern(),Access.Final,s,bad);
      if( !peek(',') ) break;   // Final comma is optional
      skipWS();                 // Skip to arg start before recording arg start
      bad = errMsg();           // Record arg start
      s = stmts();              // Parse arg
    }
    require(')',oldx);          // Balanced closing paren
    unkeep(nn).close();
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
    try( Env e = new Env(_e, null, 0, ctrl(), mem(), _e._scope.stk(), null) ) { // Nest an environment for the local vars
      _e = e;                   // Push nested environment
      stmts(true);              // Create local vars-as-fields
      require('}',oldx);        // Matched closing }
      assert ctrl() != e._scope;
      StructNode stk = e._scope.stk(); // The Env stack frame is the actual struct
      stk.close();
      e._par._scope.ctrl(ctrl()); // Carry any control changes back to outer scope
      e._par._scope.mem (mem ()); // Carry any memory  changes back to outer scope
      _e = e._par;                    // Pop nested environment
      return e._scope.ptr();
    } // Pop lexical scope around struct
  }

  /** Parse an anonymous function; the opening '{' already parsed.  After the
   *  '{' comes an optional list of arguments and a '->' token, and then any
   *  number of statements separated by ';'.
   *  func = { [[id]* ->]? stmts }
   */
  private static final Access args_are_mutable=Access.Final; // Args mutable or r/only by default
  private Node func() {
    int oldx = _x;              // Past opening '{'

    // Incrementally build up the formals, starting with the display
    Ary<Type> formals = new Ary<>(new Type[]{Type.CTRL,TypeMem.ALLMEM,scope().ptr()._tptr});
    Ary<Parse> bads= new Ary<>(new Parse [ARG_IDX]);
    Ary<String> ids= new Ary<>(new String[]{null,null,"^"});

    // Parse arguments
    while( true ) {
      skipWS();
      Parse badp = errMsg();   // Capture location in case of parameter error
      String tok = token();
      if( tok == null ) { _x=oldx; break; } // not a "[id]* ->"
      if( Util.eq((tok=tok.intern()),"->") ) break; // End of argument list
      if( !isAlpha0((byte)tok.charAt(0)) ) { _x=oldx; break; } // not a "[id]* ->"
      Type t = TypeNil.SCALAR; // Untyped, most generic type
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
          t = TypeNil.SCALAR;
          skipNonWS();         // Skip possible type sig, looking for next arg
        }
      }
      if( ids.find(tok) != -1 ) {
        err_ctrl3("Duplicate parameter name '" + tok + "'", badp);
        tok = (tok+" dup").intern();
      }
      ids.push(tok);
      formals.push(t); // Accumulate args
      bads.add(bad);
    }
    // If this is a no-arg function, we may have parsed 1 or 2 tokens as-if
    // args, and then reset.  Also reset to just the mem & display args.
    if( _x == oldx ) { formals.set_len(ARG_IDX);  ids.set_len(ARG_IDX); bads.set_len(ARG_IDX); }

    // Build the FunNode header
    FunNode fun = keep(new FunNode(formals.len()).init());

    // Build Parms for system incoming values
    Node rpc = new ParmNode(CTL_IDX,fun,null,TypeRPC.ALL_CALL   ).init();
    Node dsp = new ParmNode(DSP_IDX,fun,null,formals.at(DSP_IDX)).init();
    Node mem = new ParmNode(MEM_IDX,fun,null,TypeMem.ALLMEM     ).init();

    // Increase scope depth for function body.
    try( Env e = new Env(_e, fun, formals._len-DSP_IDX, fun, mem, dsp, null) ) { // Nest an environment for the local vars
      _e = e;                   // Push nested environment
      // Display is special: the default is simply the outer lexical scope.
      // But here, in a function, the display is actually passed in as a hidden
      // extra argument and replaces the default.
      StructNode frame = e._scope.stk();
      // Parms for all arguments
      Parse errmsg = errMsg();  // Lazy error message
      assert fun==_e._fun && fun==_e._scope.ctrl();
      for( int i=ARG_IDX; i<formals.len(); i++ ) { // User parms start
        TypeNil formal = (TypeNil)formals.at(i);
        Node parm = new ParmNode(i,fun,errmsg,TypeNil.SCALAR).peep();
        if( formal!=TypeNil.SCALAR )
          parm = new AssertNode(mem,parm,formal,bads.at(i)).peep();
        frame.add_fld(ids.at(i),args_are_mutable,parm,bads.at(i));
      }

      // Parse function body
      Node rez = stmts();       // Parse function body
      if( rez == null ) rez = err_ctrl2("Missing function body");
      require('}',oldx-1);      // Matched with opening {}
      frame.close();

      // Merge normal exit into all early-exit paths
      assert frame.is_closure();
      rez = merge_exits(rez);
      // Standard return; function control, memory, result, RPC.  Plus a hook
      // to the function for faster access.
      unkeep(fun);
      RetNode ret = (RetNode)(new RetNode(ctrl(),mem(),rez,fun.parm(CTL_IDX),fun).peep());
      
      _e = e._par;            // Pop nested environment; pops nongen also
      Node fptr = new FunPtrNode(ret).peep();
      // Anonymous functions early-bind.  Functions in structs become "methods" and late-bind.
      return scope().stk().is_closure() ? new BindFPNode(fptr,scope().ptr(),false).peep() : fptr;
    }
  }

  private Node merge_exits(Node rez) {
    ScopeNode s = scope();
    if( !s.has_early_exit() ) return rez;
    Node ctrl = s.early_ctrl();
    Node mem  = s.early_mem ();
    Node val  = s.early_val ();
    s.early_kill();
    //try(GVNGCM.Build<Node> X = _gvn.new Build<>()) {
    //  ctrl = ctrl.add_def(ctrl());
    //  ctrl._val = Type.CTRL;
    //  ctrl(ctrl=X.init(ctrl));
    //  mem.set_def(0,ctrl);
    //  val.set_def(0,ctrl);
    //  Node mem2 = X.xform(mem.add_def(mem()));
    //  Node val2 = X.xform(val.add_def(rez));
    //  mem(mem2);
    //  return (X._ret=val2);
    //}
    throw TODO();
  }

  // Merge this early exit path into all early exit paths being recorded in the
  // current Env/Scope.
  Node do_exit( ScopeNode s, Node rez ) {
    if( !s.has_early_exit() ) s.make_early_exit_merge();
    s.early_ctrl().addDef(ctrl());
    s.early_mem ().addDef(mem ());
    s.early_val ().addDef(rez   );
    ctrl(Env.XCTRL);
    mem (Node.con(TypeMem.ANYMEM));
    return Env.NIL;
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
      throw TODO();
    }
    //require(bfun.funptr().fun()._bal_close,oldx);
    //return do_call(errMsgs(oldx,oldx2),args(bfun,s));
    throw TODO();
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
  private Node number() {
    _pp.setIndex(_x);
    Number n = _nf.parse(_str,_pp);
    _x = _pp.getIndex();
    if( n instanceof Long   ) {
      if( _buf[_x-1]=='.' ) _x--; // Java default parser allows "1." as an integer; pushback the '.'
      long l = n.longValue();
      return con(l==0 ? TypeNil.NIL : TypeInt.con(l));
    }
    if( n instanceof Double ) return con(TypeFlt.con(n.doubleValue()));
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
      if( c=='%' ) throw TODO();
      if( c=='\\' ) throw TODO();
      if( _x == _buf.length ) return null;
    }
    String str = new String(_buf,oldx,_x-oldx-1).intern();
    // Convert to ptr-to-constant-memory-string
    Parse bad = errMsg(oldx);
    StructNode scon = new StructNode(0,false,bad );
    scon.add_fld(".",Access.Final,PrimNode.ZSTR,bad);
    scon.add_fld("0",Access.Final,con(TypeInt.con(str.charAt(0))),bad);
    StructNode scon1 = (StructNode)scon.close().peep();
    Node ptr = keep(new NewNode().init());
    mem( new StoreXNode(mem(),ptr,scon1,bad) );
    return unkeep(ptr);
  }

  /*
   *  type =   A* => type           // Introduce a type variable
   *  type = { A* => type }         // Introduce a type variable with explicit bounds
   *  type = tcon | tvar | [?]tptr | [?]tfun // "?" is nilable-ref
   *  tptr = tary | tstruct | ttuple
   *  tvar = HM type variable        // Scoped; includes global types like 'flt32'
   *  tcon = = ifex                  // Notice extra '=', must bake down to a constant; usually for fcns
   *  tfun = { [[type]* -> ]? type } // Mirrors func decls; ie. map=: {{A->B} [A] -> [B]}
   *  tary = [type]                  // Array types
   *  ttuple = ( [[type],]* )        // Tuple types are just a list of optional types;
   *                                 // the count of commas dictates the length, zero commas is zero length.
   *                                 // Tuple fields are always final.
   *  tstruct= [tid:]@{ [tfld;]* };  // Optional named type to extend, list of fields
   *  tfld = id [:type] [tcon]       // Field name, option type or const-expr
   */
  private Type type() {

    // First character to split type out:
    return switch( skipWS() ) {
    case '{' -> tfun();         // Function parse
    case '@' -> tstruct();      // Struct parse
    case '[' -> throw TODO(); // Array parse
    case '(' -> ttuple();       // Tuple parse
    case '=' -> throw TODO(); // Const ifex parse
    case '?' -> throw TODO(); // Nilable-ref parse
    default  -> tvar();         // TVAR parse
    };
  }

  // Parse a struct type.  BNF:
  //   @{ [tflds;]* }
  //   tfld = id [:type] [tcon]  // Field name, option type or const-expr.
  private TypeMemPtr tstruct() {
    if( !peek("@{") ) return null;
    // Parse fields
    Ary<TypeFld> flds = new Ary<>(new TypeFld[1],0);
    while( true ) {
      // Parse a field token
      String tok = token();
      if( tok==null ) break;
      tok = tok.intern();
      // Parse the optional field type
      Access access = Access.RW;     // Arbitrary AA type, not const-expr
      Type t = peek(':') ? type() : TypeNil.SCALAR;
      // Parse optional tcon: constant-expression
      if( peek('=') ) {
        Oper.make(tok,false);
        access = Access.Final;
        t = tcon();             // Arbitrary AA const-expr
      }
      // Insert the field into the structure.
      flds.push(TypeFld.make(tok,t,access));
      if(  peek('}') ) break;          // End of struct,  no trailing semicolon?
      if( !peek(';') ) throw TODO(); // Not a type
      if(  peek('}') ) break;          // End of struct, yes trailing semicolon?
    }
    TypeFld[] tflds = TypeFlds.get(flds.len());
    System.arraycopy(flds._es,0,tflds,0,flds._len);
    TypeStruct ts = TypeStruct.make_flds(Type.ANY,tflds);
    return TypeMemPtr.make(BitsAlias.LOCX,ts);
  }

  // Parse an const ifex.
  private Type tcon() {
    Node n = ifex();
    if( n==null ) throw TODO(); // Missing ifex expecting a const-expr
    if( !n._val.is_con() ) throw TODO(); // Not a const expr
    //return n._val;
    // TODO: function constants have to be 'hooked'
    throw TODO();
  }

  // Parse a tuple type.
  private Type ttuple() {
    int oldx = _x;
    peek('(');
    TypeStruct ts = TypeStruct.malloc(false,Type.ALL,TypeFlds.EMPTY);
    while(true) {
      Type t = type();
      if( t==null ) { _x=oldx; return ts.free(null); }
      throw TODO();
    }
  }

  // Parse a type function:
  // { types* -> type }
  // { type }
  private Type tfun() {
    int oldx = _x;
    peek('{');
    Ary<Type> ts = new Ary<>(new Type[1],0);
    Type arg = type(), ret=null;
    while( arg!=null ) {
      ts.push(arg);
      arg = type();
    }
    if( peek("->") )            // Explicit args/return list
      ts.push(type());      // Push return type
    else if( ts.len()>1 ) ts.push(null); // Too many types, fail out
    if( peek('}') && ts.len()>1 ) ret = ts.pop();
    if( ret==null )             // Not a function type
      { _x=oldx;  return null; }
    ts.push(ret);
    return TypeTuple.fun_sig(ts);
  }
  

  // Type-id or type-var parse.
  // TODO: type-vars done as function syntax?
  // Example: List = : @{ next:List?; val:A }  // 'A' is free.  Problem: when to Shadow and when not.
  // Example: List A = : @{ next:List?; val:A }  // 'A' is declared.  Problem: Deeply nested types STILL need wrappers to avoid ambiguity
  // Example: List = : A => @{ next:List?; val:A } // New BNF: toks* => t0 with toks as free t-vars; does not support nested "toks*=>tN" exprs
  // Example: List = : { A => @{ next:List?; val:A } } // New BNF: { toks* => t0 } with toks as free t-vars
  // Less parens; A is captured in the 'MyType' type, and B is captured in the 'map' type
  // Example: MyType = :   A => @{ table:A[]; map:  B => { MyType {A->B} -> MyType B }  ; ... }
  // More parens; A is captured in the 'MyType' type, and B is captured in the 'map' type
  // Example: MyType = : { A => @{ table:A[]; map:{ B => { MyType {A->B} -> MyType B } }; ... } }  
  private Type tvar() {
    int oldx = _x;
    String tok = token();
    if( tok==null ) return null;
    Type t = _e.lookup_type(tok.intern());
    if( t==null ) { _x=oldx; return null; }
    return t;
  }

  // Create a value forward-reference.  Must turn into a function call later.
  // Called when seeing a name for the first time, in a function-call context,
  // OR when defining a type constructor.  Not allowed to forward-ref normal
  // variables, so this is a function variable, not yet defined.  Use an
  // ForwardRef until it gets defined.
  private ForwardRefNode val_fref(String tok, Parse bad) {
    ForwardRefNode fref = new ForwardRefNode(tok,bad).init();
    // Place in nearest enclosing closure scope, this will keep promoting until we find the actual scope
    Env e = _e;
    while( e._scope.test_if() ) e = e._par;
    StructNode stk = e._scope.stk();
    stk.add_fld(tok,Access.Final,fref,null);
    return fref;
  }
  
  // Create a type forward-reference.  Must be type-defined later.  Called when
  // seeing a name in a type context for the first time.  Builds an empty type
  // NewNode and returns it.
  private Type type_fref(String tname, boolean is_val) {
    //NewNode tn = new NewNode(false,true,tname,BitsAlias.new_alias());
    //tn._val = tn.value();
    //_gvn.add_work_new(tn);
    //_e.add_type(tname,tn);
    //assert tn.is_forward_type();
    //return tn;
    throw TODO(); // TODO: is_val
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

  // Utilities to shorten code for common cases
  public Node ctrl() { return scope().ctrl(); }
  // Set and return a new control
  private <N extends Node> N ctrl(N n) { return scope().ctrl(n); }
  private Node mem() { return scope().mem(); }
  private void mem( Node n) { scope().mem(n); }

  private Node con( TypeNil t ) { return Node.con(PrimNode.wrap(t)); }

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
    Node ptr = e._scope.ptr();
    Node mmem = mem();
    while( true ) {
      if( scope == e._scope ) return ptr;
      ptr = new LoadNode(mmem,ptr,"^",null).peep(); // Gen linked-list walk code, walking display slot
      e = e._par;               // Walk linked-list in parser also
    }
  }

  // Wiring for call arguments
  private Node[] args(Node a0                           ) { return _args(new Node[]{null,null,a0}); }
  private Node[] args(Node a0, Node a1                  ) { return _args(new Node[]{null,null,a0,a1}); }
  private Node[] args(Node a0, Node a1, Node a2         ) { return _args(new Node[]{null,null,a0,a1,a2}); }
  private Node[] _args(Node[] args) {
    args[CTL_IDX] = ctrl();     // Always control
    args[MEM_IDX] = mem();      // Always memory
    return args;
  }

  // Insert a call, with memory splits.  Wiring happens later, and when a call
  // is wired it picks up projections to merge at the Fun & Parm nodes.
  private Node do_call( Parse[] bads, Node... args ) { return do_call0(true,bads,args); }
  private Node do_call0( boolean unpack, Parse[] bads, Node... args ) {
    int bal = _keeps._len;       // Balanced keep-alives
    CallNode call = new CallNode(unpack,bads,args).init();
    CallEpiNode cepi = keep(new CallEpiNode(call).init());
    ctrl(new CProjNode(cepi).peep());
    mem (new MProjNode(cepi).peep()); // Return memory from all called functions
    Node r = new  ProjNode(unkeep(cepi).peep(),REZ_IDX).peep();
    assert bal == _keeps._len;                // Balanced keep-alives
    return r;
  }

  // Whack current control with a syntax error
  private ErrNode err_ctrl1( ErrMsg msg ) { return new ErrNode(ctrl(),msg).init(); }
  private ErrNode err_ctrl2( String msg ) { return new ErrNode(ctrl(),errMsg(),msg).init(); }
  private void err_ctrl0(String s) { err_ctrl3(s,errMsg()); }
  private void err_ctrl3(String s, Parse open) {
    ctrl(new ErrNode(ctrl(),open,s).peep());
  }

  // Make a private clone just for delayed error messages
  private Parse( Parse P ) {
    _src  = P._src;
    _buf  = P._buf;
    _x    = P._x;
    _lines= P._lines;
    _lastNWS = P._lastNWS;
    _e    = null;  _nf  = null;  _pp  = null;  _str = null;
    _keeps = null;
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

  // keep a node alive
  <N extends Node> N keep(N n) { _keeps.push(n); return n.keep(); }
  <N extends Node> N unkeep(N n) { Node k = _keeps.pop(); assert k==n;  return n.unkeep(); }
  
  // Handy for the debugger to print
  @Override public String toString() { return new String(_buf,_x,_buf.length-_x); }

  // 
  @Override public boolean equals(Object loc) {
    if( this==loc ) return true;
    if( !(loc instanceof Parse p) ) return false;
    return _x==p._x && _src.equals(p._src);
  }
  @Override public int hashCode() {
    return _src.hashCode()+_x;
  }
  // Ordering for error messages
  @Override public int compareTo(Parse loc) {
    int x = _src.compareTo(loc._src);
    if( x!=0 ) return x;
    return _x - loc._x;
  }
}
