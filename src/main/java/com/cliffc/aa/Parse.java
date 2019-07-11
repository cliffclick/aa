package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import org.jetbrains.annotations.NotNull;

import java.text.NumberFormat;
import java.text.ParsePosition;
import java.util.BitSet;

/** an implementation of language AA
 *
 *  GRAMMAR:
 *  prog = stmts END
 *  stmts= [tstmt|stmt][; stmts]*[;]? // multiple statements; final ';' is optional
 *  tstmt= tvar = :type            // type variable assignment
 *  stmt = [id[:type]? [:]=]* ifex // ids are (re-)assigned, and are available in later statements
 *  ifex = expr ? expr : expr      // trinary logic
 *  expr = term [binop term]*      // gather all the binops and sort by precedence
 *  term = tfact [tuple or tfact or .field]* // application (includes uniop) or field,tuple lookup
 *                                 // application arg list: tfact(tuple)
 *                                 // application adjacent: tfact tfact
 *                                 // field and tuple lookup: tfact.field
 *
 *  term = tfact post
 *  post = empty | (tuple) post | tfact post | .field post | .field [:]= stmt
 *
 *  tfact= fact[:type]             // Typed fact
 *  fact = id                      // variable lookup
 *  fact = num                     // number
 *  fact = "str"                   // string
 *  fact = (stmts)                 // General statements parsed recursively
 *  fact = tuple                   // Tuple builder
 *  fact = func                    // Anonymous function declaration
 *  fact = @{ [id[:type]?[=stmt]?,]* } // Anonymous struct declaration; optional type, optional initial value, optional final comma
 *  fact = {binop}                 // Special syntactic form of binop; no spaces allowed; returns function constant
 *  fact = {uniop}                 // Special syntactic form of uniop; no spaces allowed; returns function constant
 *  tuple= (stmts,[stmts,])        // Tuple; final comma is optional
 *  binop= +-*%&|/<>!=             // etc; primitive lookup; can determine infix binop at parse-time
 *  uniop=  -!~                    // etc; primitive lookup; can determine infix uniop at parse-time
 *  func = { [[id[:type]?]* ->]? stmts} // Anonymous function declaration
 *                                 // Pattern matching: 1 arg is the arg; 2+ args break down a (required) tuple
 *  str  = [.\%]*                  // String contents; \t\n\r\% standard escapes
 *  str  = %[num]?[.num]?fact      // Percent escape embeds a 'fact' in a string; "name=%name\n"
 *  type = tcon | tvar | tfun[?] | tstruct[?] | ttuple[?] // Types are a tcon or a tfun or a tstruct or a type variable.  A trailing ? means 'nilable'
 *  tcon = int, int[1,8,16,32,64], flt, flt[32,64], real, str[?]
 *  tfun = {[[type]* ->]? type }   // Function types mirror func declarations
 *  ttuple = ( [:type]?,* )        // Tuple types are just a list of optional types; the count of commas dictates the length, zero commas is zero length
 *  tstruct = @{ [id[:type],]*}    // Struct types are field names with optional types
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
    _gvn = Env.GVN;      // Pessimistic during parsing
  }
  String dump() { return _e._scope.dump(99,_gvn); }// debugging hook

  // Parse the string in the given lookup context, and return an executable
  // program.  Called in a partial-program context; passed in an existing
  // ScopeNode with existing variables which survive to the next call.  Used by
  // the REPL to do incremental typing.
  TypeEnv go_partial( ) {
    prog();        // Parse a program
    _gvn.iter();   // Pessimistic optimizations; might improve error situation
    _gvn.gcp(_e._scope); // Global Constant Propagation
    _gvn.iter();   // Re-check all ideal calls now that types have been maximally lifted
    return gather_errors();
  }

  // Parse the string in the given lookup context, and return an executable
  // program.  Called in a whole-program context; passed in an empty ScopeNode
  // and nothing survives since there is no next call.  Used by the Exec to do
  // whole-compilation-unit typing.
  TypeEnv go_whole( ) {
    prog();                     // Parse a program
    clean_top_level_scope();
    _gvn.iter();   // Pessimistic optimizations; might improve error situation
    remove_unknown_callers();
    _gvn.gcp(_e._scope); // Global Constant Propagation
    _gvn.iter();   // Re-check all ideal calls now that types have been maximally lifted
    return gather_errors();
  }

  private void clean_top_level_scope() {
    // Delete names at the top scope before final optimization.
    // Keep return results & exit control.
    _e._scope.promote_forward_del_locals(_gvn,null);
  }

  private void remove_unknown_callers() {
    Ary<Node> uses = Env.ALL_CTRL._uses;
    // Leave any final result function 'hooked' by the unknown caller to keep
    // it alive to be returned.
    Node res = _e._scope.in(_e._scope._defs._len-2);
    Node fun = res instanceof EpilogNode ? ((EpilogNode)res).fun() : null;
    // For all other unknown uses of functions, they will all be known after
    // GCP.  Remove the hyper-conservative ALL_CTRL edge.  Note that I canNOT
    // run the pessimistic opto() at this point, as GCP needs to discover all
    // the actual call-graph edges and install them directly on the FunNodes.
    for( int i=0; i<uses._len; i++ ) {
      Node use = uses.at(i);
      if( use._uid >= GVNGCM._INIT0_CNT && use != fun ) {
        assert use instanceof FunNode;
        assert use.in(1)==Env.ALL_CTRL;
        _gvn.unreg(use);        // Changing edges, so unregister
        use.set_def(1,con(Type.XCTRL),_gvn);
        _gvn.rereg(use,Type.CTRL);
        i--;
      }
    }
  }

  private TypeEnv gather_errors() {
    _e._scope.pop();          // Remove self-hook
    Node res = _e._scope.pop(); // New and improved result

    // Hunt for typing errors in the alive code
    assert _e._par._par==null; // Top-level only
    BitSet bs = new BitSet();
    bs.set(0);                  // Do not walk initial scope (primitives and constants only)
    bs.set(_e._scope._uid);     // Do not walk top-level scope
    Ary<String> errs0 = new Ary<>(new String[1],0);
    Ary<String> errs1 = new Ary<>(new String[1],0);
    Ary<String> errs2 = new Ary<>(new String[1],0);
    res   .walkerr_def(errs0,errs1,errs2,bs,_gvn);
    ctrl().walkerr_def(errs0,errs1,errs2,bs,_gvn);
    mem() .walkerr_def(errs0,errs1,errs2,bs,_gvn);
    if( errs0.isEmpty() ) errs0.addAll(errs1);
    if( errs0.isEmpty() ) _e._scope.walkerr_use(errs0,new BitSet(),_gvn);
    if( errs0.isEmpty() && skipWS() != -1 ) errs0.add(errMsg("Syntax error; trailing junk"));
    if( errs0.isEmpty() ) res.walkerr_gc(errs0,new BitSet(),_gvn);
    // If the ONLY error is from unresolved calls, report them last.  Most
    // other errors result in unresolved calls, so report others first.
    if( errs0.isEmpty() ) errs0.addAll(errs2);
    errs0.sort_update(String::compareTo);

    Type tres = _gvn.type(res);
    TypeMem tmem = (TypeMem)_gvn.type(mem());
    kill(res);       // Kill Node for returned Type result
    set_ctrl(null);  // Kill control also
    set_mem (null);  // Kill memory  also
    return new TypeEnv(tres,tmem,_e,errs0.isEmpty() ? null : errs0);
  }

  /** Parse a top-level:
   *  prog = stmts END */
  private void prog() {
    Node res = stmts();
    if( res == null ) res = con(Type.ANY);
    _e._scope.add_def(res);       // Hook, so not deleted
    _e._scope.add_def(_e._scope); // Self hook, so not deleted

  }

  /** Parse a list of statements; final semi-colon is optional.
   *  stmts= [tstmt or stmt] [; stmts]*[;]?
   */
  private Node stmts() {
    Node stmt = tstmt(), last = null;
    if( stmt == null ) stmt = stmt();
    while( stmt != null ) {
      if( !peek(';') ) return stmt;
      last = stmt;
      stmt = tstmt();
      if( stmt == null ) stmt = stmt();
      if( stmt == null ) {
        if( peek(';') ) { _x--; stmt=last; }   // Ignore empty statement
      } else if( !last.is_dead() ) kill(last); // prior expression result no longer alive in parser
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
    if( tvar == null ) return null;
    if( !peek('=') || !peek(':') ) { _x = oldx; return null; }
    // Must be a type-variable assignment
    Type t = typev();
    if( t==null ) return err_ctrl2("Missing type after ':'");
    if( peek('?') ) return err_ctrl2("Named types are never nil");
    if( lookup(tvar) != null ) return err_ctrl2("Cannot re-assign val '"+tvar+"' as a type");
    // Single-inheritance & vtables & RTTI:
    //            "Objects know thy Class"
    // Which means a TypeObj knows its Name.  Its baked into the vtable.
    // Which means TypeObj is named and not the pointer-to-TypeObj.
    // "Point= :@{x,y}" declares "Point" to be a type Name for "@{x,y}".
    Type ot = _e.lookup_type(tvar);
    TypeName tn;
    if( ot == null ) {        // Name does not pre-exist
      tn = TypeName.make(tvar,_e._scope.types(),t);
      _e.add_type(tvar,tn);   // Assign type-name
    } else {
      tn = ot.merge_recursive_type(t);
      if( tn == null ) return err_ctrl2("Cannot re-assign type '"+tvar+"'");
    }

    // Add a constructor function.  If this is a primitive, build a constructor
    // taking the primitive.
    if( !(t instanceof TypeObj) ) {
      PrimNode cvt = PrimNode.convertTypeName(t,tn,errMsg());
      return _e.add_fun(tvar,gvn(cvt.as_fun(_gvn))); // Return type-name constructor
    }
    // If this is a TypeObj, build a constructor taking a pointer-to-TypeObj -
    // and the associated memory state, i.e.  takes a ptr-to-@{x,y} and returns
    // a ptr-to-Named:@{x,y}.  This stores a v-table ptr into an object.  The
    // alias# does not change, but a TypeMem[alias#] would now map to the Named
    // variant.
    EpilogNode epi1 = IntrinsicNode.convertTypeName((TypeObj)t,tn,errMsg(),_gvn);
    Node rez = _e.add_fun(tvar,epi1); // Return type-name constructor
    if( t instanceof TypeStruct ) {   // Add struct types with expanded arg lists
      EpilogNode epi2 = IntrinsicNode.convertTypeNameStruct((TypeStruct)t,tn,errMsg(),_gvn);
      Node rez2 = _e.add_fun(tvar,epi2); // type-name constructor with expanded arg list
      _gvn.init0(rez2._uses.at(0)); // Force init of Unresolved
    }
    // TODO: Add reverse cast-away
    return rez;
  }

  /** A statement is a list of variables to final-assign or re-assign, and an
   *  ifex for the value.  The variables must not be forward refs and are
   *  available in all later statements.  Final-assigned variables can never be
   *  assigned again.  All type annotations on a variable always apply to all
   *  assignments (final or not); a variable cannot be "loosened" during a
   *  reassignment.
   *
   *  stmt = [[id or ifex.field][:type] [:]=]* ifex //
   *
   *  Note the syntax difference between:
   *    stmt = id := val  //    re-assignment
   *    stmt = id  = val  // final assignment
   *   tstmt = id =:type  // type variable decl, type assignment
   *
   *  The ':=' is the re-assignment token, no spaces allowed.
   *  Variable assignment does not involve Memory and no State is changed.
   *  Field    assignment does     involve Memory and    State is changed.
   *
   *  Both kinds of assignments are legal in the same stmt:
   *    x = y = z = fcn(arg0,arg1).fld1.fld2 = some_more_ifex;
   */
  private Node stmt() {
    Ary<String> toks = new Ary<>(new String[1],0);
    Ary<Type  > ts   = new Ary<>(new Type  [1],0);
    BitSet rs = new BitSet();
    while( true ) {
      int oldx = _x;
      String tok = token();  // Scan for 'id = ...'
      if( tok == null ) break;
      int oldx2 = _x;
      Type t = null;
      if( peek(':') && (t=type())==null ) _x = oldx2; // Grammar ambiguity, resolve p?a:b from a:int
      if( peek(":=") ) rs.set(toks._len);   // Re-assignment parse
      else if( !peek('=') ) { _x = oldx; break; } // Unwind token parse, and not assignment
      toks.add(tok);
      ts  .add(t  );
    }

    // Normal statement value parse
    Node ifex = ifex();         // Parse an expression for the statement value
    if( ifex == null )          // No statement?
      return toks._len == 0 ? null
        : err_ctrl2("Missing ifex after assignment of '"+toks.last()+"'");
    // Honor all type requests, all at once
    for( Type t : ts ) if( t != null ) ifex = gvn(new TypeNode(t,ifex,errMsg()));
    // Assign tokens to value
    for( int i=0; i<toks._len; i++ ) {
      String tok = toks.at(i);     // Token being assigned
      boolean mutable = rs.get(i); // Assignment is mutable or final
      Node n = lookup(tok);        // Prior value of token
      if( n==null ) {              // Token not already bound to a value
        if( !ifex.is_forward_ref() ) { // Do not assign unknown refs to another name
          _e.update(tok,ifex,null,mutable); // Bind token to a value
          if( ifex instanceof EpilogNode ) ((EpilogNode)ifex).fun().bind(tok); // Debug only: give name to function
        }
      } else { // Handle re-assignments and forward referenced function definitions
        if( n.is_forward_ref() ) { // Prior is actually a forward-ref, so this is the def
          assert !_e.is_mutable(tok);
          ((EpilogNode)n).merge_ref_def(_gvn,tok,(EpilogNode)ifex);
        } else if( _e.is_mutable(tok) )
          _e.update(tok,ifex,_gvn,mutable);
        else
          err_ctrl0("Cannot re-assign final val '"+tok+"'");
      }
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
      Node ifex = gvn(new IfNode(ctrl(),expr));
      ctrls.add_def(ifex); // Keep alive, even if 1st Proj kills last use, so 2nd Proj can hook
      Env e_if = _e;       // Environment for 'if'
      ScopeNode if_scope = e_if._scope;
      ScopeNode t_scope = (_e = new Env(e_if))._scope; // Push new scope for true arm
      set_ctrl(gvn(new CProjNode(ifex,1))); // Control for true branch, and sharpen tested value
      Node t_sharp = ctrl().sharpen(_gvn,if_scope,t_scope);
      Node tex = expr();
      ctrls.add_def(tex==null ? err_ctrl1("missing expr after '?'",Type.SCALAR) : tex);
      ctrls.add_def(ctrl()); // 2 - hook true-side control
      require(':');
      ScopeNode f_scope = (_e = new Env(e_if))._scope; // Push new scope for false arm
      set_ctrl(gvn(new CProjNode(ifex,0))); // Control for true branch, and sharpen tested value
      Node f_sharp = ctrl().sharpen(_gvn,if_scope,f_scope);
      Node fex = expr();
      ctrls.add_def(fex==null ? err_ctrl1("missing expr after ':'",Type.SCALAR) : fex);
      ctrls.add_def(ctrl()); // 4 - hook false-side control
      _e = e_if;             // Pop the arms scope
      set_ctrl(init(new RegionNode(null,ctrls.in(2),ctrls.in(4))));
      String phi_errmsg = errMsg("Cannot mix GC and non-GC types");
      if_scope.common(this,_gvn,phi_errmsg,t_scope,f_scope,expr,t_sharp,f_sharp); // Add a PhiNode for all commonly defined variables
      if_scope.add_def(gvn(new PhiNode(phi_errmsg,ctrl(),ctrls.in(1),ctrls.in(3)))); // Add a PhiNode for the result, hook to prevent deletion
      if( !t_sharp.is_dead() && t_sharp._uses._len == 0 ) kill(t_sharp);
      if( !f_sharp.is_dead() && f_sharp._uses._len == 0 ) kill(f_sharp);
      kill(t_scope);  assert t_scope.is_dead();
      kill(f_scope);  assert f_scope.is_dead();
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
        if( term == null ) term = err_ctrl2("missing expr after binary op "+bin);
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
          Node call = do_call(new CallNode(true,errMsg(),ctrl(),fun,mem(),args.in(i-1),args.in(i)));
          args.set_def(i-1,call,_gvn);
          funs.remove(i);  args.remove(i);  i--;
        }
        max--;
      }
      return args.del(0);       // Return the remaining expression
    }
  }

  /** Parse a term, either an optional application or a field lookup
   *    term = tfact [tuple | fact | .field]* // application (includes uniop) or field (and tuple) lookup
   *  An alternative expression of the same grammar is:
   *    term = tfact post
   *    post = empty | (tuple) post | tfact post | .field post
   *  Also, field assignments are:
   *    post = .field [:]= stmt
   */
  private Node term() {
    Node n = tfact();
    if( n == null ) return null;
    while( true ) {             // Repeated application or field lookup is fine
      if( peek('.') ) {         // Field?
        String fld = token();   // Field name
        int fnum = fld==null ? field_number() : -1;
        if( fld==null && fnum==-1 ) n = err_ctrl2("Missing field name after '.'");
        else if( peek(":=") || peek('=') ) {
          Node stmt = stmt();
          if( stmt == null ) n = err_ctrl2("Missing stmt after assigning field '."+fld+"'");
          else if( fld != null ) set_mem(gvn(new StoreNode(ctrl(),mem(),n,n=stmt,fld ,errMsg())));
          else                   set_mem(gvn(new StoreNode(ctrl(),mem(),n,n=stmt,fnum,errMsg())));
        } else {
          if( fld != null ) n = gvn(new LoadNode(ctrl(),mem(),n,fld ,errMsg()));
          else              n = gvn(new LoadNode(ctrl(),mem(),n,fnum,errMsg()));
        }

      } else {                  // Attempt a function-call
        boolean arglist = peek('(');
        int oldx = _x;
        Node arg = arglist ? tuple(stmts()) : tfact(); // Start of an argument list?
        if( arg == null )       // tfact but no arg is just the tfact
          break;
        Type tn = _gvn.type(n);
        boolean may_fun = tn.isa(TypeFunPtr.GENERIC_FUNPTR);
        if( !may_fun && arg.may_prec() >= 0 ) { _x=oldx; break; }
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
          n = err_ctrl2("A function is being called, but "+tn+" is not a function type");
        } else {
          n = do_call(new CallNode(!arglist,errMsg(),ctrl(),n,mem(),arg)); // Pass the 1 arg
        }
      }
    } // Else no trailing arg, just return value
    return n;                   // No more terms
  }

  /** Parse an optional type
   *  tfact = fact[:type]
   */
  private Node tfact() {
    Node fact = fact();
    if( fact==null ) return null;
    int oldx = _x;
    if( !peek(':') ) { _x = oldx; return fact; }
    Type t = type();
    if( t==null ) { _x = oldx; return fact; } // No error for missing type, because can be ?: instead
    return gvn(new TypeNode(t,fact,errMsg()));
  }

  /** Parse a factor, a leaf grammar token
   *  fact = num       // number
   *  fact = "string"  // string
   *  fact = (stmts)   // General statements parsed recursively
   *  fact = (tuple,*) // tuple; first comma required, trailing comma not required
   *  fact = {binop}   // Special syntactic form of binop; no spaces allowed; returns function constant
   *  fact = {uniop}   // Special syntactic form of uniop; no spaces allowed; returns function constant
   *  fact = {func}    // Anonymous function declaration
   *  fact = id        // variable lookup, NOT a binop or uniop but might be e.g. function-valued, including un-/binops as values
   */
  private Node fact() {
    if( skipWS() == -1 ) return null;
    byte c = _buf[_x];
    if( isDigit(c) ) return con(number());
    if( '"' == c ) {
      Type ts = string();
      return ts==null ? err_ctrl1("Unterminated string",TypeStr.XSTR) : con(ts);
    }
    int oldx = _x;
    if( peek1(c,'(') ) {        // a nested statement or a tuple
      Node s = stmts();
      if( s==null ) { _x = oldx; return null; } // A bare "()" pair is not a statement
      if( peek(')') ) return s;                 // A (grouped) statement
      oldx = _x;
      if( !peek(',') ) return s;                // Not a tuple, probably a syntax error
      _x = oldx;                                // Reparse the ',' in tuple
      return tuple(s);                          // Parse a tuple
    }
    // Anonymous function or operator
    if( peek1(c,'{') ) {
      String tok = token0();
      Node op = tok == null ? null : _e.lookup_filter(tok,_gvn,2); // TODO: filter by >2 not ==3
      if( peek('}') && op != null && op.op_prec() > 0 )
        return op;              // Return operator as a function constant
      _x = oldx+1;              // Back to the opening paren
      return func();            // Anonymous function
    }
    // Anonymous struct
    if( peek2(c,"@{") ) return struct();

    // Check for a valid 'id'
    String tok = token0();
    if( tok == null ) return null;
    Node var = lookup(tok);
    if( var == null ) // Assume any unknown ref is a forward-ref of a recursive function
      return _e.update(tok,gvn(EpilogNode.forward_ref(_gvn,tok,this)),null,false);
    // Disallow uniop and binop functions as factors.
    if( var.op_prec() > 0 ) { _x = oldx; return null; }
    return var;
  }

  /** Parse a tuple; first stmt but not the ',' parsed.
   *  tuple= (stmts,[stmts,])     // Tuple; final comma is optional
   */
  private Node tuple(Node s) {
    // Construct a tuple
    Ary<Node> ns = new Ary<>(new Node[]{null});
    while( s!=null ) {
      ns.add(s);
      if( !peek(',') ) break;   // Final comma is optional
      s=stmts();
    }
    require(')');
    return do_mem(new NewNode(ns.asAry(),TypeStruct.make(ns._len-1)));
  }

  /** Parse an anonymous function; the opening '{' already parsed.  After the
   *  '{' comes an optional list of arguments and a '->' token, and then any
   *  number of statements separated by ';'.
   *  func = { [[id]* ->]? stmts }
   */
  private static final boolean args_are_mutable=false;
  private Node func() {
    int oldx = _x;
    Ary<String> ids = new Ary<>(new String[1],0);
    Ary<Type  > ts  = new Ary<>(new Type  [1],0);
    Ary<Parse > bads= new Ary<>(new Parse [1],0);

    while( true ) {
      String tok = token();
      if( tok == null ) { ids.clear(); _x=oldx; break; } // not a "[id]* ->"
      if( tok.equals("->") ) break;
      Type t = Type.SCALAR;    // Untyped, most generic type
      Parse bad = errMsg();    // Capture location in case of type error
      if( peek(':') )          // Has type annotation?
        if( (t=type())==null ) throw AA.unimpl(); // return an error here
      ids .add(tok);
      ts  .add(t  );
      bads.add(bad);
    }
    Node old_ctrl = ctrl();
    Node old_mem  = mem ();
    FunNode fun = init(new FunNode(ts.asAry()));
    try( Env e = new Env(_e) ) {// Nest an environment for the local vars
      _e = e;                   // Push nested environment
      set_ctrl(fun);            // New control is function head
      String errmsg = errMsg("Cannot mix GC and non-GC types");
      int cnt=0;                // Add parameters to local environment
      for( int i=0; i<ids._len; i++ )
        _e.update(ids.at(i),gvn(new ParmNode(cnt++,ids.at(i),fun,con(ts.at(i)),errmsg)),null,
                  /*memory is mutable*/i == 0 || args_are_mutable);
      Node rpc = gvn(new ParmNode(-1,"rpc",fun,con(TypeRPC.ALL_CALL),null));
      Node mem = gvn(new ParmNode(-2,"mem",fun,con(TypeMem.MEM),null));
      set_mem(mem);
      Node rez = stmts();       // Parse function body
      if( rez == null ) rez = err_ctrl1("Missing function body", Type.SCALAR);
      require('}');             //
      Node epi = gvn(new EpilogNode(ctrl(),mem(),rez,rpc,fun,null));
      _e = _e._par;             // Pop nested environment
      set_ctrl(old_ctrl);       // Back to the pre-function-def control
      set_mem (old_mem );
      return epi;               // Return function; close-out and DCE 'e'
    }
  }

  /** Parse anonymous struct; the opening "@{" already parsed.  Next comes
   *  statements, with each assigned value becoming a struct member.  A lexical
   *  scope is made (non top-level assignments are removed at the end), then
   *  the closing "}".
   *  \@{ [id[:type]?[=stmt]?,]* }
   */
  private Node struct() {
    try( Env e = new Env(_e) ) {// Nest an environment for the local vars
      Node ctrl = ctrl();
      _e = e;                   // Push nested environment
      set_ctrl(ctrl);           // Carry control through
      Ary<String> toks = new Ary<>(new String[1],0);
      BitSet fs = new BitSet();
      while( true ) {
        String tok = token();    // Scan for 'id'
        if( tok == null ) break; // end-of-struct-def
        Type t = Type.SCALAR;    // Untyped, most generic type that fits in a field
        Node stmt = con(Type.SCALAR);
        boolean is_final = true;
        if( peek(":=") ) { is_final = false; _x--; } // Parse := re-assignable field token
        if( peek('=') ) {       // Parse field initial value
          if( (stmt=stmt())==null )
            stmt = err_ctrl2("Missing ifex after assignment of '"+tok+"'");
        } else if( peek(':') )  // Has type annotation?
          if( (t=type())==null )
            stmt = err_ctrl2("Missing type after ':'");
        // Check for repeating a field name
        if( e._scope.get(tok)!=null ) {
          kill(stmt);           // Kill assignment
          stmt = err_ctrl2("Cannot define field '." + tok + "' twice"); // Error is now the result
        }
        // Add type-check into graph
        if( t != null ) stmt = gvn(new TypeNode(t,stmt,errMsg()));
        // Add field into lexical scope, field is usable after initial set
        e.update(tok,stmt,_gvn,false); // Field now available 'bare' inside rest of scope
        if( is_final ) fs.set(toks._len);
        toks.add(tok);          // Gather for final type
        if( !peek(',') ) break; // Final comma is optional
      }
      require('}');
      Node c = e._scope.remove(" control ");
      _e = e._par;              // Pop nested environment
      if( e._scope != c ) set_ctrl(c);  // Carry any control changes back to outer scope

      Node[] flds = new Node[toks._len+1];
      for( int i=0; i<toks._len; i++ )
        flds[i+1] = e._scope.get(toks.at(i));
      byte[] finals = new byte[toks._len];
      for(int i=0; i<finals.length; i++ ) if( fs.get(i) ) finals[i] = 1;
      return do_mem(new NewNode(flds,TypeStruct.make(toks.asAry(),finals)));
    } // Pop lexical scope around struct
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
    else return null; // Not a token; specifically excludes e.g. all bytes >= 128, or most bytes < 32
    if( (c==':' || c==',') && _x-x==1 ) // Disallow bare ':' as a token; ambiguous with ?: and type annotations; same for ','
      { _x=x; return null; } // Unwind, not a token
    return new String(_buf,x,_x-x);
  }

  // Parse a number; WS already skipped and sitting at a digit.  Relies on
  // Javas number parsing.
  private Type number() {
    _pp.setIndex(_x);
    Number n = _nf.parse(_str,_pp);
    _x = _pp.getIndex();
    if( n instanceof Long   ) return n.longValue()==0 ? TypeNil.NIL : TypeInt.con(n.  longValue());
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
  private Type string() {
    int oldx = ++_x;
    byte c;
    while( (c=_buf[_x++]) != '"' ) {
      if( c=='%' ) throw AA.unimpl();
      if( c=='\\' ) throw AA.unimpl();
      if( _x == _buf.length ) return null;
    }
    TypeStr ts = TypeStr.con(new String(_buf,oldx,_x-oldx-1));
    // Convert to ptr-to-constant-memory-string
    TypeMemPtr ptr = TypeMemPtr.make(ts.get_alias(),ts);
    // Store the constant string to memory
    set_mem(gvn(new MemMergeNode(mem(),con(ptr))));
    return ptr;
  }

  /** Parse a type or return null
   *  type = tcon | tfun | tstruct | ttuple | tvar  // Type choices
   *  tcon = int, int[1,8,16,32,64], flt, flt[32,64], real, str[?]
   *  tfun = {[[type]* ->]? type } // Function types mirror func decls
   *  tstruct = @{ [id[:type?],]*}  // Struct types are field names with optional types
   *  ttuple = ([type?] [,[type?]]*) // List of types, trailing comma optional
   *  tvar = A previously declared type variable
   *
   *  Unknown tokens when type_var is false are treated as not-a-type.  When
   *  true, unknown tokens are treated as a forward-ref new type.
   */
  private Type type() { return typep(false); }
  // Returning a type variable assignment result.  Do not wrap TypeObj in a
  // TypeMemPtr, return a bare TypeObj instead... so it can be Named by the
  // type variable.  Flag to allow unknown type variables as forward-refs.
  private Type typev() {
    Type t = type0(true);
    return t==Type.ANY ? null : t;
  }
  private Type typep(boolean type_var) {
    Type t = type0(type_var);
    return t!=null && (t.base() instanceof TypeObj) // Automatically convert to reference for fields
      ? typeq(TypeMemPtr.make(BitsAlias.ALL,(TypeObj)t)) // And check for null-ness
      : t;
  }
  // Wrap in a nullable if there is a trailing '?'.  No spaces allowed
  private Type typeq(Type t) { return peek_noWS('?') ? t.meet_nil() : t; }

  // Type or null or TypeErr.ANY for '->' token
  private Type type0(boolean type_var) {
    byte c = skipWS();
    if( peek1(c,'{') ) { // Function type
      Ary<Type> ts = new Ary<>(new Type[1],0);  Type t;
      while( (t=typep(type_var)) != null && t != Type.ANY  )
        ts.add(t);              // Collect arg types
      Type ret;
      if( t==Type.ANY ) {       // Found ->, expect return type
        ret = typep(type_var);
        if( ret == null ) return null; // should return TypeErr missing type after ->
      } else {                  // Allow no-args and simple return type
        if( ts._len != 1 ) return null; // should return TypeErr missing -> in tfun
        ret = ts.pop();         // Get single return type
      }
      TypeTuple targs = TypeTuple.make(ts.asAry());
      if( !peek('}') ) return null;
      return typeq(TypeFunPtr.make(BitsFun.NZERO,targs,ret));
    }

    if( peek2(c,"@{") ) { // Struct type
      Ary<String> flds = new Ary<>(new String[1],0);
      Ary<Type  > ts   = new Ary<>(new Type  [1],0);
      while( true ) {
        String tok = token();    // Scan for 'id'
        if( tok == null ) break; // end-of-struct-def
        Type t = Type.SCALAR;    // Untyped, most generic field type
        if( peek(':') &&         // Has type annotation?
            (t=typep(type_var)) == null)              // Parse type, wrap ptrs
          return null;                                // not a type
        if( flds.find(tok) != -1 ) throw AA.unimpl(); // cannot use same field name twice
        flds.add(tok);          // Gather for final type
        ts  .add(t);
        if( !peek(',') ) break; // Final comma is optional
      }
      return peek('}') ? TypeStruct.make(flds.asAry(),ts.asAry()) : null;
    }

    // "()" is the zero-entry tuple
    // "(   ,)" is a 1-entry tuple
    // "(int )" is a 1-entry tuple (optional trailing comma)
    // "(int,)" is a 1-entry tuple (optional trailing comma)
    // "(,int)" is a 2-entry tuple
    // "(, , )" is a 2-entry tuple
    if( peek1(c,'(') ) { // Tuple type
      Ary<Type> ts = new Ary<>(new Type[1],0);
      while( (c=skipWS()) != ')' ) { // No more types...
        Type t = Type.SCALAR;    // Untyped, most generic field type
        if( c!=',' &&            // Has type annotation?
            (t=typep(type_var)) == null) // Parse type, wrap ptrs
          return null;                   // not a type
        ts.add(t);
        if( !peek(',') ) break; // Final comma is optional
      }
      return peek(')') ? TypeStruct.make(ts.asAry()) : null;
    }

    // Primitive type
    int oldx = _x;
    String tok = token();
    if( tok==null ) return null;
    if( tok.equals("->") ) return Type.ANY; // Found -> return sentinel
    Type t = _e.lookup_type(tok);
    if( t==null ) {              // Not a known type var
      if( lookup(tok) != null || // Yes a known normal var; resolve as a normal var
          !type_var ) {          // Or not inside a type-var assignment
        _x = oldx;               // Unwind if not a known type var
        return null;             // Not a type
      }
      _e.add_type(tok,t=TypeName.make_forward_def_type(tok,_e._scope.types()));
    }
    return t;
  }

  // Require a specific character (after skipping WS) or polite error
  private void require( char c ) {
    if( peek(c) ) return;
    err_ctrl0("Expected '"+c+"' but "+(_x>=_buf.length?"ran out of text":"found '"+(char)(_buf[_x])+"' instead"));
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
    if(  peek_noWS(s.charAt(1)) ) return true ;
    _x--;
    return false;
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
  private void skipEOL  () { while( _x < _buf.length && _buf[_x] != '\n' ) _x++; }
  private void skipBlock() { throw AA.unimpl(); }

  /** Return true if `c` passes a test */
  private static boolean isWS    (byte c) { return c == ' ' || c == '\t' || c == '\n' || c == '\r'; }
  private static boolean isAlpha0(byte c) { return ('a'<=c && c <= 'z') || ('A'<=c && c <= 'Z') || (c=='_'); }
  private static boolean isAlpha1(byte c) { return isAlpha0(c) || ('0'<=c && c <= '9'); }
  private static boolean isOp0   (byte c) { return "!#$%*+,-.=<>@^[]~/&".indexOf(c) != -1; }
  private static boolean isOp1   (byte c) { return isOp0(c) || ":?".indexOf(c) != -1; }
  private static boolean isDigit (byte c) { return '0' <= c && c <= '9'; }

  public Node gvn (Node n) { return n==null ? null : _gvn.xform(n); }
  private <N extends Node> N init( N n ) { return n==null ? null : _gvn.init (n); }
  private void kill( Node n ) { if( n._uses._len==0 ) _gvn.kill(n); }
  public Node ctrl() { return _e._scope.get(" control "); }
  public Node mem () { return _e._scope.get(" memory " ); }
  // Set and return a new control
  private void set_ctrl(Node n) { _e._scope.update(" control ",n,_gvn,true); }
  private void set_mem (Node n) { _e._scope.update(" memory " ,n,_gvn,true); }

  private @NotNull ConNode con( Type t ) { return _gvn.con(t); }

  public Node lookup( String tok ) { return _e.lookup(tok); }

  private Node do_call( Node call0 ) {
    Node call = gvn(call0);
    // Primitives frequently inline immediately, and do not need following
    // control/data projections.
    if( !(call instanceof CallNode)) return call;

    call.add_def(call);         // Hook, so not deleted after 1st use
    set_ctrl(  gvn(new CProjNode(call,0)));
    set_mem (  gvn(new MProjNode(call,1)));
    Node ret = gvn(new  ProjNode(call,2));
    ret.add_def(ret);           // Hook, so not deleted when call goes
    if( call.pop()._uses._len==0 )
      _gvn.kill(call);
    return ret.pop();
  }

  // NewNode updates merges the new allocation into all-of-memory and returns a
  // reference.
  private Node do_mem(NewNode nnn) {
    Node nn = gvn(nnn);
    nn.add_def(nn); // Self-hook to prevent deletion
    set_mem(gvn(new MemMergeNode(mem(),nn)));
    nn.pop(); // Remove self-hook
    return nn;
  }

  // Whack current control with a syntax error
  private ErrNode err_ctrl2( String s ) { return err_ctrl1(s,Type.SCALAR); }
  public  ErrNode err_ctrl1(String s, Type t) { return init(new ErrNode(Env.START,errMsg(s),t)); }
  private void err_ctrl0(String s) {
    set_ctrl(gvn(new ErrNode(ctrl(),errMsg(s),Type.CTRL)));
  }

  // Make a private clone just for delayed error messages
  private Parse( Parse P ) {
    _src = P._src;
    _buf = P._buf;
    _x   = P._x;
    _line= P._line;
    _e   = null;  _gvn = null;  _nf  = null;  _pp  = null;  _str = null;
  }
  // Delayed error message, just record line/char index and share code buffer
  private Parse errMsg() { return new Parse(this); }

  // Polite error message for mismatched types
  public String typerr( Type t0, Type t1 ) {
    assert !t0.is_forward_ref(); // Forward/unknown refs as args to a call report their own error
    return errMsg(t0.toString()+" is not a "+t1);
  }

  // Standard mis-use of a forward-ref error (assumed to be a forward-decl of a
  // recursive function; all other uses are treated as an unknown-ref error).
  public String forward_ref_err(FunNode fun) {
    String name = fun._name;
    return errMsg("Unknown ref '"+name+"'");
  }

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
