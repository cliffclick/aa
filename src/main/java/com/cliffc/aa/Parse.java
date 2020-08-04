package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.Util;
import com.cliffc.aa.util.VBitSet;
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
 *  stmt = [id[:type] [:]=]* ifex  // ids are (re-)assigned, and are available in later statements
 *  stmt = ^ifex                   // Early function exit
 *  ifex = expr [? stmt [: stmt]]  // trinary short-circuit logic; missing ":stmt" will default to 0
 *  expr = [uniop] term [binop term]*  // gather all the binops and sort by precedence
 *  term = id++ | id--             //
 *  term = tfact post              // A term is a tfact and some more stuff...
 *  post = empty                   // A term can be just a plain 'tfact'
 *  post = (tuple) post            // Application argument list
 *  post = tfact tfact             // Application as adjacent value
 *  post = .field post             // Field and tuple lookup
 *  post = .field [:]= stmt        // Field (re)assignment.  Plain '=' is a final assignment
 *  post = .field++ | .field--     // Allowed anytime a := is allowed
 *  post = :type post              // TODO: Add this, remove 'tfact'
 *  tfact= fact[:type]             // Typed fact
 *  fact = id                      // variable lookup
 *  fact = num                     // number
 *  fact = "string"                // string
 *  fact = (stmts)                 // General statements parsed recursively
 *  fact = tuple                   // Tuple builder
 *  fact = func                    // Anonymous function declaration
 *  fact = @{ stmts }              // Anonymous struct declaration, assignments define fields
 *  fact = {binop}                 // Special syntactic form of binop; no spaces allowed; returns function constant
 *  fact = {uniop}                 // Special syntactic form of uniop; no spaces allowed; returns function constant
 *  tuple= (stmts,[stmts,])        // Tuple; final comma is optional, first comma is required
 *  binop= +-*%&|/<>!= [] ]=       // etc; primitive lookup; can determine infix binop at parse-time
 *  uniop= -!~ []                  // etc; primitive lookup; can determine infix uniop at parse-time
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
 *  tstruct = @{ [id [tmod [type?]],]*}  // Struct types are field names with optional types.  Spaces not allowed
 *  tvar = id                      // Type variable lookup
 */

public class Parse {
  private final String _src;            // Source for error messages; usually a file name
  private Env _e;                       // Lookup context; pushed and popped as scopes come and go
  private final byte[] _buf;            // Bytes being parsed
  private int _x;                       // Parser index
  private int _line;                    // Zero-based line number
  public final GVNGCM _gvn;             // Pessimistic types

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
  String dump() { return _e._scope.dump(99); }// debugging hook
  String dumprpo() { return Env.START.dumprpo(false,false); }// debugging hook

  // Parse the string in the given lookup context, and return an executable
  // program.  Called in a partial-program context; passed in an existing
  // file-sized ScopeNode with existing variables which survive to the next call.
  // Used by the REPL to do incremental typing.
  TypeEnv go_partial( ) {
    prog();        // Parse a program
    _gvn.rereg(_e._scope,Type.ALL);
    _gvn.rereg(_e._par._scope,Type.ALL);
    _gvn.iter(1);   // Pessimistic optimizations; might improve error situation
    _gvn.gcp(_e._scope); // Global Constant Propagation
    _gvn.iter(3);   // Re-check all ideal calls now that types have been maximally lifted
    return gather_errors();
  }

  // Parse the string in the given lookup context, and return an executable
  // program.  Called in a whole-program context; passed in an empty ScopeNode
  // and nothing survives since there is no next call.  Used by the Exec to do
  // whole-compilation-unit typing.
  TypeEnv go_whole( ) {
    prog();                     // Parse a program
    // Delete names at the top scope before final optimization.
    _e.close_display(_gvn);
    _gvn.rereg(_e._scope,Type.ALL);
    _e._scope._live = _e._scope.live(_gvn);
    _gvn.iter(1);   // Pessimistic optimizations; might improve error situation
    remove_unknown_callers();
    _gvn.gcp(_e._scope); // Global Constant Propagation
    _gvn.iter(3);   // Re-check all ideal calls now that types have been maximally lifted
    return gather_errors();
  }

  private void remove_unknown_callers() {
    Ary<Node> uses = Env.ALL_CTRL._uses;
    // For all unknown uses of functions, they will all be known after GCP.
    // Remove the hyper-conservative ALL_CTRL edge.  Note that I canNOT run the
    // pessimistic iter() at this point, as GCP needs to discover all the
    // actual call-graph edges and install them directly on the FunNodes.
    for( int i=0; i<uses._len; i++ ) {
      Node use = uses.at(i);
      if( !use.is_prim() ) {
        assert use instanceof FunNode;
        assert use.in(1)==Env.ALL_CTRL;
        _gvn.set_def_reg(use,1,con(Type.XCTRL));
        i--;
      }
    }
  }

  private TypeEnv gather_errors() {
    _gvn.unreg(_e._scope);
    _gvn.unreg(_e._par._scope);
    Node res = _e._scope.pop(); // New and improved result
    Node mem = _e._scope.mem();
    Type tres = _gvn.type(res);
    TypeMem tmem = (TypeMem)_gvn.type(mem);

    // Hunt for typing errors in the alive code
    assert _e._par._par==null; // Top-level only
    VBitSet bs = new VBitSet();
    bs.set(Env.MEM_0._uid);     // Do not walk initial memory
    bs.set(Env.STK_0._uid);     // Do not walk initial memory
    bs.set(_e._scope._uid);     // Do not walk top-level scope
    bs.set(Env.DEFMEM._uid);    // Do not walk default memory
    Ary<String> errs0 = new Ary<>(new String[1],0);
    Ary<String> errs1 = new Ary<>(new String[1],0);
    Ary<String> errs2 = new Ary<>(new String[1],0);
    Ary<String> errs3 = new Ary<>(new String[1],0);
    res   .walkerr_def(errs0,errs1,errs2,errs3,bs,_gvn);
    ctrl().walkerr_def(errs0,errs1,errs2,errs3,bs,_gvn);
    mem   .walkerr_def(errs0,errs1,errs2,errs3,bs,_gvn);
    if( errs0.isEmpty() ) errs0.addAll(errs1);
    if( errs0.isEmpty() ) errs0.addAll(errs2);
    if( errs0.isEmpty() ) _e._scope.walkerr_use(errs0,new VBitSet(),_gvn);
    if( errs0.isEmpty() && skipWS() != -1 ) errs0.add(errMsg("Syntax error; trailing junk"));
    if( errs0.isEmpty() ) res.walkerr_gc(errs0,new VBitSet(),_gvn);
    // Most errors result in unresolved calls, so report others first.
    errs0.addAll(errs3);
    // Do not sort the errors, because they are reported in Reverse Post-Order
    // which means control-dependent errors are reported after earlier control
    // errors... i.e., you get the errors in execution order.

    kill(res);       // Kill Node for returned Type result

    return new TypeEnv(tres,tmem,_e,errs0.isEmpty() ? null : errs0);
  }

  /** Parse a top-level:
   *  prog = stmts END */
  private void prog() {
    _gvn._opt_mode = 0;
    Node res = stmts();
    if( res == null ) res = con(Type.ANY);
    _e._scope.set_rez(res,_gvn);  // Hook result
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
      last = stmt;
      stmt = tstmt();
      if( stmt == null ) stmt = stmt(lookup_current_scope_only);
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
    // Single-inheritance & vtables & RTTI:
    //            "Objects know thy Class"
    // Which means a TypeObj knows its Name.  Its baked into the vtable.
    // Which means TypeObj is named and not the pointer-to-TypeObj.
    // "Point= :@{x,y}" declares "Point" to be a type Name for "@{x,y}".
    Type ot = _e.lookup_type(tvar);
    Type tn = null;
    if( ot == null ) {        // Name does not pre-exist
      tn = t.set_name((tvar+":").intern());  // Add a name
      _e.add_type(tvar,tn);   // Assign type-name
    } else {
      if( ot instanceof TypeStruct && t instanceof TypeStruct )
        tn = ot.has_name() ? ((TypeStruct)ot).merge_recursive_type((TypeStruct)t) : null;
      if( tn == null ) return err_ctrl2("Cannot re-assign type '"+tvar+"'");
      else _e.def_type(tvar,tn);
    }

    // Add a constructor function.  If this is a primitive, build a constructor
    // taking the primitive.
    Parse bad = errMsg();
    Node rez, stk = _e._scope.stk();
    _gvn.unreg(stk); // add_fun expects the display is not in GVN
    if( !(t instanceof TypeObj) ) {
      PrimNode cvt = PrimNode.convertTypeName(t,tn,bad);
      rez = _e.add_fun(bad,tvar,gvn(cvt.as_fun(_gvn))); // Return type-name constructor
    } else {
      // Get the prefix type name; it must exist (and has an alias# already).
      if( t.has_name() ) throw AA.unimpl();

      // If this is a TypeObj, build a constructor taking a pointer-to-TypeObj
      // - and the associated memory state, i.e.  takes a ptr-to-@{x,y} and
      // returns a ptr-to-Named:@{x,y}.  This stores a v-table ptr into an
      // object.  The alias# does not change, but a TypeMem[alias#] would now
      // map to the Named variant.
      FunPtrNode epi1 = IntrinsicNode.convertTypeName((TypeObj)tn,bad,_gvn);
      rez = _e.add_fun(bad,tvar,epi1); // Return type-name constructor
      // For Structs, add a second constructor taking an expanded arg list
      if( t instanceof TypeStruct ) {   // Add struct types with expanded arg lists
        FunPtrNode epi2 = IntrinsicNode.convertTypeNameStruct((TypeStruct)tn, BitsAlias.RECORD, _gvn);
        Node rez2 = _e.add_fun(bad,tvar,epi2); // type-name constructor with expanded arg list
        _gvn.init0(rez2._uses.at(0));      // Force init of Unresolved
      }
    }
    _gvn.rereg(stk,stk.value(_gvn)); // Re-install display in GVN
    // TODO: Add reverse cast-away
    return rez;
  }

  /** A statement is a list of variables to final-assign or re-assign, and an
   *  ifex for the value.  The variables must not be forward refs and are
   *  available in all later statements.  Final-assigned variables can never be
   *  assigned again.
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
  private Node stmt() { return stmt(false); }
  private Node stmt(boolean lookup_current_scope_only) {
    if( peek('^') ) {           // Early function exit
      Node ifex = ifex();
      if( ifex==null ) ifex=_gvn.con(Type.XNIL);
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
        if( _e._scope.test_if() ) _x = oldx2; // Grammar ambiguity, resolve p?a:b from a:int
        else                      err_ctrl0("Missing type after ':'",null);
      }
      if( peek(":=") ) rs.set(toks._len);              // Re-assignment parse
      else if( !peek_not('=','=') ) {                  // Not any assignment
        // For structs, allow a bare id as a default def of nil
        if( lookup_current_scope_only && ts.isEmpty() && (peek(';') || peek('}') )){
          _x--;                                        // Push back statement end
          default_nil=true;                            // Shortcut def of nil
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
    Node ifex = default_nil ? con(Type.XNIL) : ifex(); // Parse an expression for the statement value
    if( ifex == null ) {        // No statement?
      if( toks._len == 0 ) return  null;
      ifex = err_ctrl2("Missing ifex after assignment of '"+toks.last()+"'");
    }
    // Honor all type requests, all at once, by inserting type checks on the ifex.
    for( int i=0; i<ts._len; i++ )
      ifex = typechk(ifex,ts.at(i),mem(),badts.at(i));
    ifex.keep();
    // Assign tokens to value
    for( int i=0; i<toks._len; i++ ) {
      String tok = toks.at(i);               // Token being assigned
      byte mutable = ts_mutable(rs.get(i));  // Assignment is mutable or final
      // Find scope for token.  If not defining struct fields, look for any
      // prior def.  If defining a struct, tokens define a new field in this scope.
      ScopeNode scope = lookup_scope(tok,lookup_current_scope_only);
      if( scope==null ) {                    // Token not already bound at any scope
        if( ifex instanceof FunPtrNode && !ifex.is_forward_ref() )
          ((FunPtrNode)ifex).fun().bind(tok); // Debug only: give name to function
        create(tok,con(Type.XNIL),TypeStruct.FRW); // Create at top of scope as ~scalar.
        scope = _e._scope;              // Scope is the current one
        scope.def_if(tok,mutable,true); // Record if inside arm of if (partial def error check)
      }
      // Handle re-assignments and forward referenced function definitions.
      Node n = scope.stk().get(tok); // Get prior direct binding
      if( n.is_forward_ref() ) { // Prior is actually a forward-ref, so this is the def
        assert !scope.stk().is_mutable(tok) && scope == _e._scope;
        if( ifex instanceof FunPtrNode )
          ((FunPtrNode)n).merge_ref_def(_gvn,tok,(FunPtrNode)ifex,(TypeMemPtr)_gvn.type(scope.ptr()));
        else ; // Can be here if already in-error
      } else { // Store into scope/NewObjNode/display
        // Assign into display
        Node ptr = get_display_ptr(scope,tok); // Pointer, possibly loaded up the display-display
        set_mem(gvn(new StoreNode(mem(),ptr,ifex,mutable,tok,badfs.at(i))));
        scope.def_if(tok,mutable,false); // Note 1-side-of-if update
      }
    }
    // Too much excitement happens while ifex hooked; put on worklist
    return _gvn.add_work(ifex.unhook());
  }

  /** Parse an if-expression, with lazy eval on the branches.  Assignments to
   *  new variables are allowed in either arm (as-if each arm is in a mini
   *  scope), and variables assigned on all live arms are available afterwards.
   *  ifex = expr [? stmt [: stmt]]
   */
  private Node ifex() {
    Node expr = expr();
    if( expr == null ) return null; // Expr is required, so missing expr implies not any ifex
    if( !peek('?') ) return expr;   // No if-expression

    _e._scope.push_if();            // Start if-expression tracking new defs
    Node ifex = init(new IfNode(ctrl(),expr)).keep();
    set_ctrl(gvn(new CProjNode(ifex,1))); // Control for true branch
    Node old_mem = mem().keep();          // Keep until parse false-side
    Node tex = stmt();                    // Parse true expression
    if( tex == null ) tex = err_ctrl2("missing expr after '?'");
    tex.keep();                    // Keep until merge point
    Node t_ctrl= ctrl().keep();    // Keep until merge point
    Node t_mem = mem ().keep();    // Keep until merge point

    _e._scope.flip_if();        // Flip side of tracking new defs
    set_ctrl(gvn(new CProjNode(ifex.unhook(),0))); // Control for false branch
    set_mem(old_mem);           // Reset memory to before the IF
    Node fex = peek(':') ? stmt() : con(Type.XNIL);
    if( fex == null ) fex = err_ctrl2("missing expr after ':'");
    fex.keep();                    // Keep until merge point
    Node f_ctrl= ctrl().keep();    // Keep until merge point
    Node f_mem = mem ().keep();    // Keep until merge point
    old_mem.unkeep(_gvn);

    Parse bad = errMsg();
    t_mem = _e._scope.check_if(true ,bad,_gvn,t_ctrl,t_mem); // Insert errors if created only 1 side
    f_mem = _e._scope.check_if(false,bad,_gvn,f_ctrl,f_mem); // Insert errors if created only 1 side
    _e._scope.pop_if();         // Pop the if-scope
    RegionNode r = set_ctrl(init(new RegionNode(null,t_ctrl.unhook(),f_ctrl.unhook())).keep());
    _gvn.setype(r,Type.CTRL);
    set_mem(gvn(new PhiNode(TypeMem.FULL,bad,r       ,t_mem.unhook(),f_mem.unhook())));
    return  gvn(new PhiNode(Type.SCALAR ,bad,r.unhook(),tex.unhook(),  fex.unhook())) ; // Ifex result
  }

  /** Parse an expression, a list of terms and infix operators.  The whole list
   *  is broken up into a tree based on operator precedence.
   *  expr = term [binop term]*
   */
  private Node expr() {
    Node unifun=null;
    int oldx = _x;
    String uni = token();
    if( uni!=null ) {
      unifun = _e.lookup_filter(uni.intern(),_gvn,1); // UniOp, or null
      if( unifun==null || unifun.op_prec() == -1 ) { unifun=null; _x=oldx; } // Not a uniop
    }

    // [unifun] term [binop term]*
    skipWS();
    oldx = _x;
    Node term = term();
    if( term == null ) return unifun; // Term is required, so missing term implies not any expr
    // Collect 1st fcn/arg pair
    Ary<Node > funs = new Ary<>(new Node [1],0);
    Ary<Parse> bads = new Ary<>(new Parse[1],0);
    try( TmpNode args = new TmpNode() ) {
      funs.add(unifun==null ? null : unifun.keep());
      args.add_def(term);
      bads.add(errMsg(oldx));

      // Now loop for binop/term pairs: parse Kleene star of [binop term]
      while( true ) {
        oldx = _x;
        String bin = token();
        if( bin==null ) break;    // Valid parse, but no more Kleene star
        Node binfun = _e.lookup_filter(bin.intern(),_gvn,2); // BinOp, or null
        if( binfun==null ) { _x=oldx; break; } // Not a binop, no more Kleene star
        skipWS();  oldx = _x;
        term = term();
        if( term == null ) term = err_ctrl2("missing expr after binary op "+bin);
        funs.add(binfun.keep());  args.add_def(term);  bads.add(errMsg(oldx));
      }

      // Have a list of interspersed operators and terms.
      // Build a tree with precedence.
      int max=-1;                 // First find max precedence.
      for( Node n : funs ) if( n != null ) max = Math.max(max,n.op_prec());
      // Now starting at max working down, group list by pairs into a tree
      while( max >= 0 && args._defs._len > 0 ) {
        for( int i=0; i<funs.len(); i++ ) { // For all ops of this precedence level, left-to-right
          Node  fun = funs.at(i);
          Parse bad = bads.at(i);
          if( fun==null ) continue;
          assert fun.op_prec() <= max;
          if( fun.op_prec() < max ) continue; // Not yet
          if( i==0 ) {
            Node call = do_call(new CallNode(true,new Parse[]{bad,bad},ctrl(),mem(),fun.unhook(),args.in(0)));
            args.set_def(0,call,_gvn);
            funs.setX(0,null);
            bads.setX(0,null);
          } else {
            Parse bad1 = bads.at(i-1);
            Node call = do_call(new CallNode(true,new Parse[]{bad1,bad1,bad},ctrl(),mem(),fun.unhook(),args.in(i-1),args.in(i)));
            args.set_def(i-1,call,_gvn);
            funs.remove(i);  args.remove(i);  bads.remove(i);  i--;
          }
        }
        max--;
      }
      if( funs.last() != null ) funs.pop().unhook();
      return args.del(0);       // Return the remaining expression
    }
  }

  /** Parse a term of a lisp-like application.  Field lookups and C-like calls
   *  associate have higher precedence than lisp-like application.
   *    term = arg post
   *    post = e | _ arg post
   */
  private Node term() {
    // Normal term expansion
    Node n = arg();
    if( n == null ) return null;
    while( true ) {             // Repeated application or field lookup is fine
      int oldx = _x;            // Parser reset point
      skipWS();                 // Skip to start of 1st arg
      int arg_start = _x;       // For errors
      Node arg = arg();         // Get argument
      if( arg == null )         // just 1 arg is just the arg
        return n;
      Type tn = _gvn.type(n);
      boolean may_fun = tn.isa(TypeFunPtr.GENERIC_FUNPTR);
      if( !may_fun && arg.may_prec() >= 0 ) { _x=oldx; return n; }
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
        n = err_ctrl2("A function is being called, but "+tn+" is not a function");
      } else {
        Parse[] badargs = new Parse[]{null,errMsg(arg_start)}; // The one arg start
        badargs[0] = errMsg(oldx-1); // Base call error reported at the opening paren
        n = do_call(new CallNode(true,badargs,ctrl(),mem(),n,arg)); // Pass the 1 arg
      }
    } // Else no trailing arg, just return value
  }

  /** Parse an argument.  Field lookups and C-like calls associate
   *  left-to-right with higher precedence than lisp-like application.
   *    arg  = id++ | id--
   *    arg  = tfact [tuple | .field]* [.field[:]=stmt | .field++ | .field-- | e]
   */
  private Node arg() {
    // Check for id++ / id--
    int oldx = _x;
    String tok = token();
    if( tok != null ) {
      Node n;
      if( peek("++") && (n=inc(tok, 1))!=null ) return n;
      if( peek("--") && (n=inc(tok,-1))!=null ) return n;
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
          byte fin = _buf[_x-2]==':' ? TypeStruct.FRW : TypeStruct.FFNL;
          Node stmt = stmt();
          if( stmt == null ) n = err_ctrl2("Missing stmt after assigning field '."+fld+"'");
          else set_mem( gvn(new StoreNode(mem(),castnn,n=stmt,fin,fld ,errMsg(fld_start))));
        } else {
          n = gvn(new LoadNode(mem(),castnn,fld,errMsg(fld_start)));
        }

      } else if( peek('(') ) {  // Attempt a function-call
        oldx = _x;
        skipWS();                 // Skip to start of 1st arg
        int first_arg_start = _x;
        Node arg = tuple(oldx,stmts(),first_arg_start); // Parse argument list
        if( arg == null )       // tfact but no arg is just the tfact
          { _x = oldx; return n; }
        Type tn = _gvn.type(n);
        boolean may_fun = tn.isa(TypeFunPtr.GENERIC_FUNPTR);
        if( !may_fun && arg.may_prec() >= 0 ) { _x=oldx; return n; }
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
          n = err_ctrl2("A function is being called, but "+tn+" is not a function");
        } else {
          Parse[] badargs = ((NewObjNode)arg.in(0))._fld_starts; // Args from tuple
          badargs[0] = errMsg(oldx-1); // Base call error reported at the opening paren
          n = do_call(new CallNode(false,badargs,ctrl(),mem(),n,arg)); // Pass the tuple
        }

      } else {
        return n;               // Just an arg
      }
    } // Else no trailing arg, just return value
  }

  // Handle post-increment/post-decrement operator.
  // Does not define a field in structs: "@{ x++; y=2 }" - syntax error, no such field x
  private Node inc(String tok, int d) {
    ScopeNode scope = lookup_scope(tok=tok.intern(),false); // Find prior scope of token
    // Need a load/call/store sensible options
    Node n;
    if( scope==null ) {         // Token not already bound to a value
      create(tok,con(Type.XNIL),ts_mutable(true));
      scope = _e._scope;
    } else {                    // Check existing token for mutable
      if( !scope.is_mutable(tok) )
        return err_ctrl2("Cannot re-assign final val '"+tok+"'");
    }

    // Scope is discovered by walking lexical display stack.
    // Pointer to the proper display is found via ptr-walking live display stack.
    // Now properly load from the display
    Node ptr = get_display_ptr(scope,tok);
    n = gvn(new LoadNode(mem(),ptr,tok,null));
    if( n.is_forward_ref() )    // Prior is actually a forward-ref
      return err_ctrl2(forward_ref_err(((FunPtrNode)n).fun()));
    // Do a full lookup on "+", and execute the function
    Node plus = _e.lookup_filter("+",_gvn,2);
    Node sum = do_call(new CallNode(true,errMsgs(2),ctrl(),mem(),plus,n.keep(),con(TypeInt.con(d))));
    // Active memory for the chosen scope, after the call to plus
    set_mem(gvn(new StoreNode(mem(),ptr,sum,TypeStruct.FRW,tok,errMsg())));
    return n.unhook();          // Return pre-increment value
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
    // Anonymous function or operator
    if( peek1(c,'{') ) {
      String tok = token0();
      Node op = tok == null ? null : _e.lookup_filter(tok.intern(),_gvn,2); // TODO: filter by >2 not ==3
      if( peek('}') && op != null && op.op_prec() > 0 ) {
        // If a primitive unresolved, clone to give a proper error message.
        if( op instanceof UnresolvedNode && op.is_prim() )
          op = gvn(((UnresolvedNode)op).copy(errMsg()));
        return op;              // Return operator as a function constant
      }
      _x = oldx+1;              // Back to the opening paren
      return func();            // Anonymous function
    }
    // Anonymous struct
    if( peek2(c,"@{") ) return struct();

    // Check for a valid 'id'
    String tok = token0();
    if( tok == null ) { _x = oldx; return null; }
    tok = tok.intern();
    if( tok.equals("=") || tok.equals("^"))
      { _x = oldx; return null; } // Disallow '=' as a fact, too easy to make mistakes
    ScopeNode scope = lookup_scope(tok,false);
    if( scope == null ) { // Assume any unknown ref is a forward-ref of a recursive function
      Node fref = gvn(FunPtrNode.forward_ref(_gvn,tok,errMsg(oldx)));
      // Place in nearest enclosing closure scope
      _e._scope.stk().create(tok.intern(),fref,TypeStruct.FFNL,_gvn);
      return fref;
    }
    Node def = scope.get(tok);    // Get top-level value; only sane if no stores allowed to modify it
    // Disallow uniop and binop functions as factors.  Only possible if trying
    // to use an operator as a factor, such as "plus = +" or "f(1,+,2)".
    if( def.op_prec() > 0 ) { _x = oldx; return null; }
    // Forward refs always directly assigned into scope and never updated.
    if( def.is_forward_ref() ) return def;

    // Else must load against most recent display update.  Get the display to
    // load against.  If the scope is local, we load against it directly,
    // otherwise the display is passed in as a hidden argument.
    Node ptr = get_display_ptr(scope,tok.intern());
    return gvn(new LoadNode(mem(),ptr,tok,null));
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
      args.push(s);
      if( !peek(',') ) break;   // Final comma is optional
      skipWS();                 // Skip to arg start before recording arg start
      bad = errMsg();           // Record arg start
      s=stmts();                // Parse arg
    }
    require(')',oldx);          // Balanced closing paren

    // Build the tuple from gathered args
    TypeStruct mt_tuple = TypeStruct.make(false,new String[]{"^"},TypeStruct.ts(Type.XNIL),new byte[]{TypeStruct.FFNL},true);
    NewObjNode nn = new NewObjNode(false,BitsAlias.RECORD,mt_tuple,con(Type.XNIL));
    for( int i=0; i<args._len; i++ )
      nn.create_active((""+i).intern(),args.at(i),TypeStruct.FFNL,_gvn);
    nn._fld_starts = bads.asAry();
    nn.no_more_fields();

    // NewNode returns a TypeMem and a TypeMemPtr (the reference).
    NewObjNode nnn = (NewObjNode)gvn(nn);
    set_mem( Env.DEFMEM.make_mem_proj(_gvn,nnn,mem()) );
    return gvn(new ProjNode(1, nnn));
  }

  /** Parse anonymous struct; the opening "@{" already parsed.  A lexical scope
   *  is made and new variables are defined here.  Next comes statements, with
   *  each assigned value becoming a struct member, then the closing "}".
   *  struct = \@{ stmts }
   */
  private Node struct() {
    int oldx = _x-1; Node ptr;  // Opening @{
    try( Env e = new Env(_e,errMsg(oldx-1), false) ) { // Nest an environment for the local vars
      _e = e;                   // Push nested environment
      stmts(true);              // Create local vars-as-fields
      require('}',oldx);        // Matched closing }
      assert ctrl() != e._scope;
      ptr = e._scope.ptr().keep();         // A pointer to the constructed object
      e._par._scope.set_ctrl(ctrl(),_gvn); // Carry any control changes back to outer scope
      e._par._scope.set_mem (mem (),_gvn); // Carry any memory  changes back to outer scope
      _e = e._par;                         // Pop nested environment
    } // Pop lexical scope around struct
    return ptr.unhook();
  }

  /** Parse an anonymous function; the opening '{' already parsed.  After the
   *  '{' comes an optional list of arguments and a '->' token, and then any
   *  number of statements separated by ';'.
   *  func = { [[id]* ->]? stmts }
   */
  private static final byte args_are_mutable=ts_mutable(false); // Args mutable or r/only by default
  private Node func() {
    int oldx = _x;              // Past opening '{'
    Ary<String> ids = new Ary<>(new String[1],0);
    Ary<Type  > ts  = new Ary<>(new Type  [1],0);
    Ary<Parse > bads= new Ary<>(new Parse [1],0);

    // Push an extra hidden display argument.  Similar to java inner-class ptr
    // or when inside of a struct definition: 'this'.
    Node parent_display = _e._scope.ptr();
    TypeMemPtr tpar_disp = (TypeMemPtr)_gvn.type(parent_display); // Just a TMP of the right alias
    ids .push("^");
    ts  .push(tpar_disp);
    bads.push(null);

    // Parse arguments
    while( true ) {
      String tok = token();
      if( tok == null ) { _x=oldx; break; } // not a "[id]* ->"
      if( tok.equals("->") ) break; // End of argument list
      if( !isAlpha0((byte)tok.charAt(0)) ) { _x=oldx; break; } // not a "[id]* ->"
      Type t = Type.SCALAR;    // Untyped, most generic type
      Parse bad = errMsg();    // Capture location in case of type error
      if( peek(':') &&         // Has type annotation?
          (t=type())==null ) { // Get type
        // If no type, might be "{ x := ...}" or "{ fun arg := ...}" which can
        // be valid stmts, hence this may be a no-arg function.
        if( ids._len-1 <= 2 ) { _x=oldx; break; }
        else {
          // Might be: "{ x y z:bad -> body }" which cannot be any stmt.  This
          // is an error in any case.  Treat as a bad type on a valid function.
          err_ctrl0(peek(',') ? "Bad type arg, found a ',' did you mean to use a ';'?" : "Missing or bad type arg",null);
          t = Type.SCALAR;
          skipNonWS();         // Skip possible type sig, looking for next arg
        }
      }
      ids .add(tok.intern());   // Accumulate args
      ts  .add(t  );
      bads.add(bad);
    }
    // If this is a no-arg function, we may have parsed 1 or 2 tokens as-if
    // args, and then reset.  Also reset to just the display arg.
    if( _x == oldx ) { ids.set_len(1); ts.set_len(1); bads.set_len(1);  }

    // Build the FunNode header
    Node old_ctrl = ctrl().keep();
    Node old_mem  = mem ().keep();
    FunNode fun = gvn(new FunNode(ids.asAry(),ts.asAry()).add_def(Env.ALL_CTRL)).keep();
    // Build Parms for system incoming values
    Node rpc = gvn(new ParmNode(-1,"rpc",fun,con(TypeRPC.ALL_CALL),null)).keep();
    Node mem = gvn(new ParmNode(-2,"mem",fun,TypeMem.MEM,Env.DEFMEM,null));
    Node clo = gvn(new ParmNode( 0,"^"  ,fun,con(tpar_disp),null));
    set_ctrl(fun);              // New control is function head
    set_mem(mem);               // New memory  is function memory

    // Increase scope depth for function body.
    try( Env e = new Env(_e,errMsg(oldx-1), true) ) { // Nest an environment for the local vars
      _e = e;                   // Push nested environment
      // Display is special: the default is simply the outer lexical scope.
      // But here, in a function, the display is actually passed in as a hidden
      // extra argument and replaces the default.
      NewObjNode stk = e._scope.stk();
      stk.update(0,ts_mutable(false),clo,_gvn);

      // Parms for all arguments
      Parse errmsg = errMsg();  // Lazy error message
      for( int i=1; i<ids._len; i++ ) { // User parms start at#1
        Node parm = gvn(new ParmNode(i,ids.at(i),fun,con(Type.SCALAR),errmsg));
        create(ids.at(i),parm, args_are_mutable);
      }

      // Parse function body
      Node rez = stmts();       // Parse function body
      if( rez == null ) rez = err_ctrl2("Missing function body");
      require('}',oldx-1);      // Matched with opening {}
      // Merge normal exit into all early-exit paths
      if( e._scope.is_closure() ) rez = merge_exits(rez);
      // Standard return; function control, memory, result, RPC.  Plus a hook
      // to the function for faster access.
      RetNode ret = (RetNode)gvn(new RetNode(ctrl(),mem(),rez,rpc.unhook(),fun.unhook()));
      // The FunPtr builds a real display; any up-scope references are passed in now.
      Node fptr = gvn(new FunPtrNode(ret,e._par._scope.ptr()));
      _e = _e._par;                // Pop nested environment
      set_ctrl(old_ctrl.unhook()); // Back to the pre-function-def control
      set_mem (old_mem .unhook()); // Back to the pre-function-def memory
      return fptr;                 // Return function; close-out and DCE 'e'
    }
  }

  private Node merge_exits(Node rez) {
    rez.keep();
    ScopeNode s = _e._scope;
    Node ctrl = s.early_ctrl();
    Node mem  = s.early_mem ();
    Node val  = s.early_val ();
    s.early_kill();
    if( ctrl == null ) return rez.unhook(); // No other exits to merge into
    set_ctrl(ctrl=init(ctrl.add_def(ctrl())));
    _gvn.setype(ctrl,Type.CTRL);
    mem.set_def(0,ctrl,null);
    val.set_def(0,ctrl,null);
    set_mem (gvn(mem.add_def(mem())));
    return   gvn(val.add_def(rez.unhook())) ;
  }

  // Merge this early exit path into all early exit paths being recorded in the
  // current Env/Scope.
  Node do_exit( ScopeNode s, Node rez ) {
    Node ctrl = s.early_ctrl();
    Node mem  = s.early_mem ();
    Node val  = s.early_val ();
    if( ctrl == null ) {
      s.set_def(4,ctrl=new RegionNode((Node)null),null);
      s.set_def(5,mem =new PhiNode(TypeMem.MEM, null,(Node)null),null);
      s.set_def(6,val =new PhiNode(Type.SCALAR, null,(Node)null),null);
    }
    ctrl.add_def(ctrl());
    mem .add_def(mem ());
    val .add_def(rez   );
    set_ctrl(con(Type.XCTRL  ));
    set_mem (con(TypeMem.XMEM));
    return   con(Type.XNIL   ) ;
  }

  // Add a typecheck into the graph, with a shortcut if trivially ok.
  private Node typechk(Node x, Type t, Node mem, Parse bad) {
    return t == null || _gvn.type(x).isa(t) ? x : gvn(new TypeNode(mem,x,t,bad));
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
    if( c=='-' && _x-x>2 && _buf[x+1]=='>' ) // Disallow leading "->", confusing with function parameter list end; eg "not={x->!x}"
      _x=x+2;                                // Just return the "->"
    return new String(_buf,x,_x-x);
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
      if( c=='%' ) throw AA.unimpl();
      if( c=='\\' ) throw AA.unimpl();
      if( _x == _buf.length ) return null;
    }
    TypeStr ts = TypeStr.con(new String(_buf,oldx,_x-oldx-1).intern());
    // Convert to ptr-to-constant-memory-string
    NewStrNode nnn = gvn( new NewStrNode(ts,con(ts))).keep();
    set_mem(Env.DEFMEM.make_mem_proj(_gvn,nnn,mem()));
    return gvn( new ProjNode(1, nnn.unhook()));
  }

  /** Parse a type or return null
   *  type = tcon | tfun | tstruct | ttuple | tvar  // Type choices
   *  tcon = int, int[1,8,16,32,64], flt, flt[32,64], real, str[?]
   *  tfun = {[[type]* ->]? type } // Function types mirror func decls
   *  tmod = = | := | ==  // '=' is r/final, ':=' is r/w, '==' is read-only
   *  tstruct = @{ [id [tmod [type?]];]*}  // Struct types are field names with optional types.  Spaces not allowed
   *  ttuple = ([type?] [,[type?]]*) // List of types, trailing comma optional
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
    if( t==null ) return null;
    if( !(t instanceof TypeObj) ) return t; // Primitives are not wrapped
    // Automatically convert to reference for fields.
    // Make a reasonably precise alias.
    int type_alias = t instanceof TypeStruct ? BitsAlias.RECORD : BitsAlias.STR;
    TypeMemPtr tmp = TypeMemPtr.make(BitsAlias.make0(type_alias),(TypeObj)t);
    return typeq(tmp);          // And check for null-ness
  }
  // Wrap in a nullable if there is a trailing '?'.  No spaces allowed
  private Type typeq(Type t) { return peek_noWS('?') ? t.meet_nil(Type.XNIL) : t; }

  // No mod is r/w.  ':=' is read-write, '=' is final.
  // Currently '-' is  ambiguous with function arrow ->.
  private byte tmod() {
    if( peek_not('=','=') ) { _x--; return TypeStruct.FFNL; } // final     , leaving trailing '='
    if( peek(":="       ) ) { _x--; return TypeStruct.FRW ; } // read-write, leaving trailing '='
    if( peek("=="       ) ) { _x--; return TypeStruct.FRO ; } // read-only , leaving trailing '='
    // Default for unnamed field mod
    return TypeStruct.FRW;
  }

  // Type or null or Type.ANY for '->' token
  private Type type0(boolean type_var) {
    if( peek('{') ) {           // Function type
      Ary<Type> ts = new Ary<>(new Type[]{TypeMemPtr.DISP_SIMPLE});  Type t;
      while( (t=typep(type_var)) != null && t != Type.ANY  )
        ts.add(t);              // Collect arg types
      Type ret;
      if( t==Type.ANY ) {       // Found ->, expect return type
        ret = typep(type_var);
        if( ret == null ) return null; // should return TypeErr missing type after ->
      } else {                  // Allow no-args and simple return type
        if( ts._len != 2 ) return null; // should return TypeErr missing -> in tfun
        ret = ts.pop();         // e.g. { int } Get single return type
      }
      TypeStruct targs = TypeStruct.make_args(ts.asAry());
      if( !peek('}') ) return null;
      return typeq(TypeFunSig.make(targs,ret));
    }

    if( peek("@{") ) {          // Struct type
      Ary<String> flds = new Ary<>(new String[]{"^"});
      Ary<Type  > ts   = new Ary<>(new Type  []{TypeMemPtr.DISP_SIMPLE});
      Ary<Byte  > mods = new Ary<>(new Byte  []{TypeStruct.FFNL});
      while( true ) {
        String tok = token();            // Scan for 'id'
        if( tok == null ) break;         // end-of-struct-def
        Type t = Type.SCALAR;            // Untyped, most generic field type
        byte tmodf = tmod();             // Field access mod; trailing '=' left for us
        if( peek('=') &&                 // Has type annotation?
            (t=typep(type_var)) == null) // Parse type, wrap ptrs
          t = Type.SCALAR;               // No type found, assume default
        tok = tok.intern();              // Only 1 copy
        if( flds.find(tok) != -1 ) throw AA.unimpl(); // cannot use same field name twice
        flds  .add(tok);                 // Gather for final type
        ts    .add(t);
        mods  .add(tmodf);
        if( !peek(';') ) break; // Final semi-colon is optional
      }
      byte[] finals = new byte[mods._len];
      for( int i=0; i<mods._len; i++ )  finals[i] = mods.at(i);
      return peek('}') ? TypeStruct.make(false,flds.asAry(),ts.asAry(),finals,true) : null;
    }

    // "()" is the zero-entry tuple
    // "(   ,)" is a 1-entry tuple
    // "(int )" is a 1-entry tuple (optional trailing comma)
    // "(int,)" is a 1-entry tuple (optional trailing comma)
    // "(,int)" is a 2-entry tuple
    // "(, , )" is a 2-entry tuple
    if( peek('(') ) { // Tuple type
      byte c;
      Ary<Type> ts = new Ary<>(new Type[]{TypeMemPtr.DISP_SIMPLE});
      while( (c=skipWS()) != ')' ) { // No more types...
        Type t = Type.SCALAR;    // Untyped, most generic field type
        if( c!=',' &&            // Has type annotation?
            (t=typep(type_var)) == null) // Parse type, wrap ptrs
          return null;                   // not a type
        ts.add(t);
        if( !peek(',') ) break; // Final comma is optional
      }
      return peek(')') ? TypeStruct.make_tuple_open(ts.asAry()) : null;
    }

    // Primitive type
    int oldx = _x;
    String tok = token();
    if( tok==null ) return null;
    tok = tok.intern();
    if( Util.eq(tok,"->") ) return Type.ANY; // Found -> return sentinel
    Type t = _e.lookup_type(tok);
    if( t==null ) {              // Not a known type var
      if( lookup(tok) != null || // Yes a known normal var; resolve as a normal var
          !type_var ) {          // Or not inside a type-var assignment
        _x = oldx;               // Unwind if not a known type var
        return null;             // Not a type
      }
      _e.add_type(tok,t=TypeStruct.make_forward_def_type(tok));
    }
    return t;
  }

  // Require a closing character (after skipping WS) or polite error
  private void require( char c, int oldx ) {
    if( peek(c) ) return;
    Parse bad = errMsg();       // Generic error
    bad._x = oldx;              // Openning point
    err_ctrl0("Expected closing '"+c+"' but "+(_x>=_buf.length?"ran out of text":"found '"+(char)(_buf[_x])+"' instead"),bad);
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
  // Peek 'c' and NOT followed by 'no'
  private boolean peek_not( char c, char no ) {
    byte c0 = skipWS();
    if( c0 != c || (_x+1 < _buf.length && _buf[_x+1] == no) ) return false;
    _x++;
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
  private void skipEOL  () { while( _x < _buf.length && _buf[_x] != '\n' ) _x++; }
  private void skipBlock() { throw AA.unimpl(); }
  // Advance parse pointer to next WS.  Used for parser syntax error recovery.
  private void skipNonWS() {
    while( _x < _buf.length && !isWS(_buf[_x]) ) _x++;
  }

  /** Return true if `c` passes a test */
  private static boolean isWS    (byte c) { return c == ' ' || c == '\t' || c == '\n' || c == '\r'; }
  private static boolean isAlpha0(byte c) { return ('a'<=c && c <= 'z') || ('A'<=c && c <= 'Z') || (c=='_'); }
  private static boolean isAlpha1(byte c) { return isAlpha0(c) || ('0'<=c && c <= '9'); }
  private static boolean isOp0   (byte c) { return "!#$%*+,-.=<>^[]~/&".indexOf(c) != -1; }
  private static boolean isOp1   (byte c) { return isOp0(c) || ":?".indexOf(c) != -1; }
  public  static boolean isDigit (byte c) { return '0' <= c && c <= '9'; }

  // Utilities to shorten code for common cases
  public Node gvn (Node n) { return n==null ? null : _gvn.xform(n); }
  private <N extends Node> N init( N n ) { return n==null ? null : _gvn.init(n); }
  private void kill( Node n ) { if( n._uses._len==0 ) _gvn.kill(n); }
  public Node ctrl() { return _e._scope.ctrl(); }
  // Set and return a new control
  private <N extends Node> N set_ctrl(N n) { return _e._scope.set_ctrl(n,_gvn); }
  private Node mem() { return _e._scope.mem(); }
  private Node set_mem(Node n) { return _e._scope.set_mem(n,_gvn); }

  private @NotNull ConNode con( Type t ) { return _gvn.con(t); }

  // Lookup & extend scopes
  public  Node lookup( String tok ) { return _e.lookup(tok); }
  private ScopeNode lookup_scope( String tok, boolean lookup_current_scope_only ) { return _e.lookup_scope(tok,lookup_current_scope_only); }
  public  ScopeNode scope( ) { return _e._scope; }
  private void create( String tok, Node n, byte mutable ) { _e._scope.stk().create(tok,n,mutable,_gvn ); }
  private static byte ts_mutable(boolean mutable) { return mutable ? TypeStruct.FRW : TypeStruct.FFNL; }

  // Get the display pointer.  The function call
  // passed in the display as a hidden argument which we return here.
  private Node get_display_ptr(ScopeNode scope, String tok) {
    // Issue Loads against the Display, until we get the correct scope.  The
    // Display is a linked list of displays, and we already checked that token
    // exists at scope up in the display.
    Env e = _e;
    Node ptr = e._scope.ptr();
    Node mmem = mem();
    while( true ) {
      if( scope == e._scope ) return ptr;
      ptr = gvn(new LoadNode(mmem,ptr,"^",null)); // Gen linked-list walk code, walking display slot
      assert _gvn.sharptr(ptr,mmem).is_display_ptr();
      e = e._par;                                 // Walk linked-list in parser also
    }
  }

  // Insert a call, with memory splits.  Wiring happens later, and when a call
  // is wired it picks up projections to merge at the Fun & Parm nodes.
  private Node do_call( CallNode call0 ) {
    CallNode call = (CallNode)gvn(call0);
    // Call Epilog takes in the call which it uses to track wireable functions.
    // CallEpi internally tracks all wired functions.
    Node cepi = gvn(new CallEpiNode(call,Env.DEFMEM)).keep();
    set_ctrl(   gvn(new CProjNode(cepi,0)));
    set_mem (   gvn(new MProjNode(cepi,1))); // Return memory from all called functions
    return gvn(new ProjNode(2, cepi.unhook()));
  }

  // Whack current control with a syntax error
  private ErrNode err_ctrl2( String s ) { return init(new ErrNode(Env.START,errMsg(s),null)); }
  private void err_ctrl0(String s, Parse bad) {
    set_ctrl(gvn(new ErrNode(ctrl(),errMsg(s),bad)));
  }

  // Make a private clone just for delayed error messages
  private Parse( Parse P ) {
    _src = P._src;
    _buf = P._buf;
    _x   = P._x;
    _line= P._line;
    _gvn = P._gvn;
    _e   = null;  _nf  = null;  _pp  = null;  _str = null;
  }
  // Delayed error message, just record line/char index and share code buffer
  Parse errMsg() { return errMsg(_x); }
  Parse errMsg(int x) { Parse P = new Parse(this); P._x=x; return P; }
  Parse[] errMsgs(int n) {      // n==1 or 2 arg operator
    Parse e = errMsg();
    return n==1 ? new Parse[]{null,e,e} : new Parse[]{null,e,e,e};
  }

  // Polite error message for mismatched types
  public String typerr( Type actual, Node mem, Type expected ) {
    Type t = mem==null ? null : _gvn.type(mem);
    TypeMem tmem = t instanceof TypeMem ? (TypeMem)t : null;
    String s0 = typerr(actual  ,tmem);
    String s1 = typerr(expected,null); // Expected is already a complex ptr, does not depend on memory
    return errMsg(s0+" is not a "+s1);
  }
  public String typerr( Type actual, Node mem, Type[] expecteds ) {
    Type t = mem==null ? null : _gvn.type(mem);
    TypeMem tmem = t instanceof TypeMem ? (TypeMem)t : null;
    SB sb = new SB().p(typerr(actual,tmem));
    sb.p( expecteds.length==1 ? " is not a " : " is none of (");
    for( Type expect : expecteds ) sb.p(typerr(expect,null)).p(',');
    sb.unchar().p(expecteds.length==1 ? "" : ")");
    return errMsg(sb.toString());
  }
  private static String typerr( Type t, TypeMem tmem ) {
    return t.is_forward_ref()
      ? ((TypeFunPtr)t).names(false)
      : (t instanceof TypeMemPtr
         ? t.str(new SB(), null, tmem).toString()
         : t.toString());
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
