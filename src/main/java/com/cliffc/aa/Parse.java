package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
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
 *  post = tfact post              // Application as adjacent value
 *  post = .field post             // Field and tuple lookup
 *  post = .field [:]= stmt        // Field (re)assignment.  Plain '=' is a final assignment
 *  post = .field++ | .field--     // Allowed anytime a := is allowed
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
 *  tmod = = | := | ==             // '=' is r/only, ':=' is r/w, '==' is final
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
  String dump() { return _e._scope.dump(99,_gvn); }// debugging hook
  String dumprpo() { return Env.START.dumprpo(_gvn,false); }// debugging hook

  // Parse the string in the given lookup context, and return an executable
  // program.  Called in a partial-program context; passed in an existing
  // file-sized ScopeNode with existing variables which survive to the next call.
  // Used by the REPL to do incremental typing.
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
    // Delete names at the top scope before final optimization.
    for( Node use : _e._scope.stk()._uses )
      _gvn.add_work(use);        // No more fields added; trailing DProj needs to sharpen
    _e._scope.set_ptr(null,_gvn); // delete top-level names
    _gvn.iter();   // Pessimistic optimizations; might improve error situation
    // Attempt to remove memory state from top-level Scope, cannot use the
    // normal gvn.iter() because Scope is _keep==1.
    if( _e._scope.ideal(_gvn) != null ) _gvn.iter();
    remove_unknown_callers();
    _gvn.gcp(_e._scope); // Global Constant Propagation
    _gvn.iter();   // Re-check all ideal calls now that types have been maximally lifted
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
      if( use._uid >= GVNGCM._INIT0_CNT ) {
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
    Node res = _e._scope.pop(); // New and improved result
    Node mem = _e._scope.mem();
    // Hunt for typing errors in the alive code
    assert _e._par._par==null; // Top-level only
    VBitSet bs = new VBitSet();
    bs.set(Env.MEM_0._uid);     // Do not walk initial memory
    bs.set(Env.STK_0._uid);     // Do not walk initial memory
    bs.set(_e._scope._uid);     // Do not walk top-level scope
    Ary<String> errs0 = new Ary<>(new String[1],0);
    Ary<String> errs1 = new Ary<>(new String[1],0);
    Ary<String> errs2 = new Ary<>(new String[1],0);
    Ary<String> errs3 = new Ary<>(new String[1],0);
    res   .walkerr_def(errs0,errs1,errs2,errs3,bs,_gvn);
    ctrl().walkerr_def(errs0,errs1,errs2,errs3,bs,_gvn);
    if( mem != null ) mem.walkerr_def(errs0,errs1,errs2,errs3,bs,_gvn);
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

    Type tres = _gvn.type(res);
    kill(res);       // Kill Node for returned Type result
    TypeObj tobj = TypeObj.XOBJ;
    // If returning memory, return the (shallow) object pointed at
    if( mem != null ) {
      Type tmem = _gvn.type(mem);
      kill(mem);       // Kill Node for returned Type result
      if( tres instanceof TypeMemPtr ) {
        TypeMemPtr tmp = (TypeMemPtr)tres;
        tobj = ((TypeMem)tmem).ld(tmp);
      }
    }
    return new TypeEnv(tres,tobj,_e,errs0.isEmpty() ? null : errs0);
  }

  /** Parse a top-level:
   *  prog = stmts END */
  private void prog() {
    _gvn._opt_mode = 0;
    Node res = stmts();
    if( res == null ) res = con(Type.ANY);
    res = merge_exits(res);
    all_mem();                    // Close off top-level active memory
    _e._par._scope.all_mem(_gvn); // Loads against primitive scope will 'activate' memory, close it also
    _e._scope.add_def(res);       // Hook result
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
    TypeName tn;
    if( ot == null ) {        // Name does not pre-exist
      tn = TypeName.make_new_type(tvar,t);
      _e.add_type(tvar,tn);   // Assign type-name
    } else {
      tn = ot instanceof TypeName ? ((TypeName)ot).merge_recursive_type(t) : null;
      if( tn == null ) return err_ctrl2("Cannot re-assign type '"+tvar+"'");
    }

    // Add a constructor function.  If this is a primitive, build a constructor
    // taking the primitive.
    Parse bad = errMsg();
    Node rez, stk = _e._scope.stk();
    _gvn.unreg(stk); // add_fun expects the closure is not in GVN
    if( !(t instanceof TypeObj) ) {
      PrimNode cvt = PrimNode.convertTypeName(t,tn,bad);
      rez = _e.add_fun(bad,tvar,gvn(cvt.as_fun(_gvn))); // Return type-name constructor
    } else {
      // If this is a TypeObj, build a constructor taking a pointer-to-TypeObj
      // - and the associated memory state, i.e.  takes a ptr-to-@{x,y} and
      // returns a ptr-to-Named:@{x,y}.  This stores a v-table ptr into an
      // object.  The alias# does not change, but a TypeMem[alias#] would now
      // map to the Named variant.
      FunPtrNode epi1 = IntrinsicNode.convertTypeName(tn,bad,_gvn);
      rez = _e.add_fun(bad,tvar,epi1); // Return type-name constructor
      // For Structs, add a second constructor taking an expanded arg list
      if( t instanceof TypeStruct ) {   // Add struct types with expanded arg lists
        FunPtrNode epi2 = IntrinsicNode.convertTypeNameStruct(tn, _gvn);
        Node rez2 = _e.add_fun(bad,tvar,epi2); // type-name constructor with expanded arg list
        _gvn.init0(rez2._uses.at(0));      // Force init of Unresolved
      }
    }
    _gvn.rereg(stk,stk.value(_gvn)); // Re-install closure in GVN
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
  private Node stmt() {
    if( peek('^') ) {           // Early function exit
      Node ifex = ifex();
      return ifex == null ? err_ctrl2("Missing term after ^") : _e.early_exit(this,ifex);
    }

    // Gather ids in x = y = z = ....
    Ary<String> toks = new Ary<>(new String[1],0);
    Ary<Type  > ts   = new Ary<>(new Type  [1],0);
    BitSet rs = new BitSet();
    while( true ) {
      int oldx = _x;
      String tok = token();     // Scan for 'id = ...'
      if( tok == null ) break;  // Out of ids
      int oldx2 = _x;
      Type t = null;
      // x  =: ... type  assignment, handled before we get here
      // x  =  ... final assignment
      // x :=  ... var   assignment
      // x : type  = ... typed final assignment
      // x : type := ... typed var   assignment
      // x : nontype = ... error, missing type
      // p? x : nontype ... part of trinary
      if( peek(":=") ) _x=oldx2; // Avoid confusion with typed assignment test
      else if( peek(':') && (t=type())==null ) { // Check for typed assignment
        if( _e._scope.test_if() ) _x = oldx2; // Grammar ambiguity, resolve p?a:b from a:int
        else                      err_ctrl0("Missing type after ':'");
      }
      if( peek(":=") ) rs.set(toks._len);             // Re-assignment parse
      else if( !peek('=') ) { _x = oldx; break; } // Unwind token parse, and not assignment
      toks.add(tok.intern());
      ts  .add(t  );
    }

    // Normal statement value parse
    Node ifex = ifex();         // Parse an expression for the statement value
    if( ifex == null ) {        // No statement?
      if( toks._len == 0 ) return  null;
      ifex = err_ctrl2("Missing ifex after assignment of '"+toks.last()+"'");
    }
    // Honor all type requests, all at once, by inserting type checks on the ifex.
    for( Type t : ts )
      ifex = typechk(ifex,t,null);
    // Assign tokens to value
    for( int i=0; i<toks._len; i++ ) {
      String tok = toks.at(i);               // Token being assigned
      byte mutable = ts_mutable(rs.get(i));  // Assignment is mutable or final
      ScopeNode scope = lookup_scope(tok);   // Prior scope of token
      if( scope==null ) {                    // Token not already bound at any scope
        if( ifex instanceof FunPtrNode && !ifex.is_forward_ref() )
          ((FunPtrNode)ifex).fun().bind(tok); // Debug only: give name to function
        create(tok,con(Type.NIL),ts_mutable(true)); // Create at top of scope as nil.
        scope = _e._scope;              // Scope is the current one
        scope.def_if(tok,mutable,true); // Record if inside arm of if (partial def error check)
      }
      // Handle re-assignments and forward referenced function definitions.
      Node n = scope.stk().get(tok); // Get prior direct binding
      if( n.is_forward_ref() ) { // Prior is actually a forward-ref, so this is the def
        assert !scope.stk().is_mutable(tok) && scope == _e._scope;
        ((FunPtrNode)n).merge_ref_def(_gvn,tok,(FunPtrNode)ifex);
      } else { // Store into scope/NewObjNode/closure
        // Active (parser) memory state
        MemMergeNode mmem = mem_active();
        int alias = scope.stk()._alias; // Alias for scope
        Node omem = mmem.active_obj(alias);
        Node st = gvn(new StoreNode(ctrl(),omem,scope.ptr(),ifex,mutable,tok,errMsg()));
        int idx = mmem.make_alias2idx(alias); // Precise alias update
        mmem.set_def(idx,st,_gvn);
        scope.def_if(tok,mutable,false); // Note 1-side-of-if update
      }
    }
    return ifex;
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
    Node old_mem = all_mem().keep();      // Keep until parse false-side
    Node tex = stmt();                    // Parse true expression
    if( tex == null ) tex = err_ctrl2("missing expr after '?'");
    tex.keep();                    // Keep until merge point
    Node t_ctrl= ctrl().keep();    // Keep until merge point
    Node t_mem = all_mem().keep(); // Keep until merge point

    _e._scope.flip_if();        // Flip side of tracking new defs
    set_ctrl(gvn(new CProjNode(ifex.unhook(),0))); // Control for false branch
    set_mem(old_mem);           // Reset memory to before the IF
    Node fex = peek(':') ? stmt() : con(Type.NIL);
    if( fex == null ) fex = err_ctrl2("missing expr after ':'");
    fex.keep();                    // Keep until merge point
    Node f_ctrl= ctrl().keep();    // Keep until merge point
    Node f_mem = all_mem().keep(); // Keep until merge point
    old_mem.unkeep(_gvn);

    Parse bad = errMsg();
    t_mem = _e._scope.check_if(true ,bad,_gvn,t_ctrl,_e._scope.ptr(),t_mem); // Insert errors if created only 1 side
    f_mem = _e._scope.check_if(false,bad,_gvn,f_ctrl,_e._scope.ptr(),f_mem); // Insert errors if created only 1 side
    _e._scope.pop_if();         // Pop the if-scope
    RegionNode r = set_ctrl(init(new RegionNode(null,t_ctrl.unhook(),f_ctrl.unhook())).keep());
    set_mem(gvn(new PhiNode(bad,r       ,t_mem.unhook(),f_mem.unhook())));
    return  gvn(new PhiNode(bad,r.unhook(),tex.unhook(),  fex.unhook())) ; // Ifex result
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
      unifun = _e.lookup_filter(uni,_gvn,1); // UniOp, or null
      if( unifun==null || unifun.op_prec() == -1 ) { unifun=null; _x=oldx; } // Not a uniop
    }

    // [unifun] term [binop term]*
    Node term = term();
    if( term == null ) return unifun; // Term is required, so missing term implies not any expr
    // Collect 1st fcn/arg pair
    Ary<Node> funs = new Ary<>(new Node[1],0);
    try( TmpNode args = new TmpNode() ) {
      funs.add(unifun==null ? null : unifun.keep());
      args.add_def(term);

      // Now loop for binop/term pairs: parse Kleene star of [binop term]
      while( true ) {
        oldx = _x;
        String bin = token();
        if( bin==null ) break;    // Valid parse, but no more Kleene star
        Node binfun = _e.lookup_filter(bin,_gvn,2); // BinOp, or null
        if( binfun==null ) { _x=oldx; break; } // Not a binop, no more Kleene star
        term = term();
        if( term == null ) term = err_ctrl2("missing expr after binary op "+bin);
        funs.add(binfun.keep());  args.add_def(term);
      }

      // Have a list of interspersed operators and terms.
      // Build a tree with precedence.
      int max=-1;                 // First find max precedence.
      for( Node n : funs ) if( n != null ) max = Math.max(max,n.op_prec());
      // Now starting at max working down, group list by pairs into a tree
      while( max >= 0 && args._defs._len > 0 ) {
        for( int i=0; i<funs.len(); i++ ) { // For all ops of this precedence level, left-to-right
          Node fun = funs.at(i);
          if( fun==null ) continue;
          assert fun.op_prec() <= max;
          if( fun.op_prec() < max ) continue; // Not yet
          if( i==0 ) {
            Node call = do_call(new CallNode(true,errMsg(),ctrl(),fun.unhook(),all_mem(),args.in(0)));
            args.set_def(0,call,_gvn);
            funs.setX(0,null);
          } else {
            Node call = do_call(new CallNode(true,errMsg(),ctrl(),fun.unhook(),all_mem(),args.in(i-1),args.in(i)));
            args.set_def(i-1,call,_gvn);
            funs.remove(i);  args.remove(i);  i--;
          }
        }
        max--;
      }
      return args.del(0);       // Return the remaining expression
    }
  }

  /** Parse a term, either an optional application or a field lookup
   *    term = id++ | id--
   *    term = tfact [tuple | tfact | .field | .field[:]=stmt]* // application (includes uniop) or field (and tuple) lookup
   *  An alternative expression of the same grammar is:
   *    term = tfact post
   *    post = empty | (tuple) post | tfact post | .field post
   *  Also, field assignments are:
   *    post = .field [:]= stmt
   */
  private Node term() {
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
        String fld = token();   // Field name
        if( fld == null ) {     // Not a token, check for a field number
          int fldnum = field_number();
          if( fldnum == -1 ) return err_ctrl2("Missing field name after '.'");
          fld = ""+fldnum;      // Convert to a field name
        }
        fld=fld.intern();

        Node castnn = gvn(new CastNode(ctrl(),n,TypeMemPtr.OOP)); // Remove nil choice
        Node mem = all_mem();

        // Store or load against memory
        if( peek(":=") || peek_not('=','=')) {
          byte fin = _buf[_x-2]==':' ? TypeStruct.frw() : TypeStruct.ffinal();
          Node stmt = stmt();
          if( stmt == null ) n = err_ctrl2("Missing stmt after assigning field '."+fld+"'");
          else {
            Node st = gvn(new StoreNode(ctrl(),mem,castnn,n=stmt,fin,fld ,errMsg()));
            mem_active().st((StoreNode)st,_gvn);
          }
        } else {
          n = gvn(new LoadNode(mem,castnn,fld,errMsg()));
        }

      } else {                  // Attempt a function-call
        boolean arglist = peek('(');
        oldx = _x;
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
          n = err_ctrl2("A function is being called, but "+tn+" is not a function");
        } else {
          n = do_call(new CallNode(!arglist,errMsg(),ctrl(),n,all_mem(),arg)); // Pass the 1 arg
        }
      }
    } // Else no trailing arg, just return value
    return n;                   // No more terms
  }

  // Handle post-increment/post-decrement operator
  private Node inc(String tok, int d) {
    ScopeNode scope = lookup_scope(tok=tok.intern()); // Find prior scope of token
    // Need a load/call/store sensible options
    Node n;
    if( scope==null ) {         // Token not already bound to a value
      create(tok,n = con(Type.NIL),ts_mutable(true));
      scope = _e._scope;
    } else {                    // Check existing token for mutable
      if( !scope.is_mutable(tok) )
        return err_ctrl2("Cannot re-assign final val '"+tok+"'");
    }
    // Now properly load from the closure
    MemMergeNode mmem = mem_active(scope); // Active memory for the chosen scope
    int alias = scope.stk()._alias;        // Closure alias
    n = gvn(new LoadNode(mmem.active_obj(alias),scope.ptr(),tok,null));
    if( n.is_forward_ref() )    // Prior is actually a forward-ref
      return err_ctrl2(forward_ref_err(((FunPtrNode)n).fun()));
    // Do a full lookup on "+", and execute the function
    Node plus = _e.lookup_filter("+",_gvn,2);
    Node sum = do_call(new CallNode(true,errMsg(),ctrl(),plus,all_mem(),n.keep(),con(TypeInt.con(d))));

    MemMergeNode mmem2 = mem_active(scope); // Active memory for the chosen scope, after the call to plus
    Node st = gvn(new StoreNode(ctrl(),mmem.active_obj(alias),scope.ptr(),sum,TypeStruct.frw(),tok,errMsg()));
    int idx = mmem2.make_alias2idx(alias); // Precise alias update
    mmem2.set_def(idx,st,_gvn);
    return n.unhook();          // Return pre-increment value
  }

  /** Parse an optionally typed factor
   *  tfact = fact[:type]
   */
  private Node tfact() {
    Node fact = fact();
    if( fact==null ) return null;
    int oldx = _x;
    if( !peek(':') ) { _x = oldx; return fact; }
    Type t = type();
    if( t==null ) { _x = oldx; return fact; } // No error for missing type, because can be ?: instead
    return typechk(fact,t,null);
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
      return str==null ? err_ctrl1("Unterminated string",TypeStr.XSTR) : str;
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
      if( peek('}') && op != null && op.op_prec() > 0 ) {
        // If a primitive unresolved, clone to give a proper error message.
        if( op instanceof UnresolvedNode )
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
    if( tok == null || tok.equals("=") || tok.equals("^"))
      { _x = oldx; return null; } // Disallow '=' as a fact, too easy to make mistakes
    ScopeNode scope = lookup_scope(tok);
    if( scope == null ) { // Assume any unknown ref is a forward-ref of a recursive function
      Node fref = gvn(FunPtrNode.forward_ref(_gvn,tok,this));
      // Place in nearest enclosing closure, NOT as a field in a struct.
      _e.lookup_closure().stk().create(tok.intern(),fref,TypeStruct.ffinal(),_gvn);
      return fref;
    }
    Node def = scope.get(tok);    // Get top-level value; only sane if no stores allowed to modify it
    // Disallow uniop and binop functions as factors.
    if( def.op_prec() > 0 ) { _x = oldx; return null; }
    // Forward refs always directly assigned into scope
    if( def.is_forward_ref() ) return def;
    // Else must load against most recent closure update.
    MemMergeNode mmem = mem_active(scope); // Active memory for the chosen scope
    return gvn(new LoadNode(mmem.active_obj(scope.stk()._alias),scope.ptr(),tok.intern(),null));
  }

  /** Parse a tuple; first stmt but not the ',' parsed.
   *  tuple= (stmts,[stmts,])     // Tuple; final comma is optional
   */
  private Node tuple(Node s) {
    NewObjNode nn = new NewObjNode(false,ctrl());
    int fidx=0;
    while( s!=null ) {
      nn.create_active((""+(fidx++)).intern(),s,TypeStruct.ffinal(),_gvn);
      if( !peek(',') ) break;   // Final comma is optional
      s=stmts();
    }
    require(')');
    // NewNode updates merges the new allocation into all-of-memory and returns
    // a reference.
    Node nnn = gvn(nn);
    Node ptr = gvn(new  ProjNode(nnn,1));
    Node mem = gvn(new OProjNode(nnn,0));
    mem_active().create_alias_active(nn._alias,mem,_gvn);
    return ptr;
  }

  /** Parse an anonymous function; the opening '{' already parsed.  After the
   *  '{' comes an optional list of arguments and a '->' token, and then any
   *  number of statements separated by ';'.
   *  func = { [[id]* ->]? stmts }
   */
  private static final byte args_are_mutable=ts_mutable(false); // Args mutable or r/only by default
  private Node func() {
    int oldx = _x;
    Ary<String> ids = new Ary<>(new String[1],0);
    Ary<Type  > ts  = new Ary<>(new Type  [1],0);
    Ary<Parse > bads= new Ary<>(new Parse [1],0);

    while( true ) {
      String tok = token();
      if( tok == null ) { ids.clear(); ts.clear(); _x=oldx; break; } // not a "[id]* ->"
      if( tok.equals("->") ) break;
      Type t = Type.SCALAR;    // Untyped, most generic type
      Parse bad = errMsg();    // Capture location in case of type error
      if( peek(':') )          // Has type annotation?
        if( (t=type())==null ) {
          err_ctrl0("Missing or bad type arg");
          t = Type.SCALAR;
          skipNonWS();         // Skip possible type sig, looking for next arg
        }
      ids .add(tok.intern());
      ts  .add(t  );
      bads.add(bad);
    }
    Node old_ctrl = ctrl();
    Node old_mem  = all_mem().keep();
    FunNode fun = init(new FunNode(ts.asAry()).add_def(Env.ALL_CTRL)).keep();
    try( Env e = new Env(_e,true) ) {// Nest an environment for the local vars
      _e = e;                   // Push nested environment
      _gvn.set_def_reg(e._scope.stk(),0,fun); // Closure creation control defaults to function entry
      set_ctrl(fun);            // New control is function head
      Node rpc = gvn(new ParmNode(-1,"rpc",fun,con(TypeRPC.ALL_CALL),null)).keep();
      Node mem = gvn(new ParmNode(-2,"mem",fun,con(TypeMem.MEM),null));
      Parse errmsg = errMsg();  // Lazy error message
      int cnt=0;                // Add parameters to local environment
      for( int i=0; i<ids._len; i++ ) {
        Node parm = gvn(new ParmNode(cnt++,ids.at(i),fun,con(Type.SCALAR),errmsg));
        Node mt = typechk(parm,ts.at(i),mem);
        create(ids.at(i),mt, args_are_mutable);
      }
      // Function memory is a merge of incoming wide memory, and the local
      // closure implied by arguments.  Starts merging in parent scope, but
      // this is incorrect - should start from the incoming function memory.
      MemMergeNode amem = mem_active();
      assert amem.in(1).in(0) == e._scope.stk(); // amem slot#1 is the closure
      amem.set_def(0,mem,_gvn);                  // amem slot#0 was outer closure, should be function memory
      // Parse function body
      Node rez = stmts();       // Parse function body
      if( rez == null ) rez = err_ctrl2("Missing function body");
      require('}');             //
      // Merge normal exit into all early-exit paths
      if( e._scope.is_closure() ) rez = merge_exits(rez);
      RetNode ret = (RetNode)gvn(new RetNode(ctrl(),all_mem(),rez,rpc.unhook(),fun.unhook()));
      Node fptr = gvn(new FunPtrNode(ret));
      _e = _e._par;             // Pop nested environment
      set_ctrl(old_ctrl);       // Back to the pre-function-def control
      set_mem (old_mem.unhook());// Back to the pre-function-def memory
      return fptr;              // Return function; close-out and DCE 'e'
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
    mem.set_def(0,ctrl,null);
    val.set_def(0,ctrl,null);
    set_mem (gvn(mem.add_def(all_mem())));
    return   gvn(val.add_def(rez.unhook())) ;
  }

  // Merge this early exit path into all early exit paths being recorded in the
  // current Env/Scope.
  Node do_exit( ScopeNode s, Node rez ) {
    Node ctrl = s.early_ctrl();
    Node mem  = s.early_mem ();
    Node val  = s.early_val ();
    if( ctrl == null ) {
      s.set_def(3,ctrl=new RegionNode(  (Node)null),null);
      s.set_def(4,mem =new PhiNode(null,(Node)null),null);
      s.set_def(5,val =new PhiNode(null,(Node)null),null);
    }
    ctrl.add_def(ctrl());
    mem .add_def(all_mem());
    val .add_def(rez   );
    set_ctrl(con(Type.XCTRL  ));
    set_mem (con(TypeMem.XMEM));
    return   con(Type.NIL    ) ;
  }

  /** Parse anonymous struct; the opening "@{" already parsed.  A lexical scope
   *  is made and new variables are defined here.  Next comes statements, with
   *  each assigned value becoming a struct member, then the closing "}".
   *  \@{ stmts }
   */
  private Node struct() {
    Node ptr;
    all_mem();
    try( Env e = new Env(_e,false) ) {// Nest an environment for the local vars
      _e = e;                   // Push nested environment
      stmts();                  // Create local vars-as-fields
      require('}');
      assert ctrl() != e._scope;
      e._par._scope.set_ctrl(ctrl(),_gvn); // Carry any control changes back to outer scope
      e._par._scope.set_mem(all_mem(),_gvn); // Carry any memory changes back to outer scope
      _e = e._par;                         // Pop nested environment
      ptr = e._scope.ptr().keep();         // A pointer to the constructed object
    } // Pop lexical scope around struct
    return ptr.unhook();
  }

  // Add a typecheck into the graph, with a shortcut if trivially ok.
  private Node typechk(Node x, Type t, Node mem) {
    return t == null || _gvn.type(x).isa(t) ? x : gvn(new TypeNode(t,x,errMsg()));
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
    if( n instanceof Long   ) return n.longValue()==0 ? Type.NIL : TypeInt.con(n.  longValue());
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
    NewNode nnn = (NewNode)gvn( new NewStrNode(ts,ctrl(),con(ts)));
    Node ptr = gvn( new  ProjNode(nnn,1));
    Node mem = gvn( new OProjNode(nnn,0));
    mem_active().create_alias_active(nnn._alias,mem,_gvn);
    return ptr;
  }

  /** Parse a type or return null
   *  type = tcon | tfun | tstruct | ttuple | tvar  // Type choices
   *  tcon = int, int[1,8,16,32,64], flt, flt[32,64], real, str[?]
   *  tfun = {[[type]* ->]? type } // Function types mirror func decls
   *  tmod = = | := | ==  // '=' is r/only, ':=' is r/w, '==' is final
   *  tstruct = @{ [id [tmod [type?]];]*}  // Struct types are field names with optional types.  Spaces not allowed
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
    if( t==null ) return null;
    Type base = t.base();
    if( !(base instanceof TypeObj) ) return t;
    // Automatically convert to reference for fields.
    // Make a reasonably precise alias.
    int type_alias = BitsAlias.type_alias(base instanceof TypeStruct ? BitsAlias.REC : BitsAlias.ARY,(TypeObj)t);
    TypeMemPtr tmp = TypeMemPtr.make(type_alias);
    return typeq(tmp);          // And check for null-ness
  }
  // Wrap in a nullable if there is a trailing '?'.  No spaces allowed
  private Type typeq(Type t) { return peek_noWS('?') ? t.meet_nil() : t; }

  // No mod is r/o, the default and lattice bottom.  ':' is read-write, '=' is
  // final.  Currently '-' is ambiguous with function arrow ->.
  private byte tmod() {
    if( peek("==") ) { _x--; return TypeStruct.ffinal(); } // final     , leaving trailing '='
    if( peek(":=") ) { _x--; return TypeStruct.frw();    } // read-write, leaving trailing '='
    return tmod_default();
  }
  // Experimenting, would like to default to most unconstrained type: r/w.  But
  // r/o is the lattice bottom, and defaulting to r/w means the default cannot
  // accept final-fields.  Using lattice bottom for the default.
  private byte tmod_default() { return TypeStruct.fro(); }

  // Type or null or TypeErr.ANY for '->' token
  private Type type0(boolean type_var) {
    if( peek('{') ) {           // Function type
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
      TypeStruct targs = TypeStruct.make(ts.asAry());
      if( !peek('}') ) return null;
      return typeq(TypeFunPtr.make(BitsFun.NZERO,targs,ret));
    }

    if( peek("@{") ) {          // Struct type
      Ary<String> flds = new Ary<>(new String[1],0);
      Ary<Type  > ts   = new Ary<>(new Type  [1],0);
      Ary<Byte  > mods = new Ary<>(new Byte  [1],0);
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
      return peek('}') ? TypeStruct.make(flds.asAry(),ts.asAry(),finals) : null;
    }

    // "()" is the zero-entry tuple
    // "(   ,)" is a 1-entry tuple
    // "(int )" is a 1-entry tuple (optional trailing comma)
    // "(int,)" is a 1-entry tuple (optional trailing comma)
    // "(,int)" is a 2-entry tuple
    // "(, , )" is a 2-entry tuple
    if( peek('(') ) { // Tuple type
      byte c;
      Ary<Type> ts = new Ary<>(new Type[1],0);
      while( (c=skipWS()) != ')' ) { // No more types...
        Type t = Type.SCALAR;    // Untyped, most generic field type
        if( c!=',' &&            // Has type annotation?
            (t=typep(type_var)) == null) // Parse type, wrap ptrs
          return null;                   // not a type
        ts.add(t);
        if( !peek(',') ) break; // Final comma is optional
      }
      return peek(')') ? TypeStruct.make_tuple(ts.asAry()) : null;
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
      _e.add_type(tok,t=TypeName.make_forward_def_type(tok));
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
  private static boolean isOp0   (byte c) { return "!#$%*+,-.=<>@^[]~/&".indexOf(c) != -1; }
  private static boolean isOp1   (byte c) { return isOp0(c) || ":?".indexOf(c) != -1; }
  public  static boolean isDigit (byte c) { return '0' <= c && c <= '9'; }

  // Utilities to shorten code for common cases
  public Node gvn (Node n) { return n==null ? null : _gvn.xform(n); }
  private <N extends Node> N init( N n ) { return n==null ? null : _gvn.init(n); }
  private void kill( Node n ) { if( n._uses._len==0 ) _gvn.kill(n); }
  public Node ctrl() { return _e._scope.ctrl(); }
  // Set and return a new control
  private <N extends Node> N set_ctrl(N n) { return _e._scope.set_ctrl(n,_gvn); }
  private Node set_mem(Node n) { return _e._scope.set_mem(n,_gvn); }

  private @NotNull ConNode con( Type t ) { return _gvn.con(t); }

  // Lookup & extend scopes
  public  Node lookup( String tok ) { return _e.lookup(tok); }
  private ScopeNode lookup_scope( String tok ) { return _e.lookup_scope(tok); }
  public  ScopeNode scope( ) { return _e._scope; }
  private void create( String tok, Node n, byte mutable ) { _e._scope.stk().create(tok,n,mutable,_gvn ); }
  private static byte ts_mutable(boolean mutable) { return mutable ? TypeStruct.frw() : TypeStruct.ffinal(); }

  // Close off active memory and return it.
  private Node all_mem() { return _e._scope.all_mem(_gvn); }
  // Expand default memory to support precise aliasing: an active MemMerge (not in GVN)
  private MemMergeNode mem_active() { return mem_active(_e._scope); }
  private MemMergeNode mem_active(ScopeNode scope) {
    Node mem = scope.mem();
    if( _gvn.touched(mem) ) {
      // If only used by the parser, just make it active.
      if( mem instanceof MemMergeNode && mem._uses._len==1 && mem._keep == 0 ) _gvn.unreg(mem);
      // Not active and has uses, so make a new active memory feeding from the old
      else return scope.set_active_mem(new MemMergeNode(mem),_gvn);
    }
    return (MemMergeNode)mem;
  }

  // Insert a call, with projections
  private Node do_call( CallNode call0 ) {
    Node call = gvn(call0.keep());
    Node callepi = gvn(new CallEpiNode(call.unhook())).keep();
    set_ctrl(  gvn(new CProjNode(callepi,0)));
    set_mem (  gvn(new MProjNode(callepi,1)));
    return     gvn(new  ProjNode(callepi.unhook(),2));
  }

  // Whack current control with a syntax error
  private ErrNode err_ctrl2( String s ) { return err_ctrl1(s,Type.SCALAR); }
  private ErrNode err_ctrl1( String s, Type t ) { return init(new ErrNode(Env.START,errMsg(s),t)); }
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
    String s = t0.is_forward_ref() ? ((TypeFunPtr)t0).names() : t0.toString();
    return errMsg(s+" is not a "+t1);
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
