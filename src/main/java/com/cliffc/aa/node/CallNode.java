package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;

// Call/apply node.
//
// Control is not required for an apply but inlining the function body will
// require it; slot 0 is for Control.  Slot 1 is a function value - a Node
// typed as a TypeFunPtr; can be an Epilog, an Unresolved, or e.g. a Phi or a
// Load.  Slot 2 is for memory.  Slots 3+ are for other args.
//
// When the function simplifies to a single TypeFunPtr, the Call can inline.
//
// The Call-graph is lazily discovered during GCP/opto.  Before then all
// functions are kept alive with a special control (see FunNode), and all Calls
// are assumed to call all functions... unless their fun() input is a trival
// function constant.
//
// As the Call-graph is discovered, Calls are "wired" to make it explicit: the
// Call control is wired to the FunNode/Region; call args are wired directly to
// function ParmNodes/PhiNode; the CallEpi is wired to the function RetNode.
// After GCP/opto the call-graph is explicit and fairly precise.  The call-site
// index is just like a ReturnPC value on a real machine; it dictates which of
// several possible returns apply... and can be merged like a PhiNode.
//
// ASCIIGram: Vertical   lines are part of the original graph.
//            Horizontal lines are lazily wired during GCP.
//
// TFP&Math
//    |  arg0 arg1
//    \  |   /           Other Calls
//     | |  /             /  |  \
//     v v v             /   |   \
//      Call            /    |    \
//        +--------->------>------>             Wired during GCP
//                 FUN0   FUN1   FUN2
//                 +--+   +--+   +--+
//                 |  |   |  |   |  |
//                 |  |   |  |   |  |
//                 +--+   +--+   +--+
//            /-----Ret<---Ret<---Ret--\        Wired during GCP
//     CallEpi     Epi    Epi    Epi    Other
//      CProj         \    |    /       CallEpis
//      MProj          \   |   /
//      DProj           TFP&Math


public class CallNode extends Node {
  int _rpc;                 // Call-site return PC
  private boolean _unpacked;// Call site allows unpacking a tuple (once)
  private boolean _inlined; // Inlining a call-site is a 2-stage process; function return wired to the call return
  Parse  _badargs;          // Error for e.g. wrong arg counts or incompatible args
  public CallNode( boolean unpacked, Parse badargs, Node... defs ) {
    super(OP_CALL,defs);
    _rpc = BitsRPC.new_rpc(BitsRPC.ALL); // Unique call-site index
    _unpacked=unpacked;         // Arguments are typically packed into a tuple and need unpacking, but not always
    _badargs = badargs;
  }

  String xstr() { return (_inlined ? "_c" : "C")+"all#"+_rpc; } // Self short name
  String  str() { return xstr(); }       // Inline short name

  // Inline the CallNode
  private Node inline( GVNGCM gvn, Node ctrl, Node mem, Node rez ) {
    rez.add_def(rez);
    mem.add_def(mem);
    set_def(0,ctrl,gvn);        // New control is function epilog control; CProj._idx=0
    set_def(1,mem ,gvn);        // New memory  is function epilog memory ; MProj._idx=1
    set_def(2,rez ,gvn);        // New result  is function epilog result ; DProj._idx=2
    rez.pop();  mem.pop();
    _inlined = true;
    return this;
  }
  // Called by projections when folding away the call
  @Override public Node is_copy(GVNGCM gvn, int idx) { return _inlined ? in(idx) : null; }

  // Number of actual arguments
  private int nargs() { return _defs._len-3; }
  // Actual arguments.
  Node arg( int x ) { return _defs.at(x+3); }
  private void set_arg(int idx, Node arg, GVNGCM gvn) { set_def(idx+3,arg,gvn); }

  private Node ctl() { return in(0); }
  public  Node fun() { return in(1); }
  private Node mem() { return in(2); }
  private void set_ctl    (Node ctl, GVNGCM gvn) {     set_def    (0,ctl,gvn); }
  private void set_fun    (Node fun, GVNGCM gvn) {     set_def    (1,fun,gvn); }
  public  void set_fun_reg(Node fun, GVNGCM gvn) { gvn.set_def_reg(this,1,fun); }
  public BitsFun fidxs(GVNGCM gvn) {
    Type tf = gvn.type(fun());
    return tf instanceof TypeFunPtr ? ((TypeFunPtr)tf).fidxs() : null;
  }
  public CallEpiNode callepi() {
    assert _uses._len==1;
    return (CallEpiNode)_uses.at(0);
  }

  // Clones during inlining all become unique new call sites
  @Override CallNode copy(GVNGCM gvn) {
    CallNode call = (CallNode)super.copy(gvn);
    call._rpc = BitsRPC.new_rpc(_rpc); // Children RPC
    return call;
  }

  @Override public Node ideal(GVNGCM gvn) {
    // If an inline is in-progress, no other opts and this node will go dead
    if( _inlined ) return null;
    // Dead, do nothing
    if( gvn.type(ctl())==Type.XCTRL ) return null;

    // When do i do 'pattern matching'?  For the moment, right here: if not
    // already unpacked a tuple, and can see the NewNode, unpack it right now.
    if( !_unpacked ) { // Not yet unpacked a tuple
      assert nargs()==1;
      if( mem() instanceof MemMergeNode ) {
        NewNode nnn = ((MemMergeNode)mem()).exact(arg(0));
        if( nnn != null ) {
          remove(_defs._len-1,gvn); // Pop off the NewNode tuple
          int len = nnn._defs._len;
          for( int i=1; i<len; i++ ) // Push the args; unpacks the tuple
            add_def( nnn.in(i));
          gvn.add_work(mem());
          _unpacked = true;     // Only do it once
          return this;
        }
      }
      // Another version of structural unpacking: we can find a constant input tuple.
      Type tm = gvn.type(mem());
      Type tn = gvn.type(arg(0));
      if( tn instanceof TypeMemPtr && tm instanceof TypeMem ) {
        Type tx = ((TypeMem)tm).ld((TypeMemPtr)tn);
        if( tx instanceof TypeStruct && tx.is_con() ) {
          throw com.cliffc.aa.AA.unimpl(); // untested but probably correct
          //TypeStruct tt = (TypeStruct)tx;
          //int len = tt._ts.length;
          //remove(_defs._len-1,gvn);  // Pop off the ConNode tuple
          //for( int i=0; i<len; i++ ) // Push the args; unpacks the tuple
          //  add_def( gvn.con(tt.at(i)) );
          //_unpacked = true;     // Only do it once
          //return this;
        }
      }
    }

    Node unk  = fun();          // Function epilog/function pointer
    // If the function is unresolved, see if we can resolve it now
    if( unk instanceof UnresolvedNode ) {
      Node fun = resolve(gvn);
      if( fun != null ) { set_fun(fun,gvn); return this; }
    }
    
    // Unknown function(s) being called
    if( !(unk instanceof EpilogNode) )
      return null;
    // From here on down we know the exact function being called
    EpilogNode epi = (EpilogNode)unk;
    RetNode ret = epi.ret();
    Node ctrl = ret.ctl();
    Node mem  = ret.mem();
    Node rez  = ret.val();
    // This is due to a shortcut, where we do not modify the types of
    // primitives so they can be reused in tests.  Instead, the primitive is
    // "pure" and the memory is just a pass-through of the Call memory.
    if( gvn.type(mem) == TypeMem.XMEM ) mem = mem();
    // Function is single-caller (me) and collapsing
    if( epi.is_copy(gvn,0) != null ) {
      CallEpiNode cepi = callepi();
      assert cepi._defs._len==2; // [0] for the call, and [1] for the only return
      gvn.set_def_reg(cepi,1,null);  // Remove the CallEpi return path
      return inline(gvn, ctrl, mem, rez); // Rewire all function exits as the Call result
    }

    // Function is well-formed
    FunNode fun = epi.fun();
    if( fun.is_forward_ref() ) return null;

    // Arg counts must be compatible
    if( fun.nargs() != nargs() )
      return null;

    // Single choice; insert actual conversions as needed
    TypeTuple formals = fun._tf._args;
    for( int i=0; i<nargs(); i++ ) {
      if( fun.parm(i)==null )   // Argument is dead and can be dropped?
        set_arg(i,gvn.con(Type.XSCALAR),gvn); // Replace with some generic placeholder
      else {
        Type formal = formals.at(i);
        Type actual = gvn.type(arg(i));
        if( actual.isBitShape(formal) == 99 ) return null; // Requires user-specified conversion
      }
    }

    // If this is a forward-ref we have no body to inline
    if( epi.is_forward_ref() )
      return null;

    // Check for several trivial cases that can be fully inlined immediately.
    // Check for zero-op body (id function)
    if( rez instanceof ParmNode && rez.in(0) == fun && mem() == mem )
      return inline(gvn,ctl(),mem(),arg(((ParmNode)rez)._idx));
    // Check for constant body
    if( gvn.type(rez).is_con() && ctrl==fun )
      return inline(gvn,ctl(),mem(),rez);

    // Check for a 1-op body using only constants or parameters and no memory effects
    boolean can_inline=!(rez instanceof ParmNode) && mem==mem();
    for( Node parm : rez._defs )
      if( parm != null && parm != fun &&
          !(parm instanceof ParmNode && parm.in(0) == fun) &&
          !(parm instanceof ConNode) )
        can_inline=false;       // Not trivial
    if( can_inline ) {
      Node irez = rez.copy(gvn);// Copy the entire function body
      for( Node parm : rez._defs )
        irez.add_def((parm instanceof ParmNode && parm.in(0) == fun) ? arg(((ParmNode)parm)._idx) : parm);
      if( irez instanceof PrimNode ) ((PrimNode)irez)._badargs = _badargs;
      return inline(gvn,ctl(),mem(),gvn.xform(irez)); // New exciting replacement for inlined call
    }

    assert fun.in(1)._uid!=0; // Never wire into a primitive, just clone/inline it instead (done just above)
    assert fun.nargs() == nargs();

    // Always wire caller args into known functions
    return wire(gvn,fun);
  }

  // Wire the call args to a known function, letting the function have precise
  // knowledge of its callers and arguments.
  // TODO: Leaves the Call in the graph - making the graph "a little odd" - double
  // CTRL users - once for the call, and once for the function being called.
  Node wire( GVNGCM gvn, FunNode fun ) {
    if( _keep > 0 ) { gvn.add_work(this); return null; } // Do not wire before CallEpi is built in parser.
    
    Node ctrl = ctl();
    for( int i=1; i<fun._defs.len(); i++ )
      if( fun.in(i)==ctrl ) // Look for same control
        return null;        // Already wired up

    // Make sure we have enough args before wiring up (makes later life easier
    // to assume correct arg counts).  Note that we cannot, in general,
    // type-check the args during GCP, as they will start out too-high and pass
    // any isa-check.  Later, after wiring up in GCP they might fall to an
    // error state - so we have to support having error args coming in.
    for( Node arg : fun._uses )
      if( arg.in(0) == fun && arg instanceof ParmNode &&
          ((ParmNode)arg)._idx >= nargs() )
        return null;            // Wrong arg-count

    // Check for a sane setup
    assert gvn.touched(fun);
    CallEpiNode cepi = callepi();
    
    // Add an input path to all incoming arg ParmNodes from the Call.  Cannot
    // assert finding all args, because dead args may already be removed - and
    // so there's no Parm/Phi to attach the incoming arg to.
    for( Node arg : fun._uses ) {
      if( arg.in(0) == fun && arg instanceof ParmNode ) {
        int idx = ((ParmNode)arg)._idx; // Argument number, or -1 for rpc
        assert idx<nargs();
        Node actual = idx==-1 ? gvn.con(TypeRPC.make(_rpc)) : (idx==-2 ? mem() : arg(idx));
        gvn.add_def(arg,actual);
      }
    }
    // Add Control for this path.  Sometimes called from fun.Ideal() (because
    // inlining), sometimes called by Epilog when it discovers all callers
    // known.
    gvn.add_def(fun,ctrl);
    // Add the CallEpi hook
    gvn.add_def(cepi,fun.epi().ret());
    return this;
  }

  // Make real call edges from virtual call edges
  private void wire(GVNGCM gvn) {
    BitsFun fidxs = fidxs(gvn);     // Get all the propagated reaching functions
    if( fidxs.above_center() ) return;
    for( int fidx : fidxs ) {   // For all functions
      if( fidx >= FunNode.PRIM_CNT ) { // Do not wire up primitives, but forever take their default inputs and outputs
        // Can be wiring up the '#[ALL]' list.  Stop after seeing all existing functions
        if( fidx >= FunNode.FUNS._len ) return;
        FunNode fun = FunNode.find_fidx(fidx);
        if( !fun.is_dead() && !fun.is_forward_ref() ) wire(gvn,fun);
      }
    }
  }

  @Override public TypeTuple value(GVNGCM gvn) {
    Type tc = gvn.type(ctl());  // Control type
    if( _inlined )              // Inlined functions just pass thru & disappear
      return TypeTuple.make(tc,gvn.type(in(1)),gvn.type(in(2)));
    if( tc != Type.CTRL )       // Call is dead?
      return tc.above_center() ? TypeTuple.XCALL : TypeTuple.CALL;
    Node fp = fun();            // Function being called
    if( fp.is_forward_ref() )
      return TypeTuple.CALL;
    Type t = gvn.type(fp);
    if( Type.SCALAR.isa(t) ) // Calling something that MIGHT be a function, no idea what the result is
      return TypeTuple.CALL;
    if( !t.isa(TypeFunPtr.GENERIC_FUNPTR) ) // Calling something that MIGHT be a function, no idea what the result is
      return TypeTuple.CALL;

    if( gvn._opt ) // Manifesting optimistic virtual edges between caller and callee
      wire(gvn);   // Make real edges from virtual edges

    // See if we can reduce this to a single function (or unresolved).
    if( !(fp instanceof UnresolvedNode || fp instanceof EpilogNode) ) {
      BitsFun fidxs = fidxs(gvn);
      if( fidxs==null ) return gvn.type(fun()).above_center() ? TypeTuple.XCALL : TypeTuple.CALL;
      int fidx = fidxs.abit();
      if( fidx == -1 || fidx == BitsFun.ALL ) return TypeTuple.CALL;
      // During e.g. opto discover a single function target.  Use this for the
      // value1 calls.
      FunNode fun = FunNode.find_fidx(fidx);
      assert fun != null;
      fp = fun.epi();
    }
    
    if( fp instanceof EpilogNode )
      // Return {control,mem,value} tuple.
      return value1(gvn,(EpilogNode)fp); // Return type or SCALAR if invalid args

    TypeTuple trez = TypeTuple.CALL; // Base for JOIN
    // For unresolved, we can take the BEST choice; i.e. the JOIN of every choice.
    // Typically one choice works and the others report type errors on arguments.
    for( Node epi : fp._defs )
      trez = (TypeTuple)trez.join(value1(gvn,(EpilogNode)epi)); // JOIN of choices
    return trez;              // Return {control,mem,value} tuple.
  }

  // See if the arguments are valid.  If valid, return the function's return
  // type.  If not valid return SCALAR - as an indicator that the function
  // cannot be called, so the JOIN of valid returns is not lowered.
  private TypeTuple value1( GVNGCM gvn, EpilogNode epi ) {
    Type t = gvn.type(epi);
    if( !(t instanceof TypeFunPtr) ) // Might be any function, returning anything
      return t.above_center() ? TypeTuple.XCALL : TypeTuple.CALL;
    TypeTuple tret = (TypeTuple)gvn.type(epi.ret());
    Type    tctrl=tret.at(0);
    Type    tmem =tret.at(1), failmem;
    Type    tval =tret.at(2);
    if( tctrl == Type.XCTRL ) return TypeTuple.XCALL; // Function will never return
    if( tmem == TypeMem.XMEM ) // Primitives that never take memory?
      // This is due to a shortcut, where we do not modify the types of
      // primitives so they can be reused in tests.  Instead, the primitive is
      // "pure" and the memory is just a pass-through of the Call memory.
      failmem = tmem = gvn.type(mem());   // Use the call memory instead
    else
      failmem = TypeMem.MEM;
    assert tctrl==Type.CTRL;    // Function returns?
    FunNode fun = epi.fun();
    if( fun.is_forward_ref() ) return TypeTuple.make(tctrl,tmem,tval); // Forward refs do no argument checking

    if( fun.nargs() != nargs() ) return TypeTuple.make(Type.CTRL,failmem,Type.SCALAR); // Function not called, nothing to JOIN
    // Now do an arg-check
    TypeTuple formals = fun._tf._args; // Type of each argument
    for( int j=0; j<nargs(); j++ ) {
      Type actual = gvn.type(arg(j));
      Type formal = formals.at(j);
      if( !actual.isa(formal) ) // Actual is not a formal; call will not go thru
        return TypeTuple.make(Type.CTRL,failmem,Type.SCALAR);  // Argument not valid, nothing to JOIN
    }
    return TypeTuple.make(tctrl,tmem,tval);
  }

  // Given a list of actuals, apply them to each function choice.  If any
  // (!actual-isa-formal), then that function does not work and supplies an
  // ALL to the JOIN.  This is common for non-inlined calls where the unknown
  // arguments are approximated as SCALAR.  Lossless conversions are allowed as
  // part of a valid isa test.  As soon as some function returns something
  // other than ALL (because args apply), it supersedes other choices- which
  // can be dropped.

  // If more than one choice applies, then the choice with fewest costly
  // conversions are kept; if there is more than one then the join of them is
  // kept - and the program is not-yet type correct (ambiguous choices).
  public Node resolve( GVNGCM gvn ) {
    BitsFun fidxs = fidxs(gvn);
    if( fidxs == null ) return null; // Might be e.g. ~Scalar
    if( !fidxs.above_center() ) return null; // Sane as-is
    if( fidxs.test(BitsFun.ALL) ) return null;

    // Set of possible choices with fewest conversions
    class Data {
      private final int _xcvt, _fidx;
      private final boolean _unk;
      private final TypeTuple _formals;
      private Data( int x, boolean u, int f, TypeTuple ts ) { _xcvt = x; _unk=u; _fidx=f; _formals=ts; }
    }
    Ary<Data> ds = new Ary<>(new Data[0]);

    // For each function, see if the actual args isa the formal args.  If not,
    // toss it out.  Also count conversions, and keep the minimal conversion
    // function with all arguments known.
    outerloop:
    for( int fidx : fidxs ) {
      FunNode fun = FunNode.find_fidx(fidx);
      if( fun.nargs() != nargs() ) continue; // Wrong arg count, toss out
      TypeTuple formals = fun._tf._args;   // Type of each argument

      // Now check if the arguments are compatible at all, keeping lowest cost
      int xcvts = 0;             // Count of conversions required
      boolean unk = false;       // Unknown arg might be incompatible or free to convert
      for( int j=0; j<nargs(); j++ ) {
        Type actual = gvn.type(arg(j));
        //if( actual==Type.XSCALAR && arg(j) instanceof ConNode )
        //  continue; // Forced super-high arg is always compatible before formal is dead
        Type tx = actual.join(formals.at(j));
        if( tx != actual && tx.above_center() ) // Actual and formal have values in common?
          continue outerloop;   // No, this function will never work; e.g. cannot cast 1.2 as any integer
        byte cvt = actual.isBitShape(formals.at(j)); // +1 needs convert, 0 no-cost convert, -1 unknown, 99 never
        if( cvt == 99 )         // Happens if actual is e.g. TypeErr
          continue outerloop;   // No, this function will never work
        if( cvt == -1 ) unk = true; // Unknown yet
        else xcvts += cvt;          // Count conversions
      }

      Data d = new Data(xcvts,unk,fidx,formals);
      ds.push(d);
    }

    // Toss out choices with strictly more conversions than the minimal
    int min = 999;              // Required conversions
    for( Data d : ds )          // Find minimal conversions
      if( !d._unk && d._xcvt < min ) // If unknown, might need more converts
        min = d._xcvt;
    for( int i=0; i<ds._len; i++ ) // Toss out more expensive options
      if( ds.at(i)._xcvt > min )   // Including unknown... which might need more converts
        ds.del(i--);

    // If this set of formals is strictly less than a prior acceptable set,
    // replace the prior set.  Similarly, if strictly greater than a prior set,
    // toss this one out.
    for( int i=0; i<ds._len; i++ ) {
      if( ds.at(i)._unk ) continue;
      TypeTuple ifs = ds.at(i)._formals;
      for( int j=i+1; j<ds._len; j++ ) {
        if( ds.at(j)._unk ) continue;
        TypeTuple jfs = ds.at(j)._formals;
        if( ifs.isa(jfs) ) ds.del(j--); // Toss more expansive option j
        else if( jfs.isa(ifs) ) { ds.del(i--); break; } // Toss option i
      }
    }

    if( ds._len==0 ) return null;   // No choices apply?  No changes.
    if( ds._len==1 )                // Return the one choice
      return FunNode.find_fidx(ds.pop()._fidx).epi();
    if( ds._len==fun()._defs._len ) return null; // No improvement
    // TODO: return shrunk list
    //return gvn.xform(new UnresolvedNode(ns.asAry())); // return shrunk choice list
    return null;
  }

  @Override public String err(GVNGCM gvn) {
    assert !_inlined;           // Should have already cleaned out

    // Error#1: fail for passed-in unknown references
    for( int j=0; j<nargs(); j++ )
      if( arg(j).is_forward_ref() )
        return _badargs.forward_ref_err(((EpilogNode)arg(j)).fun());

    Node fp = fun();      // Either function pointer, or unresolved list of them
    Node xfp = fp instanceof UnresolvedNode ? fp.in(0) : fp;
    Type txfp = gvn.type(xfp);
    if( !(txfp instanceof TypeFunPtr) )
      return _badargs.errMsg("A function is being called, but "+txfp+" is not a function type");
    if( ((TypeFunPtr)txfp).fidxs().above_center() )
      return _badargs.errMsg("An ambiguous function is being called");

    assert xfp instanceof EpilogNode; // If not, then we failed to wire all callers up in opto
    EpilogNode epi = (EpilogNode)xfp;
    FunNode fun = epi.fun();
    if( fp.is_forward_ref() ) // Forward ref on incoming function
      return _badargs.forward_ref_err(fun);

    // Error#2: bad-arg-count
    if( fun.nargs() != nargs() )
      return _badargs.errMsg("Passing "+nargs()+" arguments to "+(fun.xstr())+" which takes "+fun.nargs()+" arguments");

    // Error#3: Now do an arg-check
    TypeTuple formals = fun._tf._args; // Type of each argument
    for( int j=0; j<nargs(); j++ ) {
      Type actual = gvn.type(arg(j));
      Type formal = formals.at(j);
      if( !actual.isa(formal) ) // Actual is not a formal
        return _badargs.typerr(actual,formal);
    }

    return null;
  }

  @Override public TypeTuple all_type() { return TypeTuple.make(Type.CTRL,TypeMem.MEM,Type.SCALAR); }
  @Override public int hashCode() { return super.hashCode()+_rpc; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof CallNode) ) return false;
    CallNode call = (CallNode)o;
    return _rpc==call._rpc;
  }

}

