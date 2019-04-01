package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.Bits;

// See FunNode.  Control is not required for an apply but inlining the function
// body will require it; slot 0 is for Control.  Slot 1 is a function value - a
// Node with a TypeFunPtr.  Slots 2+ are for args.
//
// When the function simplifies to a single TypeFunPtr, the Call can inline.
//
// Call-inlining can happen anytime we have a known function pointer, and
// might be several known function pointers - we are inlining the type analysis
// and not the execution code.  For this kind of inlining we replace the
// CallNode with a call-site specific Epilog, move all the CallNode args to
// the ParmNodes just like the Fun/Parm is a Region/Phi.  The call-site index
// is just like a ReturnPC value on a real machine; it dictates which of
// several possible returns apply... and can be merged like a PhiNode

public class CallNode extends Node {
  private static int RPC=1; // Call-site return PC
  int _rpc;         // Call-site return PC
  private boolean _unpacked;    // Call site allows unpacking a tuple (once)
  private boolean _inlined;     // Inlining a call-site is a 2-stage process; function return wired to the call return
  private Type   _cast_ret;     // Return type has been up-casted
  private Parse  _cast_P;       // Return type cast fail message
          Parse  _badargs;      // Error for e.g. wrong arg counts or incompatible args
  public CallNode( boolean unpacked, Parse badargs, Node... defs ) {
    super(OP_CALL,defs);
    _rpc = RPC++;               // Unique call-site index
    _unpacked=unpacked;         // Arguments are typically packed into a tuple and need unpacking, but not always
    _badargs = badargs;
  }

  String xstr() { return "Call#"+_rpc; } // Self short name
  String  str() { return xstr(); }       // Inline short name

  // Fast reset of parser state between calls to Exec
  private static int PRIM_RPC; // Primitives count of call-sites
  public static void init0() { PRIM_RPC=RPC; }
  public static void reset_to_init0() { RPC = PRIM_RPC; }

  // Inline the CallNode
  private Node inline( GVNGCM gvn, Node ctrl, Node mem, Node rez ) {
    set_def(0,ctrl,gvn);        // New control is function epilog control
    set_def(1,mem ,gvn);        // New memory  is function epilog memory
    set_def(2,rez ,gvn);        // New result  is function epilog result 
    _inlined = true;
    return this;
  }
  // Called by projections when folding away the call
  @Override public Node is_copy(GVNGCM gvn, int idx) { return _inlined ? in(idx) : null; }

  // Number of actual arguments
  private int nargs() { return _defs._len-3; }
  // Actual arguments.
  Node arg( int x ) { return _defs.at(x+3); }

  private Node ctl() { return in(0); }
  private Node mem() { return in(1); }
  public  Node fun() { return in(2); }
  private void set_fun(Node fun, GVNGCM gvn) { set_def(2,fun,gvn); }
  void set_fun_reg(Node fun, GVNGCM gvn) { gvn.set_def_reg(this,2,fun); }
  
  // Clones during inlining all become unique new call sites
  @Override CallNode copy() {
    CallNode call = super.copy();
    call._rpc = RPC++;
    return call;
  }
  
  @Override public Node ideal(GVNGCM gvn) {
    // If an inline is in-progress, no other opts and this node will go dead
    if( _inlined ) return null;
    // If an upcast is in-progress, no other opts until it finishes
    if( _cast_ret !=null ) return null;
    // Dead, do nothing
    if( gvn.type(ctl())==Type.XCTRL ) return null;

    // When do i do 'pattern matching'?  For the moment, right here: if not
    // already unpacked a tuple, and can see the NewNode, unpack it right now.
    if( !_unpacked ) { // Not yet unpacked a tuple
      assert nargs()==1;
      Node mem = mem();
      Type tn = gvn.type(arg(0));
      if( tn instanceof TypeMemPtr ) {
        Type tm = gvn.type(mem);
        if( tm instanceof TypeMem ) {
          Type tx = ((TypeMem)tm).ld((TypeMemPtr)tn);
          if( tx instanceof TypeStruct ) {
            TypeStruct tt = (TypeStruct)tx;
            // Either all the edges from a NewNode (for non-constants), or all
            // the constants types from a constant Tuple from a ConNode
            if( tt.is_con() ) {     // Allocation has constant-folded
              int len = tt._ts.length;
              pop();  gvn.add_work(mem); // Pop off the ConNode tuple
              for( int i=0; i<len; i++ ) // Push the args; unpacks the tuple
                add_def( gvn.con(tt.at(i)) );
            } else {                // Allocation exists, unpack args
              assert mem instanceof MergeMemNode && mem.in(1) instanceof MProjNode && mem.in(1).in(0) instanceof NewNode;
              Node nn = mem.in(1).in(0);
              int len = nn._defs._len;
              pop();  gvn.add_work(mem); // Pop off the NewNode/ConNode tuple
              for( int i=1; i<len; i++ ) // Push the args; unpacks the tuple
                add_def( nn.in(i));
            }
            _unpacked = true;       // Only do it once
            return this;
          }
        }
      }
    }

    // Type-checking a function; requires 2 steps, one now, one in the
    // following data Proj from the worklist.
    Node unk  = fun();          // Function epilog/function pointer
    if( unk instanceof TypeNode ) {
      TypeNode tn = (TypeNode)unk;
      TypeFun t_funptr = (TypeFun)tn._t;
      TypeFunPtr tf = t_funptr.fun();
      set_fun(tn.in(1),gvn);
      for( int i=0; i<nargs(); i++ ) // Insert casts for each parm
        set_def(i+3,gvn.xform(new TypeNode(tf._ts.at(i),arg(i),tn._error_parse)),gvn);
      _cast_ret = tf._ret;       // Upcast return results
      _cast_P = tn._error_parse; // Upcast failure message
      return this;
    }

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
    Node ctrl = epi.ctrl();
    Node mem  = epi.mem();
    Node rez  = epi.val();
    // Function is single-caller (me) and collapsing
    if( epi.is_copy(gvn,4) != null )
      return inline(gvn,ctrl,mem,rez);
    // Function is well-formed
    
    // Arg counts must be compatible
    FunNode fun = epi.fun();
    TypeFunPtr tfun = fun._tf;
    if( tfun.nargs() != nargs() )
      return null;

    // Single choice; insert actual conversions as needed
    TypeTuple formals = tfun._ts;
    for( int i=0; i<nargs(); i++ ) {
      if( fun.parm(i)==null )   // Argument is dead and can be dropped?
        set_def(i+3,gvn.con(Type.XSCALAR),gvn); // Replace with some generic placeholder
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
    if( rez instanceof ParmNode && rez.in(0) == fun ) return inline(gvn,ctl(),mem(),arg(((ParmNode)rez)._idx));
    // Check for constant body
    if( rez instanceof ConNode ) return inline(gvn,ctl(),mem(),rez);

    // Check for a 1-op body using only constants or parameters
    boolean can_inline=true;
    for( Node parm : rez._defs )
      if( parm != null && parm != fun &&
          !(parm instanceof ParmNode && parm.in(0) == fun) &&
          !(parm instanceof ConNode) )
        can_inline=false;       // Not trivial
    if( can_inline ) {
      Node irez = rez.copy();   // Copy the entire function body
      for( Node parm : rez._defs )
        irez.add_def((parm instanceof ParmNode && parm.in(0) == fun) ? arg(((ParmNode)parm)._idx) : parm);
      if( irez instanceof PrimNode ) ((PrimNode)irez)._badargs = _badargs;
      return inline(gvn,ctl(),mem,gvn.xform(irez)); // New exciting replacement for inlined call
    }

    assert fun.in(1)._uid!=0; // Never wire into a primitive, just clone/inline it instead (done just above)
    assert tfun.nargs() == nargs();

    // Always wire caller args into known functions
    return wire(gvn,fun,false);
  }

  // Wire the call args to a known function, letting the function have precise
  // knowledge of its callers and arguments.
  // Leaves the Call in the graph - making the graph "a little odd" - double
  // CTRL users - once for the call, and once for the function being called.
  Node wire(GVNGCM gvn, FunNode fun, boolean is_gcp) {
    Node ctrl = ctl();
    for( int i=1; i<fun._defs.len(); i++ )
      if( fun.in(i)==ctrl ) // Look for same control
        return null;        // Already wired up

    // Make sure we have enough args before wiring up (makes later life easier
    // to assume correct arg counts).  Note that we cannot, in general,
    // type-check the args during GCP, as they will start out too-high and pass
    // any isa-check.  Later, after wiring up in GCP they might fall to an
    // error state - so we have to support having error args coming in.
    for( Node arg : fun._uses ) {
      if( arg.in(0) == fun && arg instanceof ParmNode ) {
        int idx = ((ParmNode)arg)._idx; // Argument number, or -1 for rpc or -2 for memory
        if( idx >= nargs() ) return null; // Wrong arg-count
        if( is_gcp ) {
          Type formal = fun.targ(idx);
          Type actual = idx==-1 ? TypeRPC.make(_rpc) : (idx==-2 ? TypeMem.MEM : gvn.type(arg(idx)));
          if( !actual.isa(formal) )
            return null;     // Even if actual falls more, will never be formal
        }
      }
    }
    
    // Add an input path to all incoming arg ParmNodes from the Call.  Cannot
    // assert finding all args, because dead args may already be removed - and
    // so there's no Parm/Phi to attach the incoming arg to.
    for( Node arg : fun._uses ) {
      if( arg.in(0) == fun && arg instanceof ParmNode ) {
        int idx = ((ParmNode)arg)._idx; // Argument number, or -1 for rpc or -2 for memory
        assert idx<nargs();
        Node actual = idx==-1 ? gvn.con(TypeRPC.make(_rpc)) : (idx==-2 ? mem() : arg(idx));
        gvn.add_def(arg,actual);
      }
    }
    // Add Control for this path.  Sometimes called from fun.Ideal() (because
    // inlining), sometimes called by Epilog when it discovers all callers
    // known.
    assert gvn.touched(fun);
    gvn.add_def(fun,ctrl);
    return this;
  }

  // Make real call edges from virtual call edges
  private void wire(GVNGCM gvn, Type funptr) {
    if( !(funptr instanceof TypeFun) ) return; // Not fallen to a funptr yet
    TypeFun tfunptr = (TypeFun)funptr;
    TypeFunPtr tf = tfunptr.fun(); // Get type-propagated function list
    Bits fidxs = tf._fidxs;     // Get all the propagated reaching functions
    if( fidxs.above_center() ) return;
    for( int fidx : fidxs ) {   // For all functions
      if( fidx >= FunNode.PRIM_CNT ) { // Do not wire up primitives, but forever take their default inputs and outputs
        // Can be wiring up the '#[ALL]' list.  Stop after seeing all existing functions
        if( fidx >= FunNode.FUNS._len ) return;
        FunNode fun = FunNode.find_fidx(fidx);
        if( !fun.is_dead() && !fun.is_forward_ref() ) wire(gvn,fun,true);
      }
    }
  }
  
  @Override public Type value(GVNGCM gvn) {
    Type tc = gvn.type(ctl());  // Control type
    Type tm = gvn.type(mem());  // Memory type
    assert tm instanceof TypeMem;
    Node fp = fun();            // If inlined, its the result, if not inlined, its the function being called
    Type t = gvn.type(fp);      // If inlined, its the result, if not inlined, its the function being called
    if( _inlined )              // Inlined functions just pass thru & disappear
      return TypeTuple.make(tc,tm,t);
    if( tc == Type.XCTRL || tc == Type.ANY ) // Call is dead?
      return TypeTuple.make(Type.XCTRL,TypeMem.MEM.dual(),Type.XSCALAR);
    if( Type.SCALAR.isa(t) ) // Calling something that MIGHT be a function, no idea what the result is
      return TypeTuple.make(Type.CTRL,TypeMem.MEM,Type.SCALAR);

    if( gvn._opt ) // Manifesting optimistic virtual edges between caller and callee
      wire(gvn,t); // Make real edges from virtual edges
    
    Type trez = Type.ALL; // Base for JOIN
    if( fp instanceof UnresolvedNode ) {
      // For unresolved, we can take the BEST choice; i.e. the JOIN of every
      // choice.  Typically one choice works and the others report type
      // errors on arguments.
      for( Node epi : fp._defs )
        trez = trez.join(value1(gvn,gvn.type(epi))); // JOIN of choices
    } else {                                  // Single resolved target
      trez = value1(gvn,t);                   // Return type or SCALAR if invalid args
    }
    
    // Return {control,value} tuple.
    return TypeTuple.make(Type.CTRL,tm,trez);
  }

  // See if the arguments are valid.  If valid, return the function's return
  // type.  If not valid return SCALAR - as an indicator that the function
  // cannot be called, so the JOIN of valid returns is not lowered.
  private Type value1( GVNGCM gvn, Type t ) {
    if( !(t instanceof TypeFun) ) // Might be any function, returning anything
      return t.above_center() ? Type.XSCALAR : Type.SCALAR;
    TypeFun tepi = (TypeFun)t;
    Type    tctrl=tepi.ctl();
    Type    tval =tepi.val();
    TypeFunPtr tfun =tepi.fun();
    if( tctrl == Type.XCTRL ) return Type.XSCALAR; // Function will never return
    assert tctrl==Type.CTRL;      // Function will never return?
    if( t.is_forward_ref() ) return tfun.ret(); // Forward refs do no argument checking
    if( tfun.nargs() != nargs() ) return Type.SCALAR; // Function not called, nothing to JOIN
    // Now do an arg-check
    TypeTuple formals = tfun._ts; // Type of each argument
    for( int j=0; j<nargs(); j++ ) {
      Type actual = gvn.type(arg(j));
      Type formal = formals.at(j);
      if( !actual.isa(formal) ) // Actual is not a formal; accumulate type errors
        return Type.SCALAR;     // Argument not valid, nothing to JOIN
    }
    return tval;
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
    Type t = gvn.type(fun());
    if( !(t instanceof TypeFun) ) return null; // Might be e.g. ~Scalar
    TypeFun tfp = (TypeFun)t;
    if( !tfp.fun().is_ambiguous_fun() ) return null; // Sane as-is
    Bits fidxs = tfp.fun()._fidxs;

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
      TypeFunPtr fun = FunNode.find_fidx(fidx)._tf;
      if( fun.nargs() != nargs() ) continue; // Wrong arg count, toss out
      TypeTuple formals = fun._ts;   // Type of each argument
      
      // Now check if the arguments are compatible at all, keeping lowest cost
      int xcvts = 0;             // Count of conversions required
      boolean unk = false;       // Unknown arg might be incompatible or free to convert
      for( int j=0; j<nargs(); j++ ) {
        Type actual = gvn.type(arg(j));
        if( actual==Type.XSCALAR && arg(j) instanceof ConNode )
          continue; // Forced super-high arg is always compatible before formal is dead
        Type tx = actual.join(formals.at(j));
        if( tx.above_center() ) // Actual and formal have values in common?
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
        return _badargs.forward_ref_err((TypeFun)gvn.type(arg(j)));
    
    Node fp = fun();      // Either function pointer, or unresolve list of them
    Node xfp = fp instanceof UnresolvedNode ? fp.in(0) : fp;
    Type txfp = gvn.type(xfp);
    if( !(txfp instanceof TypeFun) )
      return _badargs.errMsg("A function is being called, but "+txfp+" is not a function type");

    TypeFun tfun = (TypeFun)txfp;
    if( tfun.is_forward_ref() ) // Forward ref on incoming function
      return _badargs.forward_ref_err(tfun);

    // Error#2: bad-arg-count
    TypeFunPtr tfp = tfun.fun();
    if( tfp.nargs() != nargs() )
      return _badargs.errMsg("Passing "+nargs()+" arguments to "+tfp+" which takes "+tfp.nargs()+" arguments");

    // Error#3: Now do an arg-check
    TypeTuple formals = tfp._ts; // Type of each argument
    for( int j=0; j<nargs(); j++ ) {
      Type actual = gvn.type(arg(j));
      Type formal = formals.at(j);
      if( !actual.isa(formal) ) // Actual is not a formal
        return _badargs.typerr(actual,formal);
    }
    
    return null;
  }
  
  // Called from the data proj.  Return a TypeNode with proper casting on return result.
  TypeNode upcast_return(GVNGCM gvn) {
    Type t = _cast_ret;
    if( t==null ) return null;  // No cast-in-progress
    _cast_ret = null;           // Gonna upcast the return result now
    gvn.add_work(this);         // Revisit after the data-proj cleans out
    return new TypeNode(t,null,_cast_P);
  }

  @Override public Type all_type() { return TypeTuple.make(Type.CTRL,TypeMem.MEM,Type.SCALAR); }
  @Override public int hashCode() { return super.hashCode()+_rpc; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof CallNode) ) return false;
    CallNode call = (CallNode)o;
    return _rpc==call._rpc;
  }

}

