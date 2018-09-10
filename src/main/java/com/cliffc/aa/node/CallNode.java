package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Bits;

// See FunNode.  Control is not required for an apply but inlining the function
// body will require it; slot 0 is for Control.  Slot 1 is a function value - a
// Node with a TypeFun or a TypeUnion of TypeFuns.  Slots 2+ are for args.
//
// When the function simplifies to a single TypeFun, the Call can inline.
// Otherwise the TypeUnion lists a bunch of function pointers are allowed here.
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
  private Parse  _badargs;      // Error for e.g. wrong arg counts or incompatible args
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
  private Node inline( GVNGCM gvn, Node rez ) {
    set_def(1,rez ,gvn);        // New result is function epilog result
    _inlined = true;
    return this;
  }
  // Called by projections when folding away the call
  @Override public Node is_copy(GVNGCM gvn, int idx) { return _inlined ? in(idx) : null; }

  // Number of actual arguments
  int nargs() { return _defs._len-2; }
  // Actual arguments.
  Node arg( int x ) { return _defs.at(x+2); }
  
  // Clones during inlining all become unique new call sites
  @Override Node copy() {
    CallNode call = super.copy();
    call._rpc = RPC++;
    return call;
  }
  
  @Override public Node ideal(GVNGCM gvn) {
    // If an inline is in-progress, no other opts and this node will go dead
    if( _inlined ) return null;
    // If an upcast is in-progress, no other opts until it finishes
    if( _cast_ret !=null ) return null;

    // When do i do 'pattern matching'?  For the moment, right here: if not
    // already unpacked a tuple, and can see the NewNode, unpack it right now.
    if( !_unpacked ) { // Not yet unpacked a tuple
      assert nargs()==1;
      Node nn = arg(0);
      Type tn = gvn.type(nn);
      if( tn instanceof TypeTuple ) {
        TypeTuple tt = (TypeTuple)tn;
        // Either all the edges from a NewNode (for non-constants), or all the
        // constants types from a constant Tuple from a ConNode
        assert nn instanceof NewNode || tt.is_con();
        int len = nn instanceof NewNode ? nn._defs._len-1 : tt._ts.length;
        pop();  gvn.add_work(nn);  // Pop off the NewNode/ConNode tuple
        for( int i=0; i<len; i++ ) // Push the args; unpacks the tuple
          add_def( nn instanceof NewNode ? nn.in(i+1) : gvn.con(tt.at(i)) );
        _unpacked = true;       // Only do it once
        return this;
      }
    }

    // Type-checking a function; requires 2 steps, one now, one in the
    // following data Proj from the worklist.
    Node unk  = in(1);          // Function epilog/function pointer
    if( unk instanceof TypeNode ) {
      TypeNode tn = (TypeNode)unk;
      TypeTuple t_funptr = (TypeTuple)tn._t;
      assert t_funptr.is_fun_ptr();
      TypeFun tf = t_funptr.get_fun();
      set_def(1,tn.in(1),gvn);
      for( int i=0; i<nargs(); i++ ) // Insert casts for each parm
        set_def(i+2,gvn.xform(new TypeNode(tf._ts.at(i),arg(i),tn._error_parse)),gvn);
      _cast_ret = tf._ret;       // Upcast return results
      _cast_P = tn._error_parse; // Upcast failure message
      return this;
    }

    // If the function is unresolved, see if we can resolve it now
    if( unk instanceof UnresolvedNode ) {
      Node fun = ((UnresolvedNode)unk).resolve(gvn,this);
      if( fun != null ) { set_def(1,fun,gvn); return this; }
    }

    // Unknown function(s) being called
    if( !(unk instanceof EpilogNode) )
      return null;
    // From here on down we know the exact function being called
    EpilogNode epi = (EpilogNode)unk;
    Node rez = epi.val();
    // Function is single-caller (me) and collapsing
    if( epi.is_copy(gvn,3) != null )
      return inline(gvn,rez);
    // Function is well-formed
    
    // Arg counts must be compatible
    FunNode fun = epi.fun();
    if( fun._tf.nargs() != nargs() )
      return null;

    // Single choice; insert actual conversions as needed
    TypeTuple formals = fun._tf._ts;
    for( int i=0; i<nargs(); i++ ) {
      Type formal = formals.at(i);
      Type actual = gvn.type(arg(i));
      byte xcvt = actual.isBitShape(formal);
      if( xcvt == 99 ) return null;
      if( xcvt == -1 ) return null;       // Wait for call args to resolve
      if( xcvt == 1 ) {
        PrimNode cvt = PrimNode.convert(arg(i),actual,formal);
        if( cvt.is_lossy() ) throw new IllegalArgumentException("Requires lossy conversion");
        set_def(i+2,gvn.xform(cvt),gvn); // set the converted arg
      }
    }

    // If this is a forward-ref we have no body to inline
    if( epi.is_forward_ref() )
      return null;

    // Check for several trivial cases that can be fully inlined immediately.
    // Check for zero-op body (id function)
    if( rez instanceof ParmNode && rez.in(0) == fun ) return inline(gvn,arg(((ParmNode)rez)._idx));
    // Check for constant body
    if( rez instanceof ConNode ) return inline(gvn,rez);

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
      return inline(gvn,gvn.xform(irez)); // New exciting replacement for inlined call
    }

    assert fun.in(1)._uid!=0; // Never wire into a primitive, just clone/inline it instead (done just above)
    assert fun._tf.nargs() == nargs();

    // Always wire caller args into known functions
    return wire(gvn,fun);
  }

  // Wire the call args to a known function, letting the function have precise
  // knowledge of its callers and arguments.
  // Leaves the Call in the graph - making the graph "a little odd" - double
  // CTRL users - once for the call, and once for the function being called.
  Node wire(GVNGCM gvn, FunNode fun) {
    Node ctrl = in(0);
    for( int i=2; i<fun._defs.len(); i++ ) // Skip default control (for top-level calls vs top-level fun-defs)
      if( fun._defs.at(i)==ctrl ) // Look for same control
        return null;              // Already wired up
    
    // Do an arg check before wiring up; cannot wire busted args (do not
    // propagate type errors past function call boundaries).
    for( Node arg : fun._uses ) {
      if( arg.in(0) == fun && arg instanceof ParmNode ) {
        int idx = ((ParmNode)arg)._idx; // Argument number, or -1 for rpc
        if( idx != -1 &&
            (idx >= nargs() || !gvn.type(arg(idx)).isa(fun._tf.arg(idx))) )
          return null;          // Illegal args?
      }
    }
    
    // Add an input path to all incoming arg ParmNodes from the Call.  Cannot
    // assert finding all args, because dead args may already be removed - and
    // so there's no Parm/Phi to attach the incoming arg to.
    for( Node arg : fun._uses ) {
      if( arg.in(0) == fun && arg instanceof ParmNode ) {
        int idx = ((ParmNode)arg)._idx; // Argument number, or -1 for rpc
        assert idx<nargs();
        Node actual = idx==-1 ? gvn.con(TypeRPC.make(_rpc)) : arg(idx);
        gvn.add_def(arg,actual);
      }
    }
    // Add Control for this path.  Sometimes called from fun.Ideal() (because
    // inlining), sometimes called by Epilog when it discovers all callers
    // known.
    if( gvn.touched(fun) || gvn._opt ) gvn.add_def(fun,in(0));
    else                               fun.add_def(    in(0));
    return this;
  }

  // Make real call edges from virtual call edges
  private void wire(GVNGCM gvn, Type funptr) {
    if( !(funptr instanceof TypeTuple) ) return; // Not fallen to a funptr yet
    assert funptr.isa(TypeTuple.GENERIC_FUN);
    TypeTuple tfunptr = (TypeTuple)funptr;
    TypeFun tf = tfunptr.get_fun(); // Get type-propagated function list
    Bits fidxs = tf._fidxs;     // Get all the propagated reaching functions
    if( fidxs.above_center() ) return;
    for( int fidx : fidxs ) {   // For all functions
      if( fidx >= FunNode.PRIM_CNT ) // Do not wire up primitives, but forever take their default inputs and outputs
        wire(gvn,FunNode.find_fidx(fidx));
    }
  }
  
  @Override public Type value(GVNGCM gvn) {
    Type tc = gvn.type(in(0));  // Control type
    Node fp = in(1);            // If inlined, its the result, if not inlined, its the function being called
    Type t = gvn.type(fp);      // If inlined, its the result, if not inlined, its the function being called
    if( _inlined )              // Inlined functions just pass thru & disappear
      return TypeTuple.make_all(tc,t);
    
    if( gvn._opt ) // Manifesting optimistic virtual edges between caller and callee
      wire(gvn,t); // Make real edges from virtual edges

    Type trez = Type.ANY;
    if( fp instanceof UnresolvedNode ) {
      // For unresolved, we can take the BEST choice; i.e. the JOIN of every
      // choice.  Typically one choice works and the others report type
      // errors on arguments.
      for( Node epi : fp._defs )
        trez = trez.meet(value1(gvn.type(epi))); // JOIN of choices
    } else {                                  // Single resolved target
      trez = value1(t);
    }

    // Return {control,value} tuple.
    return TypeTuple.make_all(tc,trez);
  }

  private Type value1( Type t ) {
    assert t.is_fun_ptr();
    TypeTuple tepi = (TypeTuple)t;
    return tepi.at(0) == Type.XCTRL ? Type.XSCALAR : tepi.at(1);
  }
  
  @Override public String err(GVNGCM gvn) {
    assert !_inlined;           // Should have already cleaned out
    
    // Error#1: fail for passed-in unknown references
    for( int j=0; j<nargs(); j++ ) 
      if( arg(j).is_forward_ref() )
        return _badargs.forward_ref_err(gvn.type(arg(j)));
    
    Node fp = in(1);      // Either function pointer, or unresolve list of them
    Node xfp = fp instanceof UnresolvedNode ? fp.in(0) : fp;
    TypeFun txfun = ((TypeTuple)gvn.type(xfp)).get_fun();
    if( txfun.is_forward_ref() ) // Forward ref on incoming function
      return _badargs.forward_ref_err(txfun);

    // Error#2: bad-arg-count
    if( txfun.nargs() != nargs() )
      return _badargs.errMsg("Passing "+nargs()+" arguments to "+txfun+" which takes "+txfun.nargs()+" arguments");

    // Error#3: ambiguous
    if( fp instanceof UnresolvedNode )
      //return _badargs.errMsg("Ambiguous call");
      return null;              // If unresolved, must also be uncalled so allow arg badness

    // Error#4: Now do an arg-check
    TypeTuple formals = txfun._ts; // Type of each argument
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

  @Override public Type all_type() { return TypeTuple.make_all(Type.CTRL,Type.SCALAR); }
  @Override public int hashCode() { return super.hashCode()+_rpc; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof CallNode) ) return false;
    CallNode call = (CallNode)o;
    return _rpc==call._rpc;
  }

}

