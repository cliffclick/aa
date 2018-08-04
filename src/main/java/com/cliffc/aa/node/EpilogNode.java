package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.*;
import java.util.BitSet;

// Tail end of functions.  Gathers:
// - exit control; function may never exit or may be more than one
// - exit value;
// - RPC - where to jump-to next; the Continuation
// - The FunNode function header (quickly maps to SESE region header)
public class EpilogNode extends Node {
  final String _unkref_err; // Unknown ref error (not really a forward ref)
  public EpilogNode( Node ctrl, Node val, Node rpc, Node fun, String unkref_err ) { super(OP_EPI,ctrl,val,rpc,fun); _unkref_err=unkref_err; }
  @Override public Node ideal(GVNGCM gvn) {
    if( skip_ctrl(gvn) ) return this;

    // Look at the set of uses post-Parse; at parse time there will be no uses.
    if( _uses._len == 0 ) return null; // Dead, or during-parse

    FunNode fun = fun();
    if( fun.callers_known(gvn) ) return null;
    
    // After parse, we have the complete set of uses.  If there are any uses as
    // a function-pointer, then "all is lost" we have to assume the F-P is
    // called later.  If all uses are RPCs or not-inlined Calls, we can union
    // them all - and cut out any incoming paths to the FunNode that have no
    // matching RPC.  Once a top-level Parse exits the "unknown callers" often
    // go away.
    BitSet bs = new BitSet();   // Union of RPCs
    for( Node use : _uses ) {
      int rpc;
      if( use instanceof RPCNode ) rpc = ((RPCNode)use)._rpc;
      else if( use instanceof CallNode ) { // Un-inlined call site
        CallNode call = (CallNode)use;
        // If any use is as an argument, all is lost.
        for( int i=0; i<call.nargs(); i++ ) if( call.arg(i)==this ) return null;
        assert call.in(1) == this;
        rpc = call._rpc;
      } else if( use instanceof CastNode ) continue; // Casts of RPC results are OK
      else return null;         // Else unknown function-pointer user
      bs.set(rpc);
    }

    // Not sure how we can have callers with no returns, so assert we found
    // them all.... but fairly sure there's a path involving late-appearing
    // dead paths that clean out quicker on the RPCs vs the FunNode inputs.
    boolean progress = false;
    ParmNode rpc=null;
    for( Node parm : fun._uses )
      if( parm instanceof ParmNode && ((ParmNode)parm)._name.equals("rpc") )
        { assert rpc==null; rpc = ((ParmNode)parm); }
    if( rpc == null ) return null;
    // Skip the unknown caller in slot 1
    assert gvn.type(rpc.in(1)) == TypeRPC.ALL_CALL;
    for( int i=2; i<rpc._defs._len; i++ ) {
      if( gvn.type( fun.in(i) ) == Type.XCTRL ) continue; // Path is dead
      TypeRPC t = (TypeRPC)gvn.type(rpc.in(i));
      if( !t.is_con() ) throw AA.unimpl(); // merged multi-callers path
      int irpc = t.rpc();
      if( bs.get(irpc) ) bs.clear(irpc); // Found matching input path; clear from BS
      else { gvn.set_def_reg(fun,i,gvn.con(Type.XCTRL)); progress=true; }// No RPC for this input path, clear path
    }

    // If all RPCs are accounted for, then kill the unknown caller.
    if( bs.isEmpty() ) {
      gvn.set_def_reg(fun,1,gvn.con(Type.XCTRL));
      fun.callers_known(gvn);
      progress=true;
    }

    return progress ? this : null;
  }
  @Override public Type value(GVNGCM gvn) {
    Type t=TypeTuple.make_all(gvn.type(ctrl()), // Function exits, or not
                              gvn.type(val ()), // Function return value
                              gvn.type(rpc ()), // Caller; the Continuation
                              fun()._tf);       // Function type plus "fidx"
    assert t.is_fun_ptr();
    return t;
  }
  // If the return PC is a constant, this is a single-target function and is
  // effectively being inlined on the spot, removing the function head and tail.
  @Override public Node is_copy(GVNGCM gvn, int idx) {
    assert idx==0 || idx==1;
    assert !gvn.type(rpc()).is_con() || fun().callers_known(gvn);
    return gvn.type(rpc()).is_con() ? in(idx) : null;
  }
  
  public    Node ctrl() { return          in(0); } // internal function control
            Node val () { return          in(1); } // standard exit value
  public    Node rpc () { return          in(2); } // Almost surely a PhiNode merging RPCs
  public FunNode fun () { return (FunNode) in(3); } // Function header
  @Override String xstr() {                        // Self short name
    String name = fun().name();
    return name==null ? "Epilog" : "Epi#"+name;
  }

  // A forward-ref is an assumed unknown-function being used before being
  // declared.  Hence we want a callable function pointer, but have no defined
  // body (yet).  Make a function pointer that takes/ignores all args, and
  // returns any/top.
  public static Node forward_ref( GVNGCM gvn, Node scope, String name, Parse unkref ) {
    FunNode fun = gvn.init(new FunNode(scope,name));
    String referr = unkref.errMsg("Unknown ref '"+name+"'");
    return new EpilogNode(fun,gvn.con(TypeErr.ANY),gvn.con(TypeRPC.ALL_CALL),fun, referr);
  }

  // True if this is a forward_ref
  @Override public boolean is_forward_ref() { return in(0)== in(3) && fun()._tf.is_forward_ref(); }

  // 'this' is a forward reference, probably with multiple uses (and no inlined
  // callers).  Passed in the matching function definition, which is brand new
  // and has no uses.  Merge the two.
  public void merge_ref_def( GVNGCM gvn, String tok, EpilogNode def ) {
    FunNode rfun = fun();
    FunNode dfun = def.fun();
    assert rfun._defs._len==2 && rfun.in(0)==null && dfun.in(1) instanceof ScopeNode; // Forward ref has no callers
    assert dfun._defs._len==2 && dfun.in(0)==null && dfun.in(1) instanceof ScopeNode;
    assert def._uses._len==0;                      // Def is brand new, no uses

    gvn.subsume(this,def);
    dfun.bind(tok);
  }

  @Override public Type all_type() { return TypeTuple.GENERIC_FUN; }
  
  // Return the op_prec of the returned value.  Not sensible except when call
  // on primitives.
  @Override public byte op_prec() { return val().op_prec(); }
}
