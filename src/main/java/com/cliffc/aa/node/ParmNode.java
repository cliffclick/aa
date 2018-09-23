package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;

// Function parameter node; just a Phi with a name
public class ParmNode extends PhiNode {
  final int _idx;    // Parameter index, zero-based; -1 reserved for RPC
  private final String _name;       // Parameter name
  public ParmNode( int idx, String name, FunNode fun, ConNode defalt, String badgc) {
    super(OP_PARM,fun,defalt,badgc);
    _idx=idx;
    _name=name;
  }
  @Override String xstr() { return "Parm:"+_name; }
  @Override public int hashCode() { return super.hashCode()+_idx; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof ParmNode) ) return false;
    ParmNode parm = (ParmNode)o;
    return _idx==parm._idx;
  }
  @Override public Node ideal(GVNGCM gvn) {
    if( !(in(0) instanceof FunNode) ) return null; // Dying
    FunNode fun = (FunNode) in(0);
    assert fun._defs._len==_defs._len;
    if( gvn.type(fun) == Type.XCTRL ) return null; // All dead, c-prop will fold up
    if( fun._defs.len() > 2 || !fun._all_callers_known ) return null;
    // Down to a single input; arg-check before folding up
    if( _idx != -1 && !gvn.type(in(1)).isa(fun._tf._ts.at(_idx)) )
      return null;              // Not correct arg-type; refuse to collapse
    return in(1);
  }

  @Override public Type value(GVNGCM gvn) {
    Type t = _default_type.dual();
    if( !(in(0) instanceof FunNode) ) return t; // Dying
    FunNode r = (FunNode) in(0);
    assert r._defs._len==_defs._len;
    // TODO: During GCP, slot#1 is the "default" input and assumed never
    // called.  As callers appear, they wire up and become actual input edges.
    // Leaving slot#1 alive here makes every call appear to be called by the
    // default caller.  Fix is to have the default (undiscovered) caller
    // control be different from the top-level REPL caller, and set the
    // undiscovered control to XCTRL.
    int s = r.slot1(gvn) ? 1 : 2;
    for( int i=s; i<_defs._len; i++ )
      if( gvn.type(r.in(i))!=Type.XCTRL ) // Only meet alive paths
        t = t.meet(gvn.type(in(i)));
    return t;
  }
  @Override public String err( GVNGCM gvn ) {
    if( !(in(0) instanceof FunNode) ) return null; // Dead, report elsewhere
    FunNode fun = (FunNode) in(0);
    assert fun._defs._len==_defs._len;
    // For the function being returned-at-top, and thus NOT called on this path
    // - ignore the argument check.  Function is not being called.
    if( _defs._len==2 && !fun._all_callers_known ) return null; // Never called, so no argument fails
    if( _idx < 0 ) return null;                                 // No arg check on RPC
    Type formal = fun._tf.arg(_idx);
    for( int i=1; i<_defs._len; i++ ) {
      Type argt = gvn.type(in(i)); // Arg type for this incoming path
      if( !argt.isa(formal) ) {    // Argument is legal?
        // The merge of all incoming calls for this argument is not legal.
        // Find the call bringing the broken args, and use it for error
        // reporting - it MUST exist, or we have a really weird situation
        EpilogNode epi=null;       // Only 1 epilog per fun
        for( Node use : fun._uses ) if( use instanceof EpilogNode ) { epi=(EpilogNode)use; break; }
        for( Node use : epi._uses ) {
          if( use instanceof CallNode ) {
            CallNode call = (CallNode)use;
            Type argc = gvn.type(call.arg(_idx)); // Call arg type
            if( !argc.isa(formal) )
              return call._badargs.typerr(argc,formal);
            // Must be a different call that is in-error
          }
        }
        throw com.cliffc.aa.AA.unimpl(); // meet of args is not the formal, but no single arg is not the formal?
      }
    }
    return null;
  }
  
}
