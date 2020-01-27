package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeRPC;
import com.cliffc.aa.type.TypeMem;

// Function parameter node; just a Phi with a name
public class ParmNode extends PhiNode {
  final int _idx;             // Parameter index, zero-based; -1 reserved for RPC, -2 for mem
  private final String _name; // Parameter name
  private final Type _alltype;
  public ParmNode( int idx, String name, Node fun, ConNode defalt, Parse badgc) {
    super(OP_PARM,fun,defalt,badgc);
    _idx=idx;
    _name=name;
    _alltype = defalt._t;
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

  @Override public Node ideal(GVNGCM gvn, int level) {
    if( !(in(0) instanceof FunNode) ) return null; // Dying
    FunNode fun = (FunNode) in(0);
    if( gvn.type(fun) == Type.XCTRL ) return null; // All dead, c-prop will fold up
    if( (level&1)==0 )          // Not doing asserts 
      gvn.add_work2(fun);       // Something changed, re-check inlining chances
    assert fun._defs._len==_defs._len;
    // Arg-check before folding up
    if( _idx >= 0 ) {                         // Skip RPC and memory
      for( int i=1; i<_defs._len; i++  )      // For all arguments
        if( gvn.type(fun.in(i))==Type.CTRL && // Path is alive
            in(i)!=this &&                    // Can ignore self- only other inputs will determine arg-check
            !gvn.type(in(i)).isa(fun.targ(_idx)) ) // Arg is NOT correct type
          return null;          // Not correct arg-type; refuse to collapse
    }
    return super.ideal(gvn,level); // Let PhiNode collapse
  }
  
  @Override public Type value(GVNGCM gvn) {
    Type t = super.value(gvn);
    // Memory tracks the notion of 'clean' or 'unwritten' since the function
    // start.  Changed memory is returned at exit and unchanged memory is NOT
    // returned - and CallEpis are aware of this behavior and do the correct
    // merge-around.  This allows loads & stores below a call bypass the call.
    t = t.clean();              // Mark all as clean
    return t;
  }

  @Override public String err( GVNGCM gvn ) {
    if( !(in(0) instanceof FunNode) ) return null; // Dead, report elsewhere
    FunNode fun = (FunNode) in(0);
    assert fun._defs._len==_defs._len;
    if( _idx < 0 ) return null;                                 // No arg check on RPC
    Type formal = fun.targ(_idx);
    for( int i=1; i<_defs._len; i++ ) {
      Type argt = gvn.type(in(i)); // Arg type for this incoming path
      if( !argt.isa(formal) ) {    // Argument is legal?
        // The merge of all incoming calls for this argument is not legal.
        // Find the call bringing the broken args, and use it for error
        // reporting - it MUST exist, or we have a really weird situation
        RetNode ret = fun.ret();
        if( ret != null ) {
          FunPtrNode fptr=ret.funptr();  // Only 1 FunPtr per fun
          for( Node use : fptr._uses ) {
            if( use instanceof UnresolvedNode )
              use = use._uses.at(0); // TODO: Need to loop over the tree of uses
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
    }
    return null;
  }
  @Override public Type all_type() { return _idx==-1 ? TypeRPC.ALL_CALL : (_idx==-2 ? TypeMem.MEM : _alltype); }
}
