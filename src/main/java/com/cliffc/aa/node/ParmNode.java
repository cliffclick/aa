package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

// Function parameter node; almost just a Phi with a name.  There is a dense
// numbering matching function arguments, with -1 reserved for the RPC and -2
// for memory.
public class ParmNode extends PhiNode {
  public final int _idx; // Parameter index, zero-based; -1 reserved for RPC, -2 for mem
  final String _name;         // Parameter name
  public ParmNode( int idx, String name, Node fun, ConNode defalt, Parse badgc) {
    this(idx,name,fun,defalt._t,defalt,badgc);
  }
  public ParmNode( int idx, String name, Node fun, Type tdef, Node defalt, Parse badgc) {
    super(OP_PARM,fun,tdef,defalt,badgc);
    _idx=idx;
    _name=name;
  }
  FunNode fun() { return (FunNode) in(0); }
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
    FunNode fun = fun();
    if( gvn.type(fun) == Type.XCTRL ) return null; // All dead, c-prop will fold up
    assert fun._defs._len==_defs._len;
    // Arg-check before folding up
    if( _idx >= 0 ) {                         // Skip RPC and memory
      Node mem = fun.parm(-2);
      for( int i=1; i<_defs._len; i++  )      // For all arguments
        if( gvn.type(fun.in(i))==Type.CTRL && // Path is alive
            in(i)!=this &&                    // Can ignore self- only other inputs will determine arg-check
            !gvn.sharptr(in(i),mem.in(i)).isa(fun.formal(_idx)) ) // Arg is NOT correct type
          return null;          // Not correct arg-type; refuse to collapse
    } else if( _idx== -2 ) {
      for( Node use : fun._uses )
        if( use instanceof ParmNode && use != this )
          // TODO: Relax this
          return null; // Never collapse memory phi, used for error reporting by other parms
    }
    return super.ideal(gvn,level); // Let PhiNode collapse
  }

  @Override public Type value(GVNGCM gvn) {
    // Not executing, go the 
    Type ctl = gvn.type(in(0));
    Type t = all_type().dual();
    if( ctl != Type.CTRL ) return ctl.above_center() ? t : t.dual();
    // If unknown callers, then always the default value because some unknown
    // caller can be that bad.
    FunNode fun = fun();
    if( fun.has_unknown_callers() )
      return gvn.type(in(1));
    // All callers known; merge the wired & flowing ones
    CallEpiNode cepi;
    for( int i=1; i<_defs._len; i++ )
      if( gvn.type(fun.in(i))==Type.CTRL ) { // Only meet alive paths
        // Only meet with wired edges
        if( (cepi=((CallNode)fun.in(i).in(0)).cepi())!=null &&
             cepi.cg_tst(fun.fidx()) )
          t = t.meet(gvn.type(in(i)));
      }
    // Bound results by simple Fun argument types.  This keeps errors from
    // spreading past function call boundaries.
    if( _idx >= 0 )
      t = t.bound(fun.formal(_idx).simple_ptr());
    assert t.bound(_t)==t;
    return t;
  }

  // Same as PhiNode, but bound like value
  @Override public Type all_type() {
    if( in(0) instanceof FunNode && _idx >= 0 )
      return fun().formal(_idx).simple_ptr();
    return _t;
  }
  @Override public String err( GVNGCM gvn ) {
    if( !(in(0) instanceof FunNode) ) return null; // Dead, report elsewhere
    FunNode fun = fun();
    assert fun._defs._len==_defs._len;
    if( _idx < 0 ) return null;                    // No arg check on RPC or Mem
    Node mem = fun.parm(-2);
    Type formal = fun.formal(_idx);
    for( int i=1; i<_defs._len; i++ ) {
      if( gvn.type(fun.in(i))!=Type.CTRL ) continue; // Ignore dead paths
      Type argt = gvn.sharptr(in(i),mem); // Arg type for this incoming path
      if( !argt.isa(formal) ) {    // Argument is legal?
        // The merge of all incoming calls for this argument is not legal.
        // Find the call bringing the broken args, and use it for error
        // reporting - it MUST exist, or we have a really weird situation
        for( Node def : fun._defs ) {
          if( def instanceof CProjNode ) {
            CallNode call = (CallNode)def.in(0);
            if( call.nargs() != fun.nargs() )
              return null;                        // #args errors reported before bad-args
            Type argc = gvn.sharptr(call.arg(_idx),call.mem()); // Call arg type
            if( !argc.isa(formal) ) // Check this call
              return call._badargs[_idx].typerr(argc,call.mem(),formal);
            // Must be a different call that is in-error
          }
        }
        throw com.cliffc.aa.AA.unimpl(); // meet of args is not the formal, but no single arg is not the formal?
      }
    }
    return null;
  }
}
