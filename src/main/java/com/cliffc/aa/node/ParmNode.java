package com.cliffc.aa.node;

import com.cliffc.aa.Env;
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
    if( fun._val == Type.XCTRL ) return null; // All dead, c-prop will fold up
    assert fun._defs._len==_defs._len;

    // Has unknown caller input
    if( fun._defs.len() > 1 && fun.in(1) == Env.ALL_CTRL ) return null;
    if( fun.noinline() ) return null; // Do not fold up, because asked not to.

    // TODO: Relax this
    // Never collapse memory phi, used for error reporting by other parms
    if( _idx== -2 )
      for( Node use : fun._uses )
        if( use instanceof ParmNode && use != this )
          return null;
    // If only 1 unique live input, return that
    // Arg-check before folding up.
    // - Dead path & self-cycle, always fold
    // - Live-path but
    //   - no Call, Cepi - confused, do not fold
    //   - not flowing, - types not aligned, do not fold
    //   - flowing but bad args, do not fold
    Node live=null;
    Node mem = fun.parm(-2);
    for( int i=1; i<_defs._len; i++  ) { // For all arguments
      Node n = in(i);
      if( fun.val(i)==Type.CTRL &&     // Dead path
          valid_args(fun,i,mem) ) {    // And valid arguments
        if( n==this || n==live ) continue; // Ignore self or duplicates
        if( live==null ) live = n;         // Found unique live input
        else live=this;         // Found 2nd live input, no collapse
      }
    }
    return live == this ? null : live; // Return single unique live input
  }

  private boolean valid_args( FunNode fun, int i, Node mem ) {
    // Check arg type, after sharpening
    Type actual = in(i).sharptr(mem.in(i));
    Type formal = fun.formal(_idx);
    return actual.isa(formal);
  }

  @Override public Type value(byte opt_mode) {
    // Not executing, go the
    Type ctl = val(0);
    if( ctl != Type.CTRL ) return ctl.oob();
    Node in0 = in(0);
    if( !(in0 instanceof FunNode) )  return in0._val.oob();
    // If unknown callers, then always the default value because some unknown
    // caller can be that bad.  During & after GCP all unknown callers are
    // accounted for.
    FunNode fun = (FunNode)in0;
    if( opt_mode < 2 && fun.has_unknown_callers() )
      return val(1);
    Node mem = fun.parm(-2);    // Memory for sharpening pointers
    // All callers known; merge the wired & flowing ones
    Type t = Type.ANY;
    for( int i=1; i<_defs._len; i++ ) {
      if( fun.val(i)!=Type.CTRL ) continue; // Only meet alive paths
      // Check arg type, after sharpening
      Type ta = in(i).sharptr(mem.in(i));
      t = t.meet(ta);
    }

    // Check against formals; if OOB, always produce an error.
    if( _idx < 0 ) return t;
    Type formal = fun.formal(_idx);
    // Good case: t.isa(formal).
    if( t.isa(formal) )  return t.simple_ptr();
    return t.bound(formal);
  }
  // TODO: for mem(), include ScopeNode.compute_live_mem forall args & mem.
  // Needed to sharpen args for e.g. value OOB and errors

  @Override public ErrMsg err( boolean fast ) {
    if( !(in(0) instanceof FunNode) ) return null; // Dead, report elsewhere
    FunNode fun = fun();
    assert fun._defs._len==_defs._len;
    if( _idx < 0 ) return null;                    // No arg check on RPC or Mem
    Node mem = fun.parm(-2);
    Type formal = fun.formal(_idx);
    for( int i=1; i<_defs._len; i++ ) {
      if( fun.val(i)!=Type.CTRL ) continue; // Ignore dead paths
      Type argt = in(i).sharptr(mem.in(i)); // Arg type for this incoming path
      if( argt!=Type.ALL && !argt.isa(formal) ) { // Argument is legal?  ALL args are in-error elsewhere
        // The merge of all incoming calls for this argument is not legal.
        // Find the call bringing the broken args, and use it for error
        // reporting - it MUST exist, or we have a really weird situation
        for( Node def : fun._defs ) {
          if( def instanceof CProjNode ) {
            CallNode call = (CallNode)def.in(0);
            if( call.nargs() != fun.nargs() )
              return null;      // #args errors reported before bad-args
            Type argc = call.arg(_idx).sharptr(call.mem()); // Call arg type
            if( argc!=Type.ALL && !argc.isa(formal) ) // Check this call
              return ErrMsg.typerr(call._badargs[_idx],argc,call.mem()._val,formal);
            // Must be a different call that is in-error
          }
        }
        // meet of args is not the formal, but no single arg is not the formal?
        return ErrMsg.typerr(_badgc,argt,mem.val(i),formal); // Can be the default
      }
    }
    return null;
  }
}
