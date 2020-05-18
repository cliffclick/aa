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
    if( gvn.type(fun) == Type.XCTRL ) return null; // All dead, c-prop will fold up
    assert fun._defs._len==_defs._len;

    // Has unknown caller input
    if( fun._defs.len() > 1 && fun.in(1) == Env.ALL_CTRL ) return null;

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
      if( gvn.type(fun.in(i))==Type.CTRL && // Dead path
          valid_args(gvn,fun,i,mem) ) {     // And valid arguments
        if( n==this || n==live ) continue;  // Ignore self or duplicates
        if( live==null ) live = n;          // Found unique live input
        else live=this;         // Found 2nd live input, no collapse
      }
    }
    return live == this ? null : live; // Return single unique live input
  }

  private boolean valid_args(GVNGCM gvn, FunNode fun, int i, Node mem) {
    Node call = fun.in(i).in(0);
    if( !(call instanceof CallNode) ) return false; // Bad graph, do not change
    CallEpiNode cepi  = ((CallNode)call).cepi();
    // If not flowing, then args are not aligned
    if( !cepi.cg_tst(fun.fidx()) ) return false;
    // Check arg type
    Type t = gvn.type(in(i));   // Arg type
    if( t instanceof TypeMemPtr ) // Sharpen pointers
      t = t.sharpen(gvn.type(mem.in(i)));
    if( !t.isa(fun.formal(_idx)) )
      return false; // Arg is NOT correct type
    return true;
  }

  @Override public Type value(GVNGCM gvn) {
    // Not executing, go the
    Type ctl = gvn.type(in(0));
    Type all = all_type();
    if( ctl != Type.CTRL ) return ctl.above_center() ? all.dual() : all;
    if( !(in(0) instanceof FunNode) )  return all;
    // If unknown callers, then always the default value because some unknown
    // caller can be that bad.
    FunNode fun = fun();
    if( fun.has_unknown_callers() )
      return gvn.type(in(1));
    Node mem = fun.parm(-2);    // Memory for sharpening pointers
    // All callers known; merge the wired & flowing ones
    Type t = all.dual();
    for( int i=1; i<_defs._len; i++ ) {
      if( gvn.type(fun.in(i))!=Type.CTRL ) continue; // Only meet alive paths
      // Only meet with wired & flowing edges
      Node call = fun.in(i).in(0);
      if( !(call instanceof CallNode) ) continue;
      CallEpiNode cepi = ((CallNode)call).cepi();
      if( cepi == null ) continue;             // Broken graph
      if( !cepi.cg_tst(fun.fidx()) ) continue; // Wired and flowing
      Type ta = gvn.type(in(i));   // Arg type
      if( ta instanceof TypeMemPtr ) // Sharpen pointers
        ta = ta.sharpen(gvn.type(mem.in(i)));
      t = t.meet(ta);
    }

    // Bound results by simple Fun argument types.  This keeps errors from
    // spreading past function call boundaries.
    if( _idx < 0 ) return t;
    Type formal = fun.formal(_idx);
    // Good case: t.isa(formal).
    if( formal.dual().isa(t) && t.isa(formal) )
      return t.simple_ptr();
    // Bad case.  If not a pointer, just pin at limits.
    if( !(t instanceof TypeMemPtr) || !(formal instanceof TypeMemPtr) )
      return (t.above_center() ? formal.dual() : formal).simple_ptr();
    // If a pointer, pin each of the aliases and object at limits.
    TypeMemPtr tmpa = (TypeMemPtr)t;
    TypeMemPtr tmpf = (TypeMemPtr)formal;
    int a = tmpf._aliases.getbit();
    if( tmpa._aliases.above_center() ) a = -a;
    TypeObj o = tmpa._obj.above_center() ? TypeObj.XOBJ : TypeObj.OBJ;
    return TypeMemPtr.make(a,o);
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
