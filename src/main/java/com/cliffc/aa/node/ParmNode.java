package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.MEM_IDX;

// Function parameter node; almost just a Phi with a name.  There is a dense
// numbering matching function arguments, with -1 reserved for the RPC and 0
// for memory.
public class ParmNode extends PhiNode {
  public final int _idx; // Parameter index, -1 RPC, 0 Mem, 1 Display, 2+ normal args
  final String _name;         // Parameter name
  public ParmNode( int idx, String name, Node fun, ConNode defalt, Parse badgc) {
    this(idx,name,fun,defalt._t,defalt,badgc);
  }
  public ParmNode( int idx, String name, Node fun, Type tdef, Node defalt, Parse badgc) {
    super(OP_PARM,fun,tdef,defalt,badgc);
    assert idx>-2;
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
    if( !(in(0) instanceof FunNode) )
      return in(0).is_copy(_idx); // Dying, or thunks
    FunNode fun = fun();
    if( fun.val() == Type.XCTRL ) return null; // All dead, c-prop will fold up
    assert fun._defs._len==_defs._len;

    // Has unknown caller input
    if( fun._defs.len() > 1 && fun.in(1) == Env.ALL_CTRL ) return null;
    if( fun.noinline() ) return null; // Do not fold up, because asked not to.

    // TODO: Relax this
    // Never collapse memory phi, used for error reporting by other parms.
    if( _idx== 0 )
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
    Node mem = fun.parm(MEM_IDX);
    for( int i=1; i<_defs._len; i++  ) { // For all arguments
      Node n = in(i);
      if( fun.val(i)==Type.CTRL ) {    // Dead path can ignore both valid and invalid args
        if( !valid_args(fun,i,mem) ) return null; // No collapse invalid args; want them for errors
        if( n==this || n==live ) continue; // Ignore self or duplicates
        if( live==null ) live = n;         // Found unique live input
        else live=this;         // Found 2nd live input, no collapse
      }
    }
    return live == this ? null : live; // Return single unique live input
  }

  private boolean valid_args( FunNode fun, int i, Node mem ) {
    if( fun._thunk_rhs ) return true; // Always allow folding of Thunks
    // Check arg type, after sharpening
    Type actual = mem==null ? val(i) : in(i).sharptr(mem.in(i));
    Type formal = fun.formal(_idx);
    return actual.isa(formal);
  }

  @Override public Type value(GVNGCM.Mode opt_mode) {
    // Not executing?
    Type ctl = val(0);
    if( ctl != Type.CTRL ) return ctl.oob();
    Node in0 = in(0);
    if( in0 instanceof ThunkNode ) return val(1);
    if( !(in0 instanceof FunNode) )  return ctl.oob();
    // If unknown callers, then always the default value because some unknown
    // caller can be that bad.  During & after GCP all unknown callers are
    // accounted for.
    FunNode fun = (FunNode)in0;
    if( !opt_mode._CG && fun.has_unknown_callers() )
      return val(1);
    Node mem = fun.parm(MEM_IDX);
    // All callers known; merge the wired & flowing ones
    Type t = Type.ANY;
    for( int i=1; i<_defs._len; i++ ) {
      if( fun.val(i)==Type.XCTRL || fun.val(i)==Type.ANY ) continue; // Only meet alive paths
      // Check arg type, after sharpening
      Type ta = mem == null ? val(i) : in(i).sharptr(mem.in(i));
      t = t.meet(ta);
    }

    if( _idx <= 0 ) return t;
    // High, but valid, values like choice-functions need to pass thru,
    // so following Calls agree that SOME function will be called.
    // Check against formals; if OOB, always produce an error.
    Type formal = fun.formal(_idx);
    // Good case:
    if( t.isa(formal) ) return t.simple_ptr();
    // Bad case: OOB, but up or down according to how close the formal is matched.
    return t.oob_deep(formal);
  }

  @Override public ErrMsg err( boolean fast ) {
    if( !(in(0) instanceof FunNode) ) return null; // Dead, report elsewhere
    FunNode fun = fun();
    assert fun._defs._len==_defs._len;
    if( _idx < 0 ) return null;                    // No arg check on RPC or Mem
    Node mem = fun.parm(MEM_IDX);
    Type formal = fun.formal(_idx);
    for( int i=1; i<_defs._len; i++ ) {
      if( fun.val(i)==Type.XCTRL ) continue;// Ignore dead paths
      Type argt = mem == null ? in(i).val() : in(i).sharptr(mem.in(i)); // Arg type for this incoming path
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
              return fast ? ErrMsg.FAST : ErrMsg.typerr(call._badargs[_idx-1],argc, call.mem().val(),formal);
            // Must be a different call that is in-error
          }
        }
        // meet of args is not the formal, but no single arg is not the formal?
        return fast ? ErrMsg.FAST : ErrMsg.typerr(_badgc,argt,mem.val(i),formal); // Can be the default
      }
    }
    return null;
  }
}
