package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;

import static com.cliffc.aa.AA.ARG_IDX;
import static com.cliffc.aa.AA.MEM_IDX;

// Function parameter node; almost just a Phi with a name.  There is a dense
// numbering matching function arguments, with -1 reserved for the RPC and 0
// for memory.
public class ParmNode extends PhiNode {
  public final int _idx; // Parameter index, MEM_IDX, FUN_IDX is display, ARGIDX+ normal args
  final String _name;    // Parameter name
  public ParmNode( int idx, String name, Node fun, ConNode defalt, Parse badgc) {
    this(idx,name,fun,defalt._t,defalt,badgc);
  }
  public ParmNode( int idx, String name, Node fun, Type tdef, Node defalt, Parse badgc) {
    super(OP_PARM,fun,tdef,defalt,badgc);
    assert idx>=0;
    _idx=idx;
    _name=name;
  }
  FunNode fun() { return (FunNode) in(0); }
  @Override public String xstr() { return "Parm:"+_name; }
  @Override public int hashCode() { return super.hashCode()+_idx; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof ParmNode) ) return false;
    ParmNode parm = (ParmNode)o;
    return _idx==parm._idx;
  }

  @Override public Node ideal_reduce() {
    if( !(in(0) instanceof FunNode) )
      return in(0).is_copy(_idx); // Dying, or thunks
    FunNode fun = fun();
    if( fun._val == Type.XCTRL ) return null; // All dead, c-prop will fold up
    assert fun._defs._len==_defs._len;
    if( fun.in(0)!=null && in(1) != this) // FunNode is a Copy
      return in(1);             // So return the copy
    // Do not otherwise fold away, as this lets Nodes in *this* function depend
    // on values in some other function... which, if code-split, gets confused
    // (would have to re-insert the Parm).
    return null;
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
    if( fun.in(0)==fun ) return t.simple_ptr(); // Function is collapsing, memory not available to check formals
    // High, but valid, values like choice-functions need to pass thru,
    // so following Calls agree that SOME function will be called.
    // Check against formals; if OOB, always produce an error.
    Type formal = fun.formal(_idx);
    // Good case:
    if( t.isa(formal) ) return t.simple_ptr();
    return Type.ALL;
  }

  // If an input to a Mem Parm changes, the flow results of other Parms can change
  @Override public void add_flow_use_extra(Node chg) {
    if( is_mem() )
      for( Node parm : in(0)._uses )
        if( parm instanceof ParmNode && parm != this )
          Env.GVN.add_flow(parm);
  }

  //@Override public TV2 new_tvar(String alloc_site) {
  //  if( _name==null ) return null; // Wait till initialized
  //  return _idx==MEM_IDX ? TV2.make_mem(this,alloc_site) : TV2.make_leaf(this,alloc_site);
  //}
  //
  //// While Parms are mostly Phis (and yes for value flows), during unification
  //// Parms are already treated by the H-M algo, and (via fresh_unify) get
  //// "fresh" TVars for every input path.
  //@Override public boolean unify( boolean test ) { return false; }

  @Override public ErrMsg err( boolean fast ) {
    if( !(in(0) instanceof FunNode) ) return null; // Dead, report elsewhere
    FunNode fun = fun();
    if( fun.in(0)== fun ) return null; // Dead, being inlined
    assert fun._defs._len==_defs._len;
    if( _idx <= MEM_IDX ) return null; // No arg check on RPC or memory
    Node mem = fun.parm(MEM_IDX);
    Type formal = fun.formal(_idx);
    for( int i=1; i<_defs._len; i++ ) {
      if( fun.val(i)==Type.XCTRL ) continue;// Ignore dead paths
      Type argt = mem == null ? in(i)._val : in(i).sharptr(mem.in(i)); // Arg type for this incoming path
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
              return fast ? ErrMsg.FAST : ErrMsg.typerr(call._badargs[_idx-ARG_IDX+1],argc, call.mem()._val,formal);
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
