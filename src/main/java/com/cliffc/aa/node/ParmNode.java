package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFld;

// Function parameter node; almost just a Phi with a name.  There is a dense
// numbering matching function arguments, with -1 reserved for the RPC and 0
// for memory.
public class ParmNode extends PhiNode {
  public final int _idx; // Parameter index, MEM_IDX, FUN_IDX is display, ARGIDX+ normal args
  final String _name;    // Parameter name
  public ParmNode( int idx, String name, Node fun, ConNode defalt, Parse badgc) {
    this(defalt._t,badgc,fun,idx,name);
    add_def(defalt);
  }
  public ParmNode( TypeFld fld, Node fun, ConNode defalt, Parse badgc) {
    this(fld._t.simple_ptr(),badgc,fun,fld._order,fld._fld);
    add_def(defalt);
  }
  public ParmNode( int idx, String name, Node fun, Type tdef, Node defalt, Parse badgc) {
    this(tdef,badgc,fun,idx,name);
    add_def(defalt);
  }

  public ParmNode( Type tdef, Parse badgc, Node fun, int idx, String name ) {
    super(OP_PARM,tdef,badgc,fun);
    assert idx>=0;
    _idx=idx;
    _name=name;
  }
  public FunNode fun() { return (FunNode) in(0); }
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
    if( fun._defs._len!=_defs._len ) return null;
    if( fun.is_copy(0)!=null )       // FunNode is a Copy
      return in(1)==this ? Env.ANY : in(1);             // So return the copy
    // Do not otherwise fold away, as this lets Nodes in *this* function depend
    // on values in some other function... which, if code-split, gets confused
    // (would have to re-insert the Parm).
    return null;
  }

  @Override public Type value() {
    // Not executing?
    Type ctl = val(0);
    if( ctl != Type.CTRL && ctl != Type.ALL ) return ctl.oob();
    Node in0 = in(0);
    if( !(in0 instanceof FunNode) )  return ctl.oob();
    FunNode fun = (FunNode)in0;
    if( fun._java_fun ) return _t;
    if( fun.len()!=len() ) return Type.ALL; // Collapsing

    // Merge all live paths
    Type t = Type.ANY;
    for( int i=1; i<_defs._len; i++ )
      if( fun.val(i)!=Type.XCTRL && fun.val(i)!=Type.ANY ) // Only meet alive paths
        t = t.meet(val(i));
    return t.join(_t);
  }

  // If an input to a Mem Parm changes, the flow results of other Parms can change
  @Override public void add_flow_use_extra(Node chg) {
    if( is_mem() )
      for( Node parm : in(0)._uses )
        if( parm instanceof ParmNode && parm != this )
          Env.GVN.add_flow(parm);
  }

  // While Parms are mostly Phis (and yes for value flows), during unification
  // Parms are already treated by the H-M algo, and (via fresh_unify) get
  // "fresh" TVars for every input path.
  @Override public boolean unify( boolean test ) { return false; }

  //@Override public ErrMsg err( boolean fast ) {
  //  if( !(in(0) instanceof FunNode) ) return null; // Dead, report elsewhere
  //  FunNode fun = fun();
  //  if( fun.in(0)== fun ) return null;  // Dead, being inlined
  //  if( fun.len()!=len() ) return null; // Broken, dying
  //  if( _idx <= MEM_IDX ) return null;  // No arg check on RPC or memory
  //  Node mem = fun.parm(MEM_IDX);
  //  assert _name!=null;
  //  TypeFld ffld = fun.formals().get(_name);
  //  if( ffld==null ) return null; // dead display, because loading a high value
  //  Type formal = ffld._t;
  //  for( int i=1; i<_defs._len; i++ ) {
  //    if( fun.val(i)==Type.XCTRL ) continue;// Ignore dead paths
  //    Type argt = mem == null ? in(i)._val : in(i).sharptr(mem.in(i)); // Arg type for this incoming path
  //    if( argt!=Type.ALL && !argt.above_center() && !argt.isa(formal) ) { // Argument is legal?  ALL args are in-error elsewhere
  //      // The merge of all incoming calls for this argument is not legal.
  //      // Find the call bringing the broken args, and use it for error
  //      // reporting - it MUST exist, or we have a really weird situation
  //      for( Node def : fun._defs ) {
  //        if( def instanceof CProjNode && def.in(0) instanceof CallNode ) {
  //          CallNode call = (CallNode)def.in(0);
  //          if( call.nargs() != fun.nargs() )
  //            return null;      // #args errors reported before bad-args
  //          Type argc = call.arg(_idx).sharptr(call.mem()); // Call arg type
  //          if( argc!=Type.ALL && !argc.isa(formal) ) // Check this call
  //            return fast ? ErrMsg.FAST : ErrMsg.typerr(call._badargs[_idx-ARG_IDX+1],argc, call.mem()._val,formal);
  //          // Must be a different call that is in-error
  //        }
  //      }
  //      // meet of args is not the formal, but no single arg is not the formal?
  //      return fast ? ErrMsg.FAST : ErrMsg.typerr(_badgc,argt,mem.val(i),formal); // Can be the default
  //    }
  //  }
  //  return null;
  //}
}
