package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFld;

import static com.cliffc.aa.AA.*;

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
    if( len()==1 ) return null;
    assert fun._defs._len==_defs._len;
    if( fun.is_copy(0)!=null )       // FunNode is a Copy
      return in(1)==this ? Env.ANY : in(1);             // So return the copy
    // Do not otherwise fold away, as this lets Nodes in *this* function depend
    // on values in some other function... which, if code-split, gets confused
    // (would have to re-insert the Parm).
    return null;
  }

  @Override public Type value(GVNGCM.Mode opt_mode) {
    // Not executing?
    Type ctl = val(0);
    if( ctl != Type.CTRL && ctl != Type.ALL ) return ctl.oob();
    Node in0 = in(0);
    if( in0 instanceof ThunkNode ) return val(1);
    if( !(in0 instanceof FunNode) )  return ctl.oob();
    FunNode fun = (FunNode)in0;
    if( fun.len()!=len() ) return Type.ALL; // Collapsing

    // If pre-Call-Graph, assume the value will be exported externally and thus
    // called by the most conservative caller.  The default input already pessimizes.
    if( !opt_mode._CG && fun._java_fun ) {
      //Type tin = _defs._len <= 1 ? _t : val(1);
      //return t0 == Type.ANY ? tin : tin.join(t0);   // No need to visit other inputs
      return _t;
    }

    // Trust the signature, if any.
    TypeFld fld = fun.formals().get(_name);
    Type t0 = fld==null ? Type.ANY : fld._t.simple_ptr();
    if( is_prim() && fld!=null ) return t0;

    // If we have a Call Graph, then we merge all the normal input paths.  If
    // we are also exporting, the export path is lifted by the H-M typing which
    // is not known for a while.  During Opto, treat Leafs as ~Scalars; post
    // Opto no more lifting will occur and Leafs are treated as Scalars.
    Type t = Type.ANY;
    Node mem = fun.parm(MEM_IDX);
    int i=1;
    // Lift the external caller by HM
    if( fun.has_unknown_callers() ) {
      i = 2;
      if( fun.len() > 1 && fun.is_unknown_alive() ) {
        assert fun.in(1) instanceof ScopeNode;
        assert fun.val(1) == Type.CTRL || fun.val(1) == Type.ALL;
        t = fld==null
          ? (mem == null ? val(1) : in(1).sharptr(mem.in(1)))
          : fld._t;              // Use formal signature if available
        if( _tvar != null ) { // Lift if HM is available
          //TV2 tv = tvar();
          //Type ta = tv.as_flow(opt_mode == GVNGCM.Mode.Opto && Combo.HM_IS_HIGH);
          //t = t.join(ta);
          throw unimpl();
        } else { // Else Input memory is the Scope escape-out memory
          if( mem==this && opt_mode._CG )
            t = ((ScopeNode)fun.in(1)).mem()._val;
        }
      }
    }

    // Merge all remaining paths
    for( ; i<_defs._len; i++ ) {
      if( fun.val(i)==Type.XCTRL || fun.val(i)==Type.ANY ) continue; // Only meet alive paths
      // Check arg type, after sharpening
      Type ta = mem == null ? val(i) : in(i).sharptr(mem.in(i));
      t = t.meet(ta);
    }

    if( _idx <= 0 ) return t;
    if( fun.in(0)==fun ) return t.simple_ptr(); // Function is collapsing, memory not available to check formals
    // High, but valid, values like choice-functions need to pass through,
    // so following Calls agree that SOME function will be called.
    // Check against formals; if OOB, always produce an error.
    // Good case: nothing in signature (parm is dead, so legit), type needs to fall, or it isa formal.
    if( fld==null || t.above_center() || t.isa(fld._t) ) return t.simple_ptr();
    return _t;
  }

  // If an input to a Mem Parm changes, the flow results of other Parms can change
  @Override public void add_work_use_extra(WorkNode work, Node chg) {
    if( is_mem() )
      for( Node parm : in(0)._uses )
        if( parm instanceof ParmNode && parm != this )
          work.add(parm);
  }

  // While Parms are mostly Phis (and yes for value flows), during unification
  // Parms are already treated by the H-M algo, and (via fresh_unify) get
  // "fresh" TVars for every input path.
  @Override public boolean unify( WorkNode work ) { return false; }

  // True if loading from a display/closure
  @Override public boolean is_display_ptr() { return _idx==DSP_IDX; }


  @Override public ErrMsg err( boolean fast ) {
    if( !(in(0) instanceof FunNode) ) return null; // Dead, report elsewhere
    FunNode fun = fun();
    if( fun.in(0)== fun ) return null;  // Dead, being inlined
    if( fun.len()!=len() ) return null; // Broken, dying
    if( _idx <= MEM_IDX ) return null;  // No arg check on RPC or memory
    Node mem = fun.parm(MEM_IDX);
    assert _name!=null;
    TypeFld ffld = fun.formals().get(_name);
    if( ffld==null ) return null; // dead display, because loading a high value
    Type formal = ffld._t;
    for( int i=1; i<_defs._len; i++ ) {
      if( fun.val(i)==Type.XCTRL ) continue;// Ignore dead paths
      Type argt = mem == null ? in(i)._val : in(i).sharptr(mem.in(i)); // Arg type for this incoming path
      if( argt!=Type.ALL && !argt.above_center() && !argt.isa(formal) ) { // Argument is legal?  ALL args are in-error elsewhere
        // The merge of all incoming calls for this argument is not legal.
        // Find the call bringing the broken args, and use it for error
        // reporting - it MUST exist, or we have a really weird situation
        for( Node def : fun._defs ) {
          if( def instanceof CProjNode && def.in(0) instanceof CallNode ) {
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
