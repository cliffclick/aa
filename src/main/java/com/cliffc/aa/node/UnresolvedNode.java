package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.*;

/** A collection of functions that can be unambiguously called (no virtual, no
 *  table-lookup) from all call sites.  The arguments have no overlap ("tile"
 *  the argument space), and so once a calls arguments are sufficiently
 *  resolved only a single FunPtr ever applies.
 *
 *  They all have the *same* display in slot 0.
 */
public class UnresolvedNode extends Node {
  public final String _name;   // Name of unresolved function
  private Parse _bad;
  // Unresolved moves through 3-states:
  // - 0 forward-ref; scope is not known; can add_fun
  // - 1 scoped; scope is known; can add_fun
  // - 2 defined; scope is known and complete, no more add_fun.
  // If no inputs, then remains an undefined forward-ref.
  private byte _fref;
  UnresolvedNode( String name, Parse bad ) { super(OP_UNR); _name = name; _bad=bad; _val = TypeFunPtr.GENERIC_FUNPTR; add_def(null); }

  @Override public String xstr() {
    if( is_dead() ) return "DEAD";
    if( _defs._len==0 ) return "???"+_name;
    String s = switch( _fref ) {
    case 0 -> "???";
    case 1 -> "??";
    default -> "?";
    };
    return s+_name;
  }
  UnresolvedNode set_bad(Parse bad) { _bad=bad; return this; }

  @Override public Type value() {
    if( is_forward_ref() ) return TypeFunPtr.GENERIC_FUNPTR;
    Type t = Type.ANY;
    for( int i=1; i<len(); i++ )
      t = t.meet(val(i));
    // If we have a display, then it replaces the input FunPtr displays.
    if( in(0)!=null && t instanceof TypeFunPtr tfp ) {         // Overwrite display
      Type dsp = in(0)._val;
      t = tfp.make_from(dsp,tfp._ret);
    }
    return t;
  }
  @Override public Node ideal_reduce() {
    if( !is_defined() || _defs._len > 2 ) return null;
    // Defined with only 1, remove for a single FunPtr
    // ValNodes stay to keep producing a TFP.
    if( in(0)==null ) return in(1) instanceof FunPtrNode ? in(1) : null;
    // Move the display in slot(0) to the FunPtr before returning it
    throw unimpl();
  }

  // Looks at the fidxs in TFP, and the arguments given and tries to resolve
  // the call.  Returns TFP if it cannot be further resolved.  Must be
  // monotonic, as it is used by CallNode.
  static TypeFunPtr resolve_value( Type[] tcall ) {
    TypeFunPtr tfp = (TypeFunPtr)tcall[tcall.length-1], tfp2=null;
    if( tfp.is_full() ||       // Too low , will not resolve.  Might lift to OK
        tfp.above_center() ||  // Too high, will not resolve.  Might fall to OK
        tfp.is_fidx() )        // Already resolved to single target
      return tfp;
    boolean high = false;       // True if args too high to resolve
    for( int fidx : tfp.fidxs() ) {
      RetNode ret = RetNode.get(fidx);
      if( ret._nargs == tcall.length-1 ) { // Ignore if wrong arg count
        Type actual = tcall[ARG_IDX];      // TODO: Looking at first arg only
        Type formal = ret.formal(ARG_IDX);
        if( actual.isa(formal) ) {
          TypeFunPtr tfp3 = TypeFunPtr.make(fidx,ret._nargs,tcall[DSP_IDX],ret.rez()._val);
          tfp2 = tfp2==null ? tfp3 : (TypeFunPtr)tfp2.meet(tfp3);
          high = actual.above_center();
        }
      }
    }
    if( high ) // Arg types too high, can fall either way
      // Result is high, with choice fidxs, choice ret, but the display is legit
      return tfp.dual().make_from(tfp.dsp(),tfp._ret.dual());
    return tfp2==null ? tfp : tfp2;
  }

  // Looks at this Unresolved and the arg types, and tries to resolve the call.
  // Returns null if no resolve, or a FunPtrNode if resolved.
  FunPtrNode resolve_node( Type[] tcall ) {
    if( !is_defined() ) return null; // More choices to be added later
    FunPtrNode choice=null;
    for( int i=1; i<len(); i++ ) {
      FunPtrNode ptr = (FunPtrNode)in(i);
      if( ptr.nargs()==tcall.length-1 ) {
        Type actual = tcall     [ARG_IDX]; // actual
        Type formal = ptr.formal(ARG_IDX); // formal
        if( actual.isa(formal) &&
            !(actual.getClass()==TypeInt.class && formal.getClass()==TypeFlt.class) ) {
          assert choice == null; // Exactly zero or one fptr resolves
          choice = ptr;          // Resolved choice
          if( in(0)!=null ) {    // Has custom display
            choice = (FunPtrNode)ptr.copy(true);
            choice.set_def(1,in(0));
            choice.xval();
          }
        }
      }
    }
    return choice;
  }

  // An UnresolvedNode is its own Leaf, because it might gather fairly unrelated
  // functions - such as integer-add vs string-add, or the 1-argument leading
  // '+' operator vs the more expected binop.
  @Override public boolean has_tvar() { return true; }

  @Override public boolean unify( boolean test ) {
    // Giant assert that all inputs are all Fun or Val constructors, ignoring errors.
    for( int i=1; i<len(); i++ ) {
      TV3 tv = tvar(i);
      assert tv.is_err() || tv.is_fun() || tv.is_leaf() || tv.is_obj();
    }
    return false;
  }

  // A forward-ref is an assumed unknown-function being used before being
  // declared.  Hence, we want a callable function pointer, but have no defined
  // body (yet).  Make a function pointer that takes/ignores all args, and
  // returns a scalar.
  public static UnresolvedNode forward_ref( String name, Parse unkref ) {
    return new UnresolvedNode(name,unkref);
  }

  // Bind to a display
  UnresolvedNode bind( Node dsp ) {
    assert in(0)==null && dsp._val instanceof TypeMemPtr tmp && tmp.is_valtype();
    return (UnresolvedNode)copy(true).set_def(0,dsp);
  }

  // True if this is a forward_ref
  public boolean is_forward_ref() { return _defs._len==0 || _fref<=1; }
  // One-time flip _fref, no longer a forward ref
  public UnresolvedNode scoped() { assert _fref==0; _fref=1; return this; }
  public UnresolvedNode define() { assert _fref==1; _fref=2; return this; }
  boolean is_scoped () { return _fref==1; }
  boolean is_defined() { return _fref==2; }

  // Add Another function to an Unresolved and return null, or return an ErrMsg
  // if this would add an ambiguous signature.  Different nargs are different.
  // Within functions with the same nargs
  public UnresolvedNode add_fun( FunPtrNode fptr) {
    assert in(0)==null;         // No display if we are adding fptrs
    for( int i=1; i<len(); i++ ) {
      FunPtrNode f0 = (FunPtrNode)in(i);
      if( f0.nargs()==fptr.nargs() ) {
        assert f0.formal(DSP_IDX) == fptr.formal(DSP_IDX); // Same displays
        Type t0a = f0  .formal(ARG_IDX);  // f0   arg type
        Type tfa = fptr.formal(ARG_IDX);  // fptr arg type
        if( t0a.isa(tfa) || tfa.isa(t0a) ) // First arg is neither isa the other
          throw unimpl();       // Check ambiguous against all other signatures
      }
    }
    add_def(fptr);
    Env.GVN.add_flow_uses(this); // Some calls can resolve
    return this;
  }

  @Override public int hashCode() { return super.hashCode()+(_bad==null ? 0 : _bad.hashCode()); }
  @Override public boolean equals(Object o) {
    if( !super.equals(o) ) return false;
    return _bad==((UnresolvedNode)o)._bad;
  }
  // Make a copy with an error message
  public UnresolvedNode copy(Parse bad) {
    //return new UnresolvedNode(bad,Arrays.copyOf(_defs._es,_defs._len));
    throw unimpl();
  }

  // Assigning the forward-ref removes the error
  @Override public ErrMsg err( boolean fast ) {
    if( is_defined() )
      return ErrMsg.unresolved(_bad,"Unable to resolve "+_name); // Ambiguous, should have resolved
    return ErrMsg.forward_ref(_bad,_name);
  }

}
