package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV2;
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
  private final Parse _bad;
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
  @Override public Node ideal_reduce() {
    if( !is_defined() || _defs._len > 2 ) return null;
    // Defined with only 1, remove for a single FunPtr
    // ValNodes stay to keep producing a TFP.
    if( in(0)==null ) return in(1) instanceof FunPtrNode ? in(1) : null;
    // Move the display in slot(0) to the FunPtr before returning it
    throw unimpl();
  }

  @Override public Type value() {
    if( is_forward_ref() ) return TypeFunPtr.GENERIC_FUNPTR;
    Type t = Type.ANY;
    for( int i=1; i<len(); i++ ) {
      TypeFunPtr tf = ValFunNode.as_tfp(val(i));
      t = t.meet(tf);
    }
    // If we have a display, then it replaces the input FunPtr displays.
    if( in(0)!=null ) {         // Overwrite display
      TypeMemPtr dsp = (TypeMemPtr)in(0)._val;
      t = ((TypeFunPtr) t).make_from(dsp);
    }
    return t;
  }

  // Look at the arguments and resolve the call, if possible.
  // Returns null if not resolvable (yet).
  // MUST resolve during Combo/GCP, or program has ambiguous calls.
  //ValFunNode resolve_value( Type[] tcall) {
  //  ValFunNode x=null;
  //  for( int i=1; i<len(); i++ ) {
  //    ValFunNode ptr = (ValFunNode)in(i);
  //    if( ptr.nargs()==tcall.length-1 ) {
  //      Type formal = ptr.arg(ARG_IDX)._val;// formal
  //      Type actual = tcall  [ARG_IDX];     // actual
  //      if( actual.isa(formal) ) {
  //        assert x == null;      // Exactly zero or one fptr resolves
  //        x = ptr;               // Resolved choice
  //        if( in(0)!=null )      // Instance call: pre-bind 'self' from slot 0
  //          throw unimpl(); //x = ((TypeFunPtr)ptr._val).make_from((TypeMemPtr)in(0)._val);
  //      }
  //    }
  //  }
  //  return x;
  //}

  // Looks at the fidxs in TFP, and the arguments given and tries to resolve
  // the call.  Returns TFP if it cannot be further resolved.
  static TypeFunPtr resolve_value( Type[] tcall ) {
    ValFunNode choice=null;
    TypeFunPtr tfp = (TypeFunPtr)tcall[tcall.length-1];
    if( tfp._fidxs==BitsFun.FULL ) return tfp;
    if( tfp._fidxs.abit() != -1 ) return tfp;
    for( int fidx : tfp._fidxs ) {
      ValFunNode vfn = ValFunNode.get(fidx);
      if( vfn.nargs() == tcall.length-1 ) {
        Type formal = vfn.formal(ARG_IDX);
        Type actual = tcall[ARG_IDX];
        if( actual.isa(formal) ) {
          assert choice == null; // Exactly zero or one fptr resolves
          choice = vfn;          // Resolved choice
          tfp = ((TypeFunPtr)vfn._val).make_from((TypeMemPtr)tcall[DSP_IDX]);
        }
      }
    }
    return tfp;
  }

  // Looks at this Unresolved and the arg types, and tries to resolve the call.
  // Returns null if no resolve, or a ValFunNode if resolved.
  ValFunNode resolve_node( Type[] tcall ) {
    ValFunNode choice=null;
    for( int i=1; i<len(); i++ ) {
      ValFunNode ptr = (ValFunNode)in(i);
      if( ptr.nargs()==tcall.length-1 ) {
        Type formal = ptr.formal(ARG_IDX); // formal
        Type actual = tcall     [ARG_IDX]; // actual
        if( actual.isa(formal) ) {
          assert choice == null; // Exactly zero or one fptr resolves
          choice = ptr;          // Resolved choice
          if( in(0)!=null ) {    // Has custom display
            assert ptr instanceof FunPtrNode;
            choice = (FunPtrNode)ptr.copy(true);
            choice.set_def(1,in(0));
            choice.xval();
          }
        }
      }
    }
    return choice;
  }


  // Bind to a display
  UnresolvedNode bind( Node dsp ) {
    assert in(0)==null && ((TypeMemPtr)dsp._val)._obj._name.length()>0;
    return (UnresolvedNode)copy(true).set_def(0,dsp);
  }


  // An UnresolvedNode is its own Leaf, because it might gather fairly unrelated
  // functions - such as integer-add vs string-add, or the 1-argument leading
  // '+' operator vs the more expected binop.
  @Override public boolean unify( boolean test ) {
    // Giant assert that all inputs are all Fun, ignoring errors.
    for( int i=1; i<len(); i++ ) {
      TV2 tv = in(i).tvar();
      assert tv.is_err() || tv.is_fun() || tv.is_leaf();
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
  public ErrMsg add_fun(ValFunNode fptr) {
    assert in(0)==null;         // No display if we are adding fptrs
    for( int i=1; i<len(); i++ ) {
      ValFunNode f0 = (ValFunNode)in(i);
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
    return null;
  }

  // Return the op_prec of the returned value.  Not sensible except when called
  // on primitives.  Should be the same across all defs.
  @Override public byte op_prec() { return _defs.at(0).op_prec(); }
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
    throw unimpl();
  }

}
