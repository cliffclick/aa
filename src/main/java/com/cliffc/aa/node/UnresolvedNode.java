package com.cliffc.aa.node;

import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFunPtr;

import static com.cliffc.aa.AA.unimpl;

/** A collection of functions that can be unambiguously called (no virtual, no
 *  table-lookup) from all call sites.  The arguments have no overlap ("tile"
 *  the argument space), and so once a calls arguments are sufficiently
 *  resolved only a single FunPtr ever applies.
 *
 *
 */
public class UnresolvedNode extends Node {
  private final String _name;   // Name of unresolved function
  private final Parse _bad;
  // Unresolved moves through 3-states:
  // - 0 forward-ref; scope is not known; can add_fun
  // - 1 scoped; scope is known; can add_fun
  // - 2 defined; scope is known and complete, no more add_fun.
  // If no inputs, then remains an undefined forward-ref.
  private byte _fref;
  UnresolvedNode( String name, Parse bad ) { super(OP_UNR); _name = name; _bad=bad; }
  @Override public String xstr() {
    if( is_dead() ) return "DEAD";
    if( _defs._len==0 ) return "???"+_name;
    String s = switch( _fref ) {
    case 0 -> "???";
    case 1 -> "?";
    default -> "";
    };
    return s+_name;
  }
  @Override public Node ideal_reduce() {
    // Defined with only 1, nuke it
    return is_defined() && _defs._len == 1 ? in(0) : null;
  }

  @Override public Type value() {
    if( is_forward_ref() ) return Type.ALL;
    Type t = Type.ANY;
    for( Node fptr : _defs )
      t = t.meet(fptr._val);
    return t;
  }

  // Look at the arguments and resolve the call, if possible.
  FunPtrNode resolve_value( Type[] tcall) {
    FunPtrNode x=null;
    for( Node n : _defs ) {
      FunPtrNode ptr = (FunPtrNode)n;
      if( ptr.nargs()==tcall.length-1 ) {
        assert x==null;         // Exactly zero or one fptr resolves
        x=ptr;
      }
    }
    return x;
  }


  // An UnresolvedNode is its own Leaf, because it might gather fairly unrelated
  // functions - such as integer-add vs string-add, or the 1-argument leading
  // '+' operator vs the more expected binop.
  @Override public boolean unify( boolean test ) {
    // Giant assert that all inputs are all Fun, ignoring errors.
    for( Node n : _defs ) {
      TV2 tv = n.tvar();
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
  boolean is_scoped() { return _fref==1; }
  boolean is_defined() { return _fref==2; }

  // Add Another function to an Unresolved and return null, or return an ErrMsg
  // if this would add an ambiguous signature.
  public ErrMsg add_fun(FunPtrNode fun) {
    for( Node n : _defs )
      if( ((FunPtrNode)n).nargs()==fun.nargs() )
        throw unimpl();         // Check ambiguous against all other signatures
    add_def(fun);
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
