package com.cliffc.aa.node;

import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;

/** Error nodes.  If any remain in the program after optimization, the program
 *  is not well-typed. */
public final class ErrNode extends Node {
  final ErrMsg _err;
  public ErrNode( Node ctrl, Parse loc, String msg ) { this(ctrl,new ErrMsg(loc,msg,ErrMsg.Level.ErrNode)); }
  public ErrNode( Node ctrl, ErrMsg err ) {
    super(OP_ERR,ctrl);
    _err = err;
    _live= Type.ALL;
  }
  @Override public String xstr() { return _err._msg; }
  @Override String str() { return "Err"; }
  @Override public Node ideal_reduce() {  Node cc = in(0).is_copy(0);  return cc==null ? null : set_def(0,cc); }
  @Override public Type value() {
    Type t = val(0);
    return t == Type.ANY || t == Type.XCTRL ? Type.ANY : Type.ALL; // For dead data errors return ANY (no error)
  }
  @Override public Type live_use( Node def ) { return Type.ALL; }
  @Override public boolean has_tvar() { return true; }
  
  @Override public ErrMsg err( boolean fast ) {
    // While you might think we should ALWAYS report these, as their existence
    // means the program is in-error - the program may have other earlier
    // errors we want to report in preference to this one.  If any user
    // has ANOTHER ALL/Err input, return null instead.
    for( Node use : _uses )
      for( Node def : use._defs )
        if( def != null && def != this && def._val ==Type.ALL )
          return null;
    return _err;
  }
  @Override public int hashCode() { return super.hashCode()+_err.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof ErrNode) ) return false;
    ErrNode err = (ErrNode)o;
    return _err.equals(err._err);
  }
}
