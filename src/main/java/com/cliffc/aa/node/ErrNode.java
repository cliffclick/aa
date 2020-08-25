package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;

/** Error nodes.  If any remain in the program after optimization, the program
 *  is not well-typed. */
public final class ErrNode extends Node {
  final ErrMsg _err;
  public ErrNode( Node ctrl, Parse loc, String msg ) { this(ctrl,new ErrMsg(loc,msg,Level.ErrNode)); }
  public ErrNode( Node ctrl, ErrMsg err ) {
    super(OP_ERR,ctrl);
    _err = err;
    _live= TypeMem.ESCAPE;
  }
  @Override String xstr() { return _err._msg; }
  @Override String str() { return "Err"; }
  @Override public Node ideal(GVNGCM gvn, int level) { return null; }
  @Override public Type value(GVNGCM.Mode opt_mode) {
    Type t = val(0);
    return t == Type.ANY || t == Type.XCTRL ? Type.ANY : Type.ALL; // For dead data errors return ANY (no error)
  }
  @Override public ErrMsg err( boolean fast ) { return _err; }
  @Override public int hashCode() { return super.hashCode()+_err.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof ErrNode) ) return false;
    ErrNode err = (ErrNode)o;
    return _err.equals(err._err);
  }
}
