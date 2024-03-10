package com.cliffc.aa;

import com.cliffc.aa.node.FunPtrNode;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeStruct;
import com.cliffc.aa.util.SB;

// Error messages
public class ErrMsg implements Comparable<ErrMsg> {

  // Error levels
  public enum Level {
    Syntax,                   // Syntax
    ForwardRef,               // Forward refs
    ErrNode,                  // ErrNodes
    Assert,                   // Assert type errors
    Field,                    // Field naming errors
    UnresolvedCall,           // Unresolved calls
    TypeErr,                  // Type errors
    NilAdr,                   // Address might be nil on mem op
    BadArgs,                  // Unspecified primitive bad args
    AllTypeErr,               // Type errors, with one of the types All
    TrailingJunk,             // Trailing syntax junk
    MixedPrimGC,              // Mixed primitives & GC
  }


  public       Parse _loc;    // Point in code to blame
  public final String _msg;   // Printable error message, minus code context
  public final Level _lvl;    // Priority for printing
  public int _order;          // Message order as they are found.
  public static final ErrMsg FAST = new ErrMsg(null,"fast",Level.Syntax);
  public static final ErrMsg BADARGS = new ErrMsg(null,"bad arguments",Level.BadArgs);
  public ErrMsg(Parse loc, String msg, Level lvl) { _loc=loc; _msg=msg; _lvl=lvl; }
  public static ErrMsg forward_ref(Parse loc, FunPtrNode fun) { return forward_ref(loc,fun._name); }
  public static ErrMsg forward_ref(Parse loc, String name) {
    return new ErrMsg(loc,"Unknown ref '"+name+"'",Level.ForwardRef);
  }
  public static ErrMsg syntax(Parse loc, String msg) {
    return new ErrMsg(loc,msg,Level.Syntax);
  }
  public static ErrMsg unresolved(Parse loc, String msg) {
    return new ErrMsg(loc,msg,Level.UnresolvedCall);
  }
  public static ErrMsg typerr( Parse loc, Type actual, Type expected ) { return typerr(loc,actual, expected,Level.TypeErr); }
  public static ErrMsg typerr( Parse loc, Type actual, Type expected, Level lvl ) {
    Type.PENV P = new Type.PENV(false,false,false);
    actual  ._str_dups(P);
    expected._str_dups(P);
    actual  ._str(P).p(" is not a ");
    expected._str(P);
    if( actual==Type.ALL && lvl==Level.TypeErr ) lvl=Level.AllTypeErr; // ALLs have failed earlier, so this is a lower priority error report
    return new ErrMsg(loc,P.sb.toString(),lvl);
  }
  public static ErrMsg typerr2( Parse loc, Type actual, Type[] expecteds ) {
    Type.PENV P = new Type.PENV(false,false,false);
    actual._str_dups(P);
    for( Type expect : expecteds ) expect._str_dups(P);
    actual._str(P);
    P.p( expecteds.length==1 ? " is not a " : " is none of (");
    for( Type expect : expecteds ) expect._str(P).p(',');
    P.sb.unchar().p(expecteds.length==1 ? "" : ")");
    return new ErrMsg(loc,P.sb.toString(),Level.TypeErr);
  }
  public static ErrMsg asserterr( Parse loc, Type actual, Type expected ) {
    return typerr(loc,actual, expected,Level.Assert);
  }
  public static ErrMsg field(Parse loc, String msg, String fld, boolean closure, TypeStruct ts) {
    Type.PENV P = new Type.PENV();
    if( ts != null && !closure ) ts._str_dups(P);
    P.sb.p(msg).p(Parse.isOp(fld) ? " operator '" : (closure ? " val '" : " field '.")).p(fld).p("'");
    if( ts != null && !closure ) ts._str(P.p(" in "));
    return new ErrMsg(loc,P.sb.toString(),Level.Field);
  }
  public static ErrMsg niladr(Parse loc, String msg, String fld) {
    String f = fld==null ? msg : msg+" field '."+fld+"'";
    return new ErrMsg(loc,f,Level.NilAdr);
  }
  public static ErrMsg badGC(Parse loc) {
    return new ErrMsg(loc,"Cannot mix GC and non-GC types",Level.MixedPrimGC);
  }
  public static ErrMsg trailingjunk(Parse loc) {
    return new ErrMsg(loc,"Syntax error; trailing junk",Level.TrailingJunk);
  }

  @Override public String toString() {
    return _loc==null ? _msg : _loc.errLocMsg(_msg);
  }
  @Override public int compareTo(ErrMsg msg) {
    int cmp = _lvl.compareTo(msg._lvl);
    if( cmp != 0 ) return cmp;
    return _order - msg._order;
    //cmp = _loc.compareTo(msg._loc);
    //if( cmp != 0 ) return cmp;
    //return _msg.compareTo(msg._msg);
  }
  @Override public boolean equals(Object obj) {
    if( this==obj ) return true;
    if( !(obj instanceof ErrMsg err) ) return false;
    if( _lvl!=err._lvl || !_msg.equals(err._msg) ) return false;
    // Spread a missing loc; cheaty but only a little bit.
    // TODO: track down missing loc in Parser
    if( _loc==null && err._loc!=null ) _loc=err._loc;
    if( _loc!=null && err._loc==null ) err._loc=_loc;
    return _loc==err._loc || _loc.equals(err._loc);
  }
  @Override public int hashCode() {
    return (_loc==null ? 0 : _loc.hashCode())+_msg.hashCode()+_lvl.hashCode();
  }
}
