package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

// Load a named field from a struct.  Does it's own null-check testing.  Loaded
// value depends on the struct typing.
public class LoadNode extends Node {
  private final String _fld;
  private final int _fld_num;
  private final String _badfld;
  private final String _badnil;
  private LoadNode( Node ctrl, Node st, String fld, int fld_num, Parse bad ) {
    super(OP_LOAD,ctrl,st);
    _fld = fld;
    _fld_num = fld_num;
    _badfld = bad.errMsg("Unknown field '."+fld+"'");
    _badnil = bad.errMsg("Struct might be nil when reading field '."+fld+"'");
  }
  public LoadNode( Node ctrl, Node st, String fld , Parse bad ) { this(ctrl,st,fld,-1,bad); }
  public LoadNode( Node ctrl, Node st, int fld_num, Parse bad ) { this(ctrl,st,null,fld_num,bad); }
  String xstr() { return "."+(_fld==null ? ""+_fld_num : _fld); } // Self short name
  String  str() { return xstr(); }      // Inline short name
  @Override public Node ideal(GVNGCM gvn) {
    Node ctrl = in(0);
    Node addr = in(1);
    if( ctrl==null || gvn.type(ctrl)!=Type.CTRL )
      return null;              // Dead load, or a no-control-no-fail load
    Type t = gvn.type(addr);    // Address type

    // Lift control on Loads as high as possible... and move them over
    // to a CastNode (to remove null-ness) and remove the control.
    if( !TypeNil.NIL.isa(t) ) // No null, no need for ctrl
      // remove ctrl; address already casts-away-null
      return set_def(0,null,gvn);

    // Looking for a null-check pattern:
    //   this.0->dom*->True->If->addr
    //   this.1->[Cast]*-------/   Cast(s) are optional
    // If found, convert to this pattern:
    //   this.0      ->True->If->addr
    //   this.1->Cast/---------/
    // Where the cast-away-null is local and explicit
    Node baseaddr = addr;
    while( baseaddr instanceof CastNode ) baseaddr = baseaddr.in(1);
    final Node fbaseaddr = baseaddr;

    Node tru = ctrl.walk_dom_last(n ->
                                  n instanceof CProjNode && ((CProjNode)n)._idx==1 &&
                                  n.in(0) instanceof IfNode &&
                                  n.in(0).in(1) == fbaseaddr );
    if( tru==null ) return null;
    assert !(tru==ctrl && addr != baseaddr) : "not the immediate location or we would be not-null already";

    if( !(t instanceof TypeNil) )
      return null; // below a nil (e.g. Scalar), do nothing yet
    set_def(1,gvn.xform(new CastNode(tru,baseaddr,((TypeNil)t)._t)),gvn);
    return set_def(0,null,gvn);
  }
  @Override public Type value(GVNGCM gvn) {
    Type t = gvn.type(in(1)).base();
    if( t.isa(TypeNil.XOOP) ) return Type.XSCALAR; // Very high address; might fall to any valid value
    if( TypeOop.OOP.isa(t) ) return Type.SCALAR;   // Too low, might not have any fields
    if( t.is_forward_ref() ) return Type.SCALAR;   // Not yet defined, might fail
    boolean needs_nil_check=false;
    if( t instanceof TypeNil ) {
      if( t==TypeNil.NIL ) return Type.SCALAR;     // Must fail
      if( !t.above_center() ) needs_nil_check=true;// Above_center might fall to no-nil
      t = ((TypeNil)t)._t.base();                  // Assume guarded by test
    }

    if( t instanceof TypeStruct ) {
      TypeStruct ts = (TypeStruct)t;
      int idx = find(ts);       // Find the named field
      if( idx == -1 ) return Type.SCALAR;
      if( needs_nil_check )
        return gvn.self_type(this);
      return ts.at(idx);        // Field type
    }
    
    throw AA.unimpl();
  }
  private int find(TypeStruct ts) {
    if( _fld == null ) {
      if( _fld_num < ts._ts.length )
        return _fld_num;
      else
        throw AA.unimpl();
    } else return ts.find(_fld);  // Find the named field
  }
  @Override public String err(GVNGCM gvn) {
    Type t = gvn.type(in(1));
    while( t instanceof TypeName ) t = ((TypeName)t)._t;
    if( t instanceof TypeNil && !t.above_center() ) return _badnil;
    if( TypeOop.OOP.isa(t) ) return _badfld; // Too low, might not have any fields
    if( t instanceof TypeStruct &&
        find((TypeStruct)t) == -1 )
      return _badfld;
    return null;
  }
  @Override public Type all_type() { return Type.SCALAR; }
  @Override public int hashCode() { return super.hashCode()+(_fld==null ? _fld_num : _fld.hashCode()); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof LoadNode) ) return false;
    LoadNode ld = (LoadNode)o;
    return _fld_num == ld._fld_num && (_fld==null ? ld._fld==null : _fld.equals(ld._fld));
  }
}
