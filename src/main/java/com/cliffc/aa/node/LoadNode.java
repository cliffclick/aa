package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

// Load a named field from a struct.  Does it's own nil-check testing.  Loaded
// value depends on the struct typing.
public class LoadNode extends Node {
  private final String _fld;
  private final int _fld_num;
  private final String _badfld;
  private final String _badnil;
  private LoadNode( Node ctrl, Node mem, Node adr, String fld, int fld_num, Parse bad ) {
    super(OP_LOAD,ctrl,mem,adr);
    _fld = fld;
    _fld_num = fld_num;
    // Tests can pass a null, but nobody else does
    _badfld = bad==null ? null : bad.errMsg("Unknown field '."+fld+"'");
    _badnil = bad==null ? null : bad.errMsg("Struct might be nil when reading field '."+fld+"'");
  }
  public LoadNode( Node ctrl, Node mem, Node adr, String fld , Parse bad ) { this(ctrl,mem,adr,fld,-1,bad); }
  public LoadNode( Node ctrl, Node mem, Node adr, int fld_num, Parse bad ) { this(ctrl,mem,adr,null,fld_num,bad); }
  String xstr() { return "."+(_fld==null ? ""+_fld_num : _fld); } // Self short name
  String  str() { return xstr(); }      // Inline short name
  Node ctl() { return in(0); }
  Node mem() { return in(1); }
  Node adr() { return in(2); }
  Node set_ctl(Node c, GVNGCM gvn) { return set_def(0,c,gvn); }
  Node set_mem(Node m, GVNGCM gvn) { return set_def(1,m,gvn); }
  Node set_adr(Node a, GVNGCM gvn) { return set_def(2,a,gvn); }
  
  @Override public Node ideal(GVNGCM gvn) {
    Node ctrl = ctl();
    Node addr = adr();
    if( ctrl==null || gvn.type(ctrl)!=Type.CTRL )
      return null;              // Dead load, or a no-control-no-fail load
    Type t = gvn.type(addr);    // Address type
    if( t.is_forward_ref() ) return null;

    // Lift control on Loads as high as possible... and move them over
    // to a CastNode (to remove nil-ness) and remove the control.
    if( !TypeNil.NIL.isa(t) ) // No nil, no need for ctrl
      // remove ctrl; address already casts-away-nil
      return set_ctl(null,gvn);

    // Looking for a nil-check pattern:
    //   this.0->dom*->True->If->addr
    //   this.1->[Cast]*-------/   Cast(s) are optional
    // If found, convert to this pattern:
    //   this.0      ->True->If->addr
    //   this.1->Cast/---------/
    // Where the cast-away-nil is local and explicit
    Node baseaddr = addr;
    while( baseaddr instanceof CastNode ) baseaddr = baseaddr.in(1);
    final Node fbaseaddr = baseaddr;

    Node tru = ctrl.walk_dom_last(n ->
                                  n instanceof CProjNode && ((CProjNode)n)._idx==1 &&
                                  n.in(0) instanceof IfNode &&
                                  n.in(0).in(1) == fbaseaddr );
    if( tru==null ) return null;
    assert !(tru==ctrl && addr != baseaddr) : "not the immediate location or we would be not-nil already";

    if( !(t instanceof TypeNil) )
      return null; // below a nil (e.g. Scalar), do nothing yet
    set_adr(gvn.xform(new CastNode(tru,baseaddr,((TypeNil)t)._t)),gvn);
    return set_ctl(null,gvn);
  }

  @Override public Type value(GVNGCM gvn) {
    Type t = gvn.type(adr()).base();
    if( t.isa(TypeNil.XOOP) ) return Type.XSCALAR; // Very high address; might fall to any valid value
    if( t.isa(TypeMemPtr.MEMPTR.dual()) ) return Type.XSCALAR; // Very high address; might fall to any valid value
    if( t instanceof TypeNil ) {
      if( !t.above_center() )     // NIL or below?
        return Type.SCALAR;       // Fails - might be nil at runtime
      t = ((TypeNil)t)._t.base(); // Assume guarded by test
    }

    //if( t instanceof TypeStruct ) {
    //  TypeStruct ts = (TypeStruct)t;
    //  int idx = find(ts);       // Find the named field
    //  if( idx != -1 ) return ts.at(idx); // Field type
    //}
    //
    //return Type.SCALAR;
    throw AA.unimpl();
  }

  private int find(TypeStruct ts) {
    if( _fld == null ) { // No fields, i.e. a tuple?
      if( _fld_num < ts._ts.length ) // Range-check tuple
        return _fld_num; // Return nth tuple field
      else
        throw AA.unimpl();
    } else return ts.find(_fld);  // Find the named field
  }

  @Override public String err(GVNGCM gvn) {
    Type t = gvn.type(adr());
    while( t instanceof TypeName ) t = ((TypeName)t)._t;
    if( t instanceof TypeNil && !t.above_center() ) return _badnil;
    Type t2 = t instanceof TypeNil ? ((TypeNil)t)._t : t; // Strip off the nil
    //if( TypeOop.OOP.isa(t) ) return _badfld; // Too low, might not have any fields
    if( !(t2 instanceof TypeMemPtr) ) return _badfld; // Not a pointer, cannot load a field
    TypeMemPtr t3 = (TypeMemPtr)t2; 
    TypeMem t4 = (TypeMem)gvn.type(mem()); // Should be memory
    Type t5 = t4.ld(t3); // Meets of all aliases
    throw AA.unimpl();
    //if( !(t instanceof TypeStruct) ) return _badfld;
    //if( find((TypeStruct)t) == -1 )
    //  return _badfld;
    //return null;
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
