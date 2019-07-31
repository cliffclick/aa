package com.cliffc.aa.node;

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
  private Node ctl() { return in(0); }
  private Node mem() { return in(1); }
  private Node adr() { return in(2); }
  private Node nil_ctl(GVNGCM gvn) { return set_def(0,null,gvn); }
  private void set_adr(Node a, GVNGCM gvn) { set_def(2,a,gvn); }

  @Override public Node ideal(GVNGCM gvn) {
    Node ctrl = ctl();
    Node addr = adr();
    if( ctrl==null || gvn.type(ctrl)!=Type.CTRL )
      return null;              // Dead load, or a no-control-no-fail load
    if( addr.is_forward_ref() ) return null;
    Type t = gvn.type(addr);    // Address type

    // Lift control on Loads as high as possible... and move them over
    // to a CastNode (to remove nil-ness) and remove the control.
    if( !t.must_nil() ) // No nil, no need for ctrl
      // remove ctrl; address already casts-away-nil
      return nil_ctl(gvn);

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

    if( !(t instanceof TypeMemPtr) )
      return null; // below a nil (e.g. Scalar), do nothing yet
    Type tnz = t.join(TypeMemPtr.OOP); // Remove nil choice
    set_adr(gvn.xform(new CastNode(tru,baseaddr,tnz)),gvn);
    return nil_ctl(gvn);
  }

  @Override public Type value(GVNGCM gvn) {
    Type adr = gvn.type(adr()).base();
    if( adr.isa(TypeMemPtr.OOP0.dual()) ) return Type.XSCALAR;
    if( adr.must_nil() ) return Type.SCALAR; // Not provable not-nil, so fails
    if( TypeMemPtr.OOP0.isa(adr) ) return Type.SCALAR; // Very low, might be any address
    if( adr.is_forward_ref() ) return Type.SCALAR;
    if( !(adr instanceof TypeMemPtr) )
      return adr.above_center() ? Type.XSCALAR : Type.SCALAR;

    Type mem = gvn.type(mem());     // Memory
    if( !(mem instanceof TypeMem) ) // Nothing sane
      return mem.above_center() ? Type.XSCALAR : Type.SCALAR;
    TypeObj obj = ((TypeMem)mem).ld((TypeMemPtr)adr);
    Type base = obj.base();

    if( base instanceof TypeStruct ) {
      TypeStruct ts = (TypeStruct)base;
      int idx = ts.find(_fld,_fld_num);  // Find the named field
      if( idx != -1 ) return ts.at(idx); // Field type
      // No such field
      return base.above_center() ? Type.XSCALAR : Type.SCALAR;
    }
    return Type.SCALAR;        // No loading from e.g. Strings
  }

  @Override public String err(GVNGCM gvn) {
    Type t = gvn.type(adr());
    while( t instanceof TypeName ) t = ((TypeName)t)._t;
    if( t.must_nil() ) return _badnil;
    if( !(t instanceof TypeMemPtr) )
      return _badfld; // Not a pointer, cannot load a field
    TypeMemPtr t3 = (TypeMemPtr)t;
    TypeMem t4 = (TypeMem)gvn.type(mem()); // Should be memory
    Type t5 = t4.ld(t3);                   // Meets of all aliases
    if( !(t5 instanceof TypeStruct) ) {    // No fields, so memory or ptr is in-error
      Type t6 = t3._obj.base();
      if( t6 instanceof TypeStruct ) {
        t5 = t6;
      } else {
        return _badfld;
      }
    }
    if( ((TypeStruct)t5).find(_fld,_fld_num) == -1 )
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
