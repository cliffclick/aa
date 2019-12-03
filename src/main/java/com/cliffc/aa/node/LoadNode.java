package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;

// Load a named field from a struct.  Does it's own nil-check testing.  Loaded
// value depends on the struct typing.
public class LoadNode extends Node {
  private final String _fld;
  private final Parse _bad;
  public LoadNode( Node ctrl, Node mem, Node adr, String fld, Parse bad ) {
    super(OP_LOAD,ctrl,mem,adr);
    _fld = fld;
    _bad = bad;
  }
  String xstr() { return _fld; }   // Self short name
  String  str() { return xstr(); } // Inline short name
  private Node ctl() { return in(0); }
  private Node mem() { return in(1); }
  private Node adr() { return in(2); }
  private Node nil_ctl(GVNGCM gvn) { return set_def(0,null,gvn); }
  private Node set_mem(Node a, GVNGCM gvn) { return set_def(1,a,gvn); }
  private void set_adr(Node a, GVNGCM gvn) { set_def(2,a,gvn); }

  @Override public Node ideal(GVNGCM gvn) {
    Node ctrl = ctl();
    Node mem  = mem();
    Node addr = adr();

    // Load from a single alias bypasses a MemMerge
    Type tadr = gvn.type(addr);
    if( tadr instanceof TypeMemPtr && mem instanceof MemMergeNode ) {
      int alias = ((TypeMemPtr)tadr)._aliases.abit();
      // TODO: Actually if all bits subset a single entry, and no partial
      // subsets, can bypass along the single entry.
      if( alias != -1 ) {       // Single alias?
        // Find nearest alias parent
        Node obj = ((MemMergeNode)mem).alias2node(alias);
        return set_mem(obj,gvn);
      }
    }

    // Loads against a NewNode cannot NPE, cannot fail, always return the input
    NewNode nnn = addr.in(0) instanceof NewNode ? (NewNode)addr.in(0) : null;
    int idx=-1;
    if( nnn != null && nnn == mem.in(0) && (idx=nnn._ts.find(_fld)) != -1 )
      return nnn.fld(idx);      // Field value

    // Load from a memory Phi; split through in an effort to sharpen the memory.
    if( mem instanceof PhiNode && ctrl == null && nnn!=null ) {
      // TODO: Only split thru function args if no unknown_callers, and must make a Parm not a Phi
      if( !(mem instanceof ParmNode) ) {
        Node lphi = new PhiNode(((PhiNode)mem)._badgc,mem.in(0));
        for( int i=1; i<mem._defs._len; i++ )
          lphi.add_def(gvn.xform(new LoadNode(null,mem.in(i),addr,_fld,_bad)));
        return lphi;
      }
    }

    //// Load of final field can bypass call
    //if( idx!=-1 && nnn != null && nnn.is_final(idx) && mem instanceof MProjNode && mem.in(0) instanceof CallEpiNode )
    //  return set_mem(((CallNode)mem.in(0).in(0)).mem(),gvn);

    // Loads against an equal store; cannot NPE since the Store did not.
    StoreNode st;
    if( mem instanceof StoreNode && addr == (st=((StoreNode)mem)).adr() ) {
      if( Util.eq(_fld,st._fld) && st.err(gvn)==null )
        return st.val();
    }

    //// Bypass unrelated Stores
    //if( st != null && st.err(gvn)==null &&
    //    ( st._fld_num != _fld_num || (_fld != null && !_fld.equals(st._fld_num)) ))
    //  return set_mem(st.mem(),gvn);

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

    Type tnz = t.join(TypeMemPtr.OOP); // Remove nil choice
    set_adr(gvn.xform(new CastNode(tru,baseaddr,tnz)),gvn);
    return nil_ctl(gvn);
  }

  @Override public Type value(GVNGCM gvn) {
    Type adr = gvn.type(adr()).base();
    if( adr.isa(TypeMemPtr.OOP0.dual()) ) return Type.XSCALAR;
    if( TypeMemPtr.OOP0.isa(adr) ) return Type.SCALAR; // Very low, might be any address
    if( adr.is_forward_ref() ) return Type.SCALAR;
    if( !(adr instanceof TypeMemPtr) )
      return adr.above_center() ? Type.XSCALAR : Type.SCALAR;
    TypeMemPtr tadr = (TypeMemPtr)adr;
    // Loading from TypeMem - will get a TypeObj out.
    Type mem = gvn.type(mem());     // Memory
    Type badmemrez = mem.above_center() ? Type.XSCALAR : Type.SCALAR;
    if( !(mem instanceof TypeStruct) ) {
      if( !(mem instanceof TypeMem) ) // Nothing sane
        return badmemrez;
      TypeObj obj = ((TypeMem)mem).ld(tadr);
      mem = obj.base();
    }

    // Loading from TypeObj - hoping to get a field out
    if( mem instanceof TypeStruct ) {
      TypeStruct ts = (TypeStruct)mem;
      int idx = ts.find(_fld);  // Find the named field
      if( idx != -1 ) {         // Found a field
        // Nil-check before allowing the load.
        if( tadr.must_nil() ) {
          // Check for nil-check not in the graph, but locally available.
          if( !(ctl() instanceof CProjNode && ((CProjNode)ctl())._idx==1 && ctl().in(0).in(1)==adr()) ) {
            // TODO: Need a type-flow in the graph for cycles...
            return Type.SCALAR; // Not provable not-nil, so fails
          }
        }
        return ts.at(idx); // Field type
      }
      // No such field
    }
    return badmemrez; // No loading from e.g. Strings
  }

  @Override public String err(GVNGCM gvn) {
    Type t = gvn.type(adr()).base();
    if( t.must_nil() ) return bad("Struct might be nil when reading");
    if( !(t instanceof TypeMemPtr) )
      return bad("Unknown"); // Not a pointer, cannot load a field
    TypeMemPtr t3 = (TypeMemPtr)t;
    Type t4 = gvn.type(mem());
    if( t4 instanceof TypeMem ) {         // Memory or Struct, for various errors
      TypeMem t5 = (TypeMem)t4;           // Should be memory
      Type t6 = t5.ld(t3);                // General load from memory
      if( !(t6 instanceof TypeStruct) ) { // No fields, so memory or ptr is in-error
        Type t7 = t3._obj.base();
        if( t7 instanceof TypeStruct ) {
          t4 = t7;
        } else {
          return bad("Unknown");
        }
      } else t4 = t6;
    }
    if( !(t4 instanceof TypeStruct) || ((TypeStruct)t4).find(_fld) == -1 )
      return bad("Unknown");
    return null;
  }
  private String bad( String msg ) {
    String f = msg+" field '."+_fld+"'";
    return _bad==null ? f : _bad.errMsg(f);
  }
  @Override public Type all_type() { return Type.SCALAR; }
  @Override public int hashCode() { return super.hashCode()+_fld.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    return (o instanceof LoadNode) && Util.eq(_fld,((LoadNode)o)._fld);
  }
}
