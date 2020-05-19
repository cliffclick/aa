package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;

// Load a named field from a struct.  Does it's own nil-check testing.  Loaded
// value depends on the struct typing.
public class LoadNode extends Node {
  private final String _fld;
  private final Parse _bad;
  // TRUE if either the address or value must be a TFP.
  // Address: means loading from a closure.
  // Value  : means loading      a closure.
  // Both: this is a linked-list display walk, finding the closure at the proper lexical depth.
  // Just address: this is loading a local variable at this closure.
  // Neither: this is a normal field load from a non-closure structure.
  // Just value: not allowed.
  private final boolean _closure_adr, _closure_val;
  public LoadNode( Node mem, Node adr, String fld, Parse bad ) { this(mem,adr,fld,bad,false,false); }
  public LoadNode( Node mem, Node adr, String fld, Parse bad, boolean closure_adr, boolean closure_val ) {
    super(OP_LOAD,null,mem,adr);
    _fld = fld;
    _bad = bad;
    assert (closure_adr || !closure_val); // Just value: not allowed
    _closure_adr = closure_adr;
    _closure_val = closure_val;
  }
  String xstr() { return "."+_fld; }   // Self short name
  String  str() { return xstr(); } // Inline short name
  private Node mem() { return in(1); }
          Node adr() { return in(2); }
  private Node set_mem(Node a, GVNGCM gvn) { return set_def(1,a,gvn); }

  @Override public Node ideal(GVNGCM gvn, int level) {
    Node mem  = mem();
    Node adr = adr();

    Type tadr = gvn.type(adr);
    BitsAlias aliases = tadr instanceof TypeMemPtr ? ((TypeMemPtr)tadr)._aliases : null;
    int alias = aliases == null ? -2 : aliases.strip_nil().abit();

    // Load from a single alias bypasses a MemMerge
    if( alias >= 0 && mem instanceof MemMergeNode ) {
      // TODO: Actually if all bits subset a single entry, and no partial
      // subsets, can bypass along the single entry.
      // Find nearest alias parent
      Node obj = ((MemMergeNode)mem).alias2node_precise(alias);
      if( obj != null ) return set_mem(obj,gvn);
    }

    // Load can move out of a Call, if the function has no Parm:mem - happens
    // for single target calls that do not (have not yet) inlined.
    CallNode call;
    if( mem instanceof MProjNode && mem.in(0) instanceof CallNode && !(call=(CallNode)mem.in(0)).is_copy() )
      return set_mem(call.mem(),gvn);

    // Loads from unescape memory can bypass calls
    if( adr instanceof  ProjNode && adr.in(0) instanceof NewNode && ((NewNode)adr.in(0))._no_escape &&
        mem instanceof MProjNode && mem.in(0) instanceof CallEpiNode )
      return set_mem(((CallEpiNode)mem.in(0)).call().mem(),gvn);
    
    // Loads against a NewNode cannot NPE, cannot fail, always return the input
    NewObjNode nnn = adr.in(0) instanceof NewObjNode ? (NewObjNode)adr.in(0) : null;
    int idx;
    if( nnn != null && nnn == mem.in(0) && (idx=nnn._ts.find(_fld)) != -1 )
      return nnn.fld(idx);      // Field value

    // Load from a memory Phi; split through in an effort to sharpen the memory.
    if( mem instanceof PhiNode && nnn!=null ) {
      // TODO: Only split thru function args if no unknown_callers, and must make a Parm not a Phi
      if( !(mem instanceof ParmNode) ) {
        Node lphi = new PhiNode(Type.SCALAR,((PhiNode)mem)._badgc,mem.in(0));
        for( int i=1; i<mem._defs._len; i++ )
          lphi.add_def(gvn.xform(new LoadNode(mem.in(i),adr,_fld,_bad)));
        return lphi;
      }
    }

    // Loads against an equal store; cannot NPE since the Store did not.
    StoreNode st=null;
    if( mem instanceof StoreNode && adr == (st=((StoreNode)mem)).adr() ) {
      if( Util.eq(_fld,st._fld) && st.err(gvn)==null )
        return st.val();
    }

    // Bypass unrelated Stores.  Since unrelated, can bypass in-error stores.
    if( st != null && !Util.eq(_fld,st._fld) )
      return set_mem(st.mem(),gvn);
    return null;
  }

  @Override public Type value(GVNGCM gvn) {
    Type adr = gvn.type(adr());
    if( adr.isa(TypeMemPtr.OOP0.dual()) ) return Type.XSCALAR;
    if( TypeMemPtr.OOP0.isa(adr) ) return Type.SCALAR; // Very low, might be any address
    if( adr.is_forward_ref() ) return Type.SCALAR;
    if( !(adr instanceof TypeMemPtr) )
      return adr.above_center() ? Type.XSCALAR : Type.SCALAR;
    TypeMemPtr tmp = (TypeMemPtr)adr;

    // Loading from TypeMem - will get a TypeObj out.
    Node mem = mem();
    Type tmem = gvn.type(mem); // Memory
    if( !(tmem instanceof TypeStruct) ) {
      if( !(tmem instanceof TypeMem) ) // Nothing sane
        return tmem.above_center() ? Type.XSCALAR : Type.SCALAR;
      tmem = ((TypeMem)tmem).ld(tmp);
    }

    // Loading from TypeObj - hoping to get a field out
    if( tmem == TypeObj.XOBJ ) return Type.XSCALAR;
    if( tmem == TypeObj. OBJ ) return Type. SCALAR;
    // Struct; check for field
    if( tmem instanceof TypeStruct ) {
      TypeStruct ts = (TypeStruct)tmem;
      int idx = ts.find(_fld);  // Find the named field
      if( idx != -1 ) {         // Found a field
        Type t = ts.at(idx);
        if( tmp.must_nil() )    // Might be in-error, but might fall to correct
          return t.widen();     // Return conservative but sane answer
        return t;               // Field type
      }
      // No such field
    }
    return tmem.above_center() ? Type.XSCALAR : Type.SCALAR; // No loading from e.g. Strings
  }

  @Override public TypeMem live_use( GVNGCM gvn, Node def ) {
    if( _live == TypeMem.DEAD ) return TypeMem.DEAD; // Am dead, so nothing extra is alive.
    Type tmem = gvn.type(mem());
    Type tptr = gvn.type(adr());
    // If either is above-center, then only basic-liveness - the load can load
    // from anything getting anything.
    if( tmem.above_center() || tptr.above_center() )
      return _live==TypeMem.DEAD ? TypeMem.DEAD : (mem()==def ? TypeMem.UNUSED : TypeMem.EMPTY);
    // TypeObj memory is already alias-constricted.  Can only demand from that alias.
    if( tmem instanceof TypeObj && tptr instanceof TypeMemPtr )
      return TypeMem.make(((TypeMemPtr)tptr)._aliases,(TypeObj)tmem);
    // Alive (like normal liveness), plus the address, plus whatever can be
    // reached from the address.
    return ScopeNode.compute_live_mem(gvn,TypeMem.UNUSED,mem(),adr());
  }

  @Override public String err(GVNGCM gvn) {
    Type tadr = gvn.type(adr());
    if( tadr.must_nil() ) return bad("Struct might be nil when reading");
    if( !(tadr instanceof TypeMemPtr) )
      return bad("Unknown"); // Not a pointer nor memory, cannot load a field
    TypeMemPtr ptr = (TypeMemPtr)tadr;
    Type tmem = gvn.type(mem());
    TypeObj objs = tmem instanceof TypeMem
      ? ((TypeMem)tmem).ld(ptr) // General load from memory
      : ((TypeObj)tmem);
    if( !(objs instanceof TypeStruct) || ((TypeStruct)objs).find(_fld) == -1 )
      return bad("Unknown");
    return null;
  }
  private String bad( String msg ) {
    String f = msg+" field '."+_fld+"'";
    return _bad==null ? f : _bad.errMsg(f);
  }
  @Override public int hashCode() { return super.hashCode()+_fld.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    return (o instanceof LoadNode) && Util.eq(_fld,((LoadNode)o)._fld);
  }
}
