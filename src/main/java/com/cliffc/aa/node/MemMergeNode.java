package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.AA;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.AryInt;
import com.cliffc.aa.util.SB;
import org.jetbrains.annotations.NotNull;

// Merge a lot of TypeObjs into a TypeMem.  Each input is from a different
// alias.  Each collection represents the whole of memory, with missing parts
// coming in the alias#1 in slot 0, and no duplication.
public class MemMergeNode extends Node {
  // Alias equivalence class matching each input.  No overlaps.
  // Phat memory always in slot 0.
  private AryInt _aliases;

  public MemMergeNode( Node mem ) { super(OP_MERGE,mem);  _aliases = new AryInt(new int[]{BitsAlias.ALL}); }
  // A first alias
  public MemMergeNode( Node mem, Node obj, int alias ) {
    super(OP_MERGE,mem,obj);
    _aliases = new AryInt(new int[]{BitsAlias.ALL,alias});
  }
  public void reset_to_init1() { _aliases.set_len(_defs._len); }

  @Override String str() {
    SB sb = new SB().p('[');
    for( int i=0;i<_defs._len; i++ )
      if( in(i) != null )
          sb.p(in(i)._uid).p(":#").p(_aliases.at(i)).p(", ");
    return sb.unchar().unchar().p(']').toString();
  }

  private Node mem() { return in(0); } // Phat/Wide mem

  // Return the Node index that matches this alias, including parents of a
  // split alias.
  int afind( int alias ) {
    for( int i=1; i<_aliases._len; i++ )
      if( BitsAlias.is_parent(_aliases.at(i),alias) )
        return i;
    return -1;
  }

  // Return an 'active' (not in GVN) object, for direct manipulation by the Parser.
  public ObjMergeNode active_obj(int alias, GVNGCM gvn) {
    assert !gvn.touched(this) && alias > 1;  // Only if this MemMerge is also active
    int idx = afind(alias);     // Find index of matching alias
    if( idx == -1 ) {           // Not split on this alias before
      idx = _defs._len;         // Just append; TODO: sort by alias
      add_def(null);            // No def yet
      _aliases.push(alias);     // But set alias to index mapping
    }
    Node obj = in(idx);         // Get current def
    if( obj instanceof ObjMergeNode && obj._uses._len==1 ) { // Must be an ObjMerge, and if this is the only use, then just reactivate
      if( gvn.touched(obj) ) gvn.unreg(obj);
      return (ObjMergeNode)obj; // Active already, just return
    }
    ObjMergeNode o = new ObjMergeNode(obj==null ? in(0) : obj,alias); // New ObjMerge from phat memory
    set_def(idx,o,gvn);
    return o;
  }

  // Mid-iter call, will need to unreg/rereg
  public Node obj(int alias, GVNGCM gvn) {
    assert gvn.touched(this) && alias > 1; // Only if this MemMerge is not active
    int idx = afind(alias);     // Find index of matching alias
    if( idx == -1 ) {           // Not split on this alias before
      idx = _defs._len;         // Just append; TODO: sort by alias
      Type t = gvn.type(this);  gvn.unreg(this);
      add_def(null);            // No def yet
      _aliases.push(alias);     // But set alias to index mapping
      gvn.rereg(this,t);
    }
    if( in(idx) != null ) return in(idx); // Already exists
    // Make it, splitting the object from phat memory
    Node obj = gvn.xform(new ObjMergeNode(in(0),alias));
    Type t = gvn.type(this);  gvn.unreg(this);
    set_def(idx,obj,gvn);
    gvn.rereg(this,t);
    return obj;
  }
  // Lookup a node index, given a TypeMemPtr.  Only works if the given alias
  // has not been split into parts
  Node obj( TypeMemPtr tmp, GVNGCM gvn ) {
    int alias = tmp._aliases.abit();
    if( alias == -1 ) throw AA.unimpl(); // Handle multiple aliases, handle all/empty
    return obj(alias,gvn);
  }

  // Create a new alias with initial value for deactive/gvn-registered memory
  public void create_alias( int alias, Node n, GVNGCM gvn ) {
    assert gvn.touched(this);
    Type t = gvn.type(this);  gvn.unreg(this);
    create_alias_active(alias,n,gvn);
    gvn.rereg(this,t);
  }
  // Create a new alias with initial value for an active this
  public void create_alias_active( int alias, Node n, GVNGCM gvn ) {
    assert !gvn.touched(this) && gvn.type(n) instanceof TypeObj;
    assert _aliases.find(alias) == -1; // No dups
    add_def(n);                 // The default
    _aliases.push(alias);       // But set alias to index mapping
  }

  // This MemMerge is 'active': not installed in GVN and free to have its edges
  // changed (by the Parser as new variables are discovered).  Make it
  // 'inactive' and ready for nested Node.ideal() calls.
  Node deactive( GVNGCM gvn ) {
    assert !gvn.touched(this) && _uses._len==0;
    for( int i=0; i<_defs._len; i++ ) {
      Node obj = in(i);
      if( !gvn.touched(obj) ) {
        _defs.set(i,null);
        obj._uses.del(this);
        assert obj._uses.isEmpty();    // Ready for gvn.xform as a new node
        set_def(i,gvn.xform(obj),gvn);
      }
    }
    return this;                // Ready for gvn.xform as a new node
  }

  // Return the node for the alias, or the default if not overridden
  Node nfind( int alias ) {
    int idx = afind(alias);     // Find index of matching alias
    return in(idx==-1 ? 0 : idx);
  }
  int alias_at(int idx) { return _aliases.at(idx); }

  @Override public Node ideal(GVNGCM gvn) {
    assert _defs._len==_aliases._len;
    // Dead & duplicate inputs can be removed.
    boolean progress = false;
    for( int i=1; i<_defs._len; i++ ) {
      if( in(i)==in(0) || gvn.type(in(i))==TypeObj.XOBJ ||
          // An ObjMerge, merging nothing and only existing to be a narrow slice
          (in(i) instanceof ObjMergeNode && in(i)._defs._len==1 && in(i).in(0)==in(0) )) {
        remove(i,gvn);
        _aliases.remove(i);
        i--;
        progress = true;
      }
    }
    if( _defs._len==1 ) return in(0); // Merging nothing
    if( progress ) return this;       // Removed some dead inputs

    //// If I have a Named Constructor usage, and have 2 uses (named constructor
    //// and the Merge following it), make sure the Named Constructor can run
    //// ideal() so it can fold away.
    //if( _uses._len==2 )
    //  for( Node use : _uses )
    //    if( use instanceof IntrinsicNode.ConvertPtrTypeName )
    //      gvn.add_work(use);
    //
    //// If skinny is a pointer and not memory, then this is a collapsing
    //// named-type-into-allocator.
    //if( gvn.type(obj()) instanceof TypeMemPtr )
    //  return mem;

    // Back-to-back merges collapse
    if( mem() instanceof MemMergeNode ) {
      MemMergeNode mem = (MemMergeNode)mem();
      for( int i=1; i<mem._defs._len; i++ ) {
        int alias = mem._aliases.at(i);
        // If alias is old, keep the original (it stomped over the incoming
        // memory).  If alias is new, use the new value.
        if( afind(alias) == -1 )
          create_alias_active(alias,mem.in(i),gvn);
      }
      return set_def(0,mem.in(0),gvn); // Return improved self
    }
    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    // Base type in slot 0
    Type t = gvn.type(in(0));
    if( !(t instanceof TypeMem) )
      return t.above_center() ? TypeMem.XMEM : TypeMem.MEM;
    TypeMem tm = (TypeMem)t;
    Type tx = gvn.self_type(this);
    if( tx == null ) tx = t.above_center() ? TypeMem.XMEM : TypeMem.MEM;
    // We merge precise updates to the list of aliases
    for( int i=1; i<_defs._len; i++ ) {
      int alias = _aliases.at(i);
      Type ta = gvn.type(in(i));
      if( !(ta instanceof TypeObj) ) return tx;
      TypeObj tobj = (TypeObj)ta;
      if( Math.abs(tobj._news.getbit())!=alias )
        return tx; // Expecting an exact alias
      tm = tm.st(alias,tobj);
    }
    return tm;
  }
  @Override public Type all_type() { return TypeMem.MEM; }

  // Return the exact NewNode, or null
  NewNode exact( Node ptr ) {
    throw AA.unimpl();
    //return ptr.in(0)==obj().in(0) && ptr.in(0) instanceof NewNode ? (NewNode)ptr.in(0) : null;
  }

  @Override @NotNull public MemMergeNode copy( boolean copy_edges, GVNGCM gvn) {
    MemMergeNode mmm = (MemMergeNode)super.copy(copy_edges, gvn);
    mmm._aliases = new AryInt(_aliases._es.clone(),_aliases._len);
    return mmm;
  }
}

