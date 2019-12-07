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
//
// MemMerge is used by the parser to create the initial memory state.  While
// parsing the MemMerge is left "active" - not in the GVN tables - which means
// edges can be updated without e.g. rehashing in GVN.  Post parsing follows
// the normal edge-modification rules.  This means there are two versions of
// some routines - the "in GVN tables" and "out of GVN tables" versions.
//
// Any alias can be split from its parent, and the parent remains to handle the
// unsplit parts.  New aliases can be added; when added they effectively
// pre-split up the alias tree to the root, and take their initial value from
// their deepest parent.  All aliases are assumed to be precisely independent
// (equivalence class).  Alias parents are typically assumed to have more
// future unknown splits in them, so merges of all known children still expect
// to have a parent merge.

public class MemMergeNode extends Node {

  // Alias equivalence class matching each input.
  // A map from idx# to Alias, aligned with the Nodes.
  private AryInt _aliases;

  // Alias-to-idx#, for fast reverse lookup.
  private AryInt _aidxes;

  public MemMergeNode( Node mem ) {
    super(OP_MERGE,mem);
    // Forward mapping from idx# to alias#.  Slot 0 is always BitsAlias.ALL
    _aliases = new AryInt(new int[]{BitsAlias.ALL});
    // Reverse mapping from alias# to idx#.  BitsAlias.ALL is always slot 0,
    // and null (alias 0) is never a thing.
    _aidxes  = new AryInt(new int[]{-1,0});
  }
  // A first alias
  public MemMergeNode( Node mem, Node obj, int alias ) {
    this(mem);
    create_alias_active(alias,obj,null);
  }
  @Override public void reset_to_init1(GVNGCM gvn) {
    for( int i=1; i<_defs._len; i++ )
      if( in(i)._uid >= GVNGCM._INIT0_CNT )
        remove0(i,gvn);
    _aliases.set_len(_defs._len);
  }

  @Override String str() {
    SB sb = new SB().p('[');
    for( int i=0;i<_defs._len; i++ )
      sb.p(in(i)==null ? -1 : in(i)._uid).p(":#").p(alias_at(i)).p(", ");
    return sb.unchar().unchar().p(']').toString();
  }

  private Node mem() { return in(0); } // Phat/Wide mem
  int alias_at(int idx) { return _aliases.at(idx); }

  // Index# for Alias#.  Returns 0 if no exact match.
  private int alias2idx( int alias ) { return _aidxes.atX(alias); }
  private void set_alias2idx( int alias, int idx ) { _aidxes.setX(alias,idx); }

  // Index# for Alias#, or nearest enclosing alias parent
  private int find_alias2idx( int alias ) {
    int idx;
    while( (idx=alias2idx(alias)) == 0 && alias != BitsAlias.ALL )
      alias = BitsAlias.parent(alias);
    return idx;
  }

  // Index# for Alias#, creating as needed.  If created the new slot will be null.
  private int make_alias2idx( int alias ) {
    // Insert in alias index order
    int iidx = _aliases.binary_search(alias);
    if( _aliases.atX(iidx)==alias ) return iidx; // Exact match
    insert(iidx,null);          // Initial value
    _aliases.insert(iidx,alias);// Matching idx# to alias map
    // Every alias after the insertion point has its index upped by 1
    _aidxes.map_update(i -> i >= iidx ? i+1 : i);
    set_alias2idx(alias,iidx);// Reverse map alias# to idx#
    return iidx;
  }

  // Remove a DEF, and update everything
  private void remove0( int xidx, GVNGCM gvn ) {
    remove(xidx,gvn);                  // Remove def, preserving order
    int alias = _aliases.remove(xidx); // Remove alias mapping, preserving order
    // Every alias after the removal point has its index downed by 1
    _aidxes.map_update(i -> i >= xidx ? i-1 : i);
    set_alias2idx(alias,0);     // Remove reverse mapping alias# to idx#
  }

  // Node for an alias, using the nearest enclosing parent alias as needed
  Node alias2node( int alias ) { return in(find_alias2idx(alias)); }

  // Node for an alias, using the nearest enclosing parent alias as needed.
  // Fails with NULL if there are any children of the parent.
  // Used by Loads, which can bypass exact aliases.
  Node alias2node_precise( int alias ) {
    int idx = find_alias2idx(alias);
    for( int j=idx+1; j<_defs._len; j++ )
      if( BitsAlias.is_parent(alias,alias_at(j)) )
        return null;
    return in(idx);
  }

  // Return an 'active' (not in GVN) object, for direct manipulation by the Parser.
  public ObjMergeNode active_obj(int alias, GVNGCM gvn) {
    assert !gvn.touched(this) && alias > 1;  // Only if this MemMerge is also active
    assert !BitsAlias.is_parent(alias);      // No already-split aliases
    int idx = make_alias2idx(alias);         // Make a spot for this alias
    Node obj = in(idx);                      // Get current def
    if( obj instanceof ObjMergeNode && obj._uses._len==1 ) { // Must be an ObjMerge, and if this is the only use, then just reactivate
      if( gvn.touched(obj) ) gvn.unreg(obj); // Make active (out of GVN)
      return (ObjMergeNode)obj;              // Active already, just return
    }
    int pidx = find_alias2idx(BitsAlias.parent(alias)); // Parent index
    ObjMergeNode o = new ObjMergeNode(obj==null ? in(pidx) : obj, alias); // New ObjMerge from parent memory
    set_def(idx,o,gvn);
    return o;
  }

  // Mid-iter call, will need to unreg/rereg
  public Node obj(int alias, GVNGCM gvn) {
    assert gvn.touched(this) && alias > 1; // Only if this MemMerge is not active
    Type t = gvn.type(this);  gvn.unreg(this);
    int idx = make_alias2idx(alias);         // Make a spot for this alias
    Node obj = in(idx);                      // Get current def
    if( obj == null ) {                      // No prior alias
      obj = in(find_alias2idx(BitsAlias.parent(alias)));
      set_def(idx, obj, null);  // Set in immediate alias parent
    }
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
    assert gvn==null || (!gvn.touched(this) && gvn.type(n) instanceof TypeObj);
    assert alias2idx(alias) == 0;    // No dups
    int idx = make_alias2idx(alias); // Get the exact alias
    assert in(idx)==null;            // Must be newly created, so set to null
    set_def(idx,n,null);             // No need for GVN since null
  }

  // This MemMerge is 'active': not installed in GVN and free to have its edges
  // changed (by the Parser as new variables are discovered).  Make it
  // 'inactive' and ready for nested Node.ideal() calls.
  Node deactive( GVNGCM gvn ) {
    assert !gvn.touched(this) && _uses._len==0;
    for( int i=0; i<_defs._len; i++ ) {
      Node obj = in(i);
      if( !gvn.touched(obj) ) { // Found active child ObjMerge
        _defs.set(i,null);      // Unpoint to it
        obj._uses.del(this);    // Keep sane asserts
        assert obj._uses.isEmpty(); // Ready for gvn.xform as a new node
        set_def(i,gvn.xform(obj),gvn); // Clean up child ObjMerge like normal
      }
    }
    return this;                // Ready for gvn.xform as a new node
  }

  @Override public Node ideal(GVNGCM gvn) {
    assert _defs._len==_aliases._len;
    // Dead & duplicate inputs can be removed.
    boolean progress = false;
    for( int i=1; i<_defs._len; i++ )
      if( in(i)==in(0) ||       // Dup of the main memory
          // Dup of immediate alias parent, the more general version of the prior test
          in(i)==alias2node(BitsAlias.parent(alias_at(i))) ||
          gvn.type(in(i))==TypeObj.XOBJ || // Dead input
          // An ObjMerge, merging nothing and only existing to be a narrow slice
          (in(i) instanceof ObjMergeNode && in(i)._defs._len==1 && in(i).in(0)==in(0) ))
        { remove0(i--,gvn); progress = true; }
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
        int alias = mem.alias_at(i);
        // If alias is old, keep the original (it stomped over the incoming
        // memory).  If alias is new, use the new value.
        int idx = alias2idx(alias);
        if( idx != 0 ) { // 'this' has an exact update, so the prior alias got stomped
          // But need to make sure no children, since all children got stomped.
          // All child aliases are strictly larger than parents, and since
          // sorted by alias# can just look after the current point.
          for( int j=i+1; j<mem._defs._len; j++ )
            if( BitsAlias.is_parent(alias,mem.alias_at(j)) )
              throw AA.unimpl(); // Need to crush all children, since parent got crushed
        } else {
          // Create alias slice from nearest alias parent
          create_alias_active(alias,mem.in(i),gvn);
        }
      }
      return set_def(0,mem.in(0),gvn); // Return improved self
    }

    // If input sharpens, need to sharpen internal mappings
    for( int i=1; i<_aliases._len; i++ ) {
      int new_alias = in2alias(i,gvn);
      int old_alias = alias_at(i);
      if( new_alias != old_alias && BitsAlias.is_parent(old_alias,new_alias) ) { // Input alias sharpens?
        set_alias2idx(old_alias,0); // Assume old alias goes dead here
        _aliases.set(i,new_alias);
        set_alias2idx(new_alias,i);
      }
    }

    // CNC - This stanza is here because of a flaw in unpacking Call args.
    //
    // If an input is an OProj and a use is a Call, put the Call on the
    // worklist.  This is because the Call "peeks through" this Merge looking
    // for an OProj in order to unpack arguments, and the OProj might have just
    // appeared.  The Call cannot step-through the Merge, because after
    // unpacking the same Merge is also the Calls normal memory.
    boolean has_oproj=false;
    for( int i=1; i<_aliases._len; i++ )
      if( in(i) instanceof OProjNode )
        { has_oproj=true; break; }
    if( has_oproj )
      for( Node use : _uses )
        if( use instanceof CallNode && !((CallNode)use)._unpacked )
          gvn.add_work(use);

    return null;
  }

  int in2alias( int idx, GVNGCM gvn ) {
    Type t = gvn.type(in(idx));
    if( !(t instanceof TypeObj) ) return -1; // Types have not flowed yet
    TypeObj tobj = (TypeObj)t;
    return Math.abs(tobj._news.getbit());
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
      int alias = alias_at(i);
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

  @Override @NotNull public MemMergeNode copy( boolean copy_edges, GVNGCM gvn) {
    MemMergeNode mmm = (MemMergeNode)super.copy(copy_edges, gvn);
    mmm._aliases = new AryInt(_aliases._es.clone(),_aliases._len);
    mmm._aidxes  = new AryInt(_aidxes ._es.clone(),_aidxes ._len);
    return mmm;
  }
}

