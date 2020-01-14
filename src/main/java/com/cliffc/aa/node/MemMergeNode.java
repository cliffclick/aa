package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.AA;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.AryInt;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;
import org.jetbrains.annotations.NotNull;
import java.util.BitSet;

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
//
// As a special case, MemMerge will take the results of an all-call-memory in
// alias#1 slot 0 - and will gradually widen general memory around the call as
// the call memory sharpens.  This is specifically for SESE call behavior.
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
  public int alias2idx( int alias ) { return _aidxes.atX(alias); }
  private void set_alias2idx( int alias, int idx ) { _aidxes.setX(alias,idx); }

  // Index# for Alias#, or nearest enclosing alias parent
  private int find_alias2idx( int alias ) {
    int idx;
    while( (idx=alias2idx(alias)) == 0 && alias != BitsAlias.ALL )
      alias = BitsAlias.parent(alias);
    return idx;
  }

  // Index# for Alias#, creating as needed.  If created the new slot will be null.
  public int make_alias2idx( int alias ) {
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

  // Precise alias input
  public Node active_obj(int alias) {
    assert alias > 1 && !BitsAlias.is_parent(alias); // No already-split aliases
    return in(find_alias2idx(alias));        // Alias
  }

  // Mid-iter call, will need to unreg/rereg
  public Node obj(int alias, GVNGCM gvn) {
    assert gvn.touched(this) && alias > 1; // Only if this MemMerge is not active
    Type oldt = gvn.unreg(this);
    int idx = make_alias2idx(alias);         // Make a spot for this alias
    Node obj = in(idx);                      // Get current def
    if( obj == null ) {                      // No prior alias
      obj = in(find_alias2idx(BitsAlias.parent(alias)));
      set_def(idx, obj, null);  // Set in immediate alias parent
    }
    gvn.rereg(this,oldt);
    return obj;
  }

  // Lookup a node index, given a TypeMemPtr.  Only works if the given alias
  // has not been split into parts
  Node obj( TypeMemPtr tmp, GVNGCM gvn ) {
    int alias = tmp._aliases.abit();
    if( alias == -1 ) throw AA.unimpl(); // Handle multiple aliases, handle all/empty
    return obj(alias,gvn);
  }

  // Create a new alias slot with initial value for an active this
  public void create_alias_active( int alias, Node n, GVNGCM gvn ) {
    assert gvn==null || (!gvn.touched(this) && gvn.type(n) instanceof TypeObj);
    assert alias2idx(alias) == 0;    // No dups
    int idx = make_alias2idx(alias); // Get the exact alias
    assert in(idx)==null;            // Must be newly created, so set to null
    set_def(idx,n,null);             // No need for GVN since null
  }

  // An imprecise store updates all aliases
  public void st( StoreNode st, GVNGCM gvn ) {
    assert !gvn.touched(this);
    TypeMemPtr ptr = (TypeMemPtr)gvn.type(st.adr());
    BitSet bs = ptr._aliases.tree().plus_kids(ptr._aliases);
    for( int alias = bs.nextSetBit(0); alias >= 0; alias = bs.nextSetBit(alias+1) ) {
      int idx = make_alias2idx(alias);
      set_def(idx,st,gvn);
    }
  }


  // This MemMerge is 'active': not installed in GVN and free to have its edges
  // changed (by the Parser as new variables are discovered).  Make it
  // 'inactive' and ready for nested Node.ideal() calls.
  Node deactive( GVNGCM gvn ) {
    assert !gvn.touched(this) && _uses._len==0;
    for( int i=0; i<_defs._len; i++ ) {
      Node obj = in(i);
      assert gvn.touched(obj); // No longer needed
      //if( !gvn.touched(obj) ) { // Found active child ObjMerge
      //  _defs.set(i,null);      // Unpoint to it
      //  obj._uses.del(this);    // Keep sane asserts
      //  assert obj._uses.isEmpty(); // Ready for gvn.xform as a new node
      //  set_def(i,gvn.xform(obj),gvn); // Clean up child ObjMerge like normal
      //}
    }
    return this;                // Ready for gvn.xform as a new node
  }

  // MemMerge lost a use.  MemMerge should try to remove some aliases
  @Override public boolean ideal_impacted_by_losing_uses(GVNGCM gvn, Node dead) { return true; }

  @Override public Node ideal(GVNGCM gvn) {
    assert _defs._len==_aliases._len;
    // Dead & duplicate inputs can be removed.
    boolean progress = false;
    for( int i=1; i<_defs._len; i++ )
      if( in(i)==in(0) ||       // Dup of the main memory
          // Dup of immediate alias parent, the more general version of the prior test
          in(i)==alias2node(BitsAlias.parent(alias_at(i))) ||
          gvn.type(in(i))==TypeObj.XOBJ ) // Dead input
        { remove0(i--,gvn); progress = true; }
    if( _defs._len==1 ) return in(0); // Merging nothing
    if( progress ) return this;       // Removed some dead inputs

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

    // Back-to-back merges not in alias#1
    for( int i=1; i<_defs._len; i++ )
      if( in(i) instanceof MemMergeNode )
        { set_def(i,((MemMergeNode)in(i)).alias2node(alias_at(i)),gvn); progress = true; }
    if( progress ) return this; // Removed back-to-back merge
    

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

    // Try to remove some unused aliases.  Gather alias uses from all users.
    if( !_uses.isEmpty() && gvn._opt_mode != 0 /*not during parsing, not all users available */) {
      VBitSet bas = new VBitSet();
      boolean bad = false;
      for( Node use : _uses ) {
        VBitSet rez = use.alias_uses(gvn);
        if( rez == null )       // Some use uses all aliases
          { bad = true; break; }
        bas.or(rez);
      }
      // Kill unused aliases
      if( !bad ) {
        for( int i=1; i<_defs._len; i++ )
          if( !bas.get(_aliases.at(i)) )
            { remove0(i--,gvn); progress = true; }
        if( progress ) return this;
      }
    }

    return null;
  }

  @Override public Type value(GVNGCM gvn) {
    // Base type in slot 0
    Type t = gvn.type(in(0));
    if( !(t instanceof TypeMem) )
      return t.above_center() ? TypeMem.MEM : TypeMem.XMEM;
    TypeMem tm = (TypeMem)t;
    // We merge precise updates to the list of aliases
    for( int i=1; i<_defs._len; i++ ) {
      int alias = alias_at(i);
      Type ta = gvn.type(in(i));
      if( !(ta instanceof TypeObj) ) // Handle ANY, ALL
        ta = ta.above_center() ? TypeObj.XOBJ : TypeObj.OBJ;
      tm = tm.st(alias,(TypeObj)ta);
    }
    return tm;
  }
  @Override public Type all_type() { return TypeMem.MEM; }
  // Set of used aliases across all inputs.  This is only called from another
  // MemMerge, which means back-to-back MemMerge which will be cleared out
  // eventually.  Ok to report super conservative here.
  @Override public VBitSet alias_uses(GVNGCM gvn) { return null; }

  @Override @NotNull public MemMergeNode copy( boolean copy_edges, CallEpiNode unused, GVNGCM gvn) {
    MemMergeNode mmm = (MemMergeNode)super.copy(copy_edges, unused, gvn);
    mmm._aliases = new AryInt(_aliases._es.clone(),_aliases._len);
    mmm._aidxes  = new AryInt(_aidxes ._es.clone(),_aidxes ._len);
    return mmm;
  }
  @Override void update_alias( Node copy, BitSet aliases, GVNGCM gvn ) {
    assert gvn.touched(this);
    Type oldt = gvn.unreg(this);
    for( int i=1; i<_aliases._len; i++ ) {
      int mya = _aliases.at(i);
      if( !aliases.get(mya) ) continue;
      int[] kid0_aliases = BitsAlias.get_kids(mya);
      ((MemMergeNode)copy)._aliases.set(i,kid0_aliases[1]  );
                           _aliases.set(i,kid0_aliases[2]);
      ((MemMergeNode)copy)._aidxes.set(mya,0);
                           _aidxes.set(mya,0);
      ((MemMergeNode)copy)._aidxes.setX(kid0_aliases[1]  ,i);
                           _aidxes.setX(kid0_aliases[2],i);
    }
    gvn.rereg(this,oldt);
  }
}

