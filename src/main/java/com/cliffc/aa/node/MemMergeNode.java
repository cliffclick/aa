package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.AryInt;
import com.cliffc.aa.util.SB;
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

  // Alias equivalence class matching each input.  Sorted.
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
    gvn.unreg(this);
    for( int i=1; i<_defs._len; i++ )
      if( !in(i).is_prim() )
        remove0(i--,gvn);
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

  private boolean check() {
    for( int i=1; i<_aliases._len; i++ )
      if( _aliases.at(i-1) >= _aliases.at(i) )
        return false;
    return true;
  }

  // Index# for Alias#, creating as needed.  If created the new slot will be null.
  public int make_alias2idx( int alias ) {
    assert check();
    // Insert in alias index order
    int iidx = _aliases.binary_search(alias);
    if( _aliases.atX(iidx)==alias ) return iidx; // Exact match
    insert(iidx,null);          // Initial value
    _aliases.insert(iidx,alias);// Matching idx# to alias map
    // Every alias after the insertion point has its index upped by 1
    _aidxes.map_update(i -> i >= iidx ? i+1 : i);
    set_alias2idx(alias,iidx);// Reverse map alias# to idx#
    assert check();
    return iidx;
  }

  // Remove a DEF, and update everything
  public void remove0( int xidx, GVNGCM gvn ) {
    assert check();
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
    assert gvn==null || (gvn.type(n) instanceof TypeObj || gvn.type(n) instanceof TypeMem);
    assert alias2idx(alias) == 0;    // No dups
    int idx = make_alias2idx(alias); // Get the exact alias
    assert in(idx)==null;            // Must be newly created, so set to null
    set_def(idx,n,null);             // No need for GVN since null
  }

  // An imprecise store updates all aliases
  public void st( StoreNode st, GVNGCM gvn ) {
    assert !gvn.touched(this);
    Type tadr = gvn.type(st.adr());
    // If address is super conservative, store over everything
    if( !(tadr instanceof TypeMemPtr) ) {
      if( tadr.above_center() ) return; // Assume nothing is being stored into
      assert TypeMemPtr.OOP.isa(tadr);  // Address might lift to a valid ptr
      tadr = TypeMemPtr.STRUCT;         // All possible field aliases
    }
    TypeMemPtr ptr = (TypeMemPtr)tadr;
    for( int alias : ptr._aliases )
      for( int kid = alias; kid!=0; kid = BitsAlias.next_kid(alias,kid) )
        set_def(make_alias2idx(alias),st,gvn);
  }


  // This MemMerge is 'active': not installed in GVN and free to have its edges
  // changed (by the Parser as new variables are discovered).  Make it
  // 'inactive' and ready for nested Node.ideal() calls.
  Node deactive( GVNGCM gvn ) {
    assert !gvn.touched(this) && _uses._len==0;
    for( int i=0; i<_defs._len; i++ ) {
      Node obj = in(i);
      assert gvn.touched(obj);  // No longer needed
    }
    return this;                // Ready for gvn.xform as a new node
  }

  @Override public Node ideal(GVNGCM gvn, int level) {
    if( is_prim() ) return null;
    assert _defs._len==_aliases._len;
    boolean live_stable = _live.isa(in(0)._live);
    if( _defs._len==1 )
      // Much pondering: MemMerge can filter liveness on slot0 (because some
      // closure goes dead so the alias for it is XOBJ).  This knowledge has
      // flowed "uphill": no one needs to provide this alias.  But also, the
      // value()s can flow downhill and the slot0 might also be XOBJ.  Then we
      // simplify to a single input edge, merging nothing.  But we cannot
      // collapse lest we "lower" liveness by making the unused alias used again.
      return live_stable ? in(0) : null; // Merging nothing

    // Remove child instances of the parent
    boolean progress = false;
    for( int i=_defs._len-1; i>=1; i-- ) {
      int alias = alias_at(i);
      int par = BitsAlias.parent(alias);
      int pidx = find_alias2idx(par);
      if( in(i)==in(pidx) )
        { progress=true; remove0(i,gvn); }
    }
    if( progress )
      return this;

    // Collapse back-to-back MemMerge
    if( in(0) instanceof MemMergeNode ) {
      MemMergeNode mmm = (MemMergeNode)in(0);
      int max_alias = Math.max(_aliases.last(),mmm._aliases.last());
      for( int alias=2; alias<=max_alias; alias++ ) {
        int xidx =     alias2idx(alias);
        int midx = mmm.alias2idx(alias);
        // Not set here, and yes set on coming?
        if( xidx==0 && midx!=0 ) // Then set it here, instead of taking from base
          create_alias_active(alias,mmm.in(midx),gvn);
        else if( xidx > 0 && in(xidx)==mmm ) // Just gets from base?
          set_def(xidx,mmm.in(midx),gvn); // Then get from where base gets it from
      }
      set_def(0,mmm.in(0),gvn);
      return this;
    }

    return null;
  }


  // Base memory (alias#1) comes in input#0.  Other inputs refer to other
  // aliases (see _aliases) and children follow parents (since alias#s are
  // sorted).  Each input replaces (not merges) their parent in just that
  // subtree.
  @Override public Type value(GVNGCM gvn) {
    // Base memory type in slot 0
    Type t = gvn.type(in(0));
    if( !(t instanceof TypeMem) )
      return t.above_center() ? TypeMem.XMEM : TypeMem.MEM;
    TypeMem tm = (TypeMem)t;

    // Merge inputs with parent.
    Ary<TypeObj> tos = new Ary<>(tm.alias2objs().clone());
    for( int i=1; i<_defs._len; i++ ) {
      final int alias = alias_at(i);
      Type ta = gvn.type(in(i));
      if( ta instanceof TypeMem )
        ta = ((TypeMem)ta).at(alias);
      TypeObj tao = ta instanceof TypeObj ? (TypeObj)ta
        : (ta==null || ta.above_center() ? TypeObj.XOBJ : TypeObj.OBJ); // Handle ANY, ALL

      // Meet this alias (plus all children) into the base.  Must be a MEET and
      // not a replacement, because the same alias might be available in the
      // base as well as from a local edge.
      TypeObj base = tm.at(alias);
      if( base == null ) base = TypeObj.XOBJ;
      for( int kid=alias; kid!=0; kid=BitsAlias.next_kid(alias,kid) ) {
        TypeObj tkid = tos.atX(kid);
        if( tkid == null ) tkid = base;
        tos.setX(kid,(TypeObj)tkid.meet(tao));
      }
    }
    return TypeMem.make0(tos._es);
  }


  // Compute the liveness local contribution to def's liveness.  Ignores the
  // incoming memory types, as this is a backwards propagation of demanded
  // memory.
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) {
    if( in(0)==def ) {
      return _live;             // Pass thru all requests.
    } else {
      // Pass thru just the alias slice in question
      int alias = alias_at(_defs.find(def));
      return TypeMem.make(alias, _live.at(alias));
    }
  }
  @Override public boolean basic_liveness() { return false; }

  @Override public Type all_type() { return TypeMem.MEM; }

  @Override @NotNull public MemMergeNode copy( boolean copy_edges, CallEpiNode unused, GVNGCM gvn) {
    MemMergeNode mmm = (MemMergeNode)super.copy(copy_edges, unused, gvn);
    mmm._aliases = new AryInt(_aliases._es.clone(),_aliases._len);
    mmm._aidxes  = new AryInt(_aidxes ._es.clone(),_aidxes ._len);
    return mmm;
  }
  void update_alias( Node copy, BitSet aliases, GVNGCM gvn ) {
    MemMergeNode cmem = (MemMergeNode)copy;
    assert gvn.touched(this);
    Node xobj = gvn.con(TypeObj.XOBJ);
    Type oldt = gvn.unreg(this);
    for( int i=1; i<_aliases._len; i++ ) {
      int mya = _aliases.at(i);
      if( !aliases.get(mya) ) continue; // Alias not split here
      int[] kid0_aliases = BitsAlias.get_kids(mya);
      int newalias1 = kid0_aliases[1];
      int newalias2 = kid0_aliases[2];
      cmem._update(gvn,xobj,i,mya,newalias1,newalias2);
      this._update(gvn,xobj,i,mya,newalias2,newalias1);
    }
    assert check() && cmem.check();
    gvn.rereg(this,oldt);
  }
  private void _update(GVNGCM gvn, Node xobj, int oidx, int oldalias, int newalias1, int newalias2) {
    int nidx1 = make_alias2idx(newalias1);
    set_def(nidx1,in(oidx),null); // My alias comes from the original
    int nidx2 = make_alias2idx(newalias2);
    set_def(nidx2, in(0)  ,gvn ); // The other alias comes from default
    set_def(oidx , xobj   ,gvn ); // The original goes dead
  }
  @Override public int hashCode() { return super.hashCode()+_aliases.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof MemMergeNode) ) return false;
    MemMergeNode mem = (MemMergeNode)o;
    return _aliases.equals(mem._aliases);
  }

}

