package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.AryInt;
import com.cliffc.aa.util.SB;
import org.jetbrains.annotations.NotNull;

import java.util.BitSet;

// Merge a lot of TypeObjs into a TypeMem.  Each input is from a different
// alias.  Each collection represents the whole of memory, with missing parts
// coming in the alias#1 in slot 0, and no duplication in the other edges.
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
// The edge behavior encourages tree-like compaction, to handle the expected
// common case of having many known aliases unrelated to the local computation.
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

  @Override String str() {
    SB sb = new SB().p('[');
    for( int i=0;i<_defs._len; i++ )
      sb.p(in(i)==null ? -1 : in(i)._uid).p(":#").p(alias_at(i)).p(", ");
    return sb.unchar().unchar().p(']').toString();
  }

  Node mem() { return in(0); } // Phat/Wide mem
  int alias_at(int idx) { return _aliases.at(idx); }
  int max() { return _aliases.last(); }

  // index# for Alias#.  Returns 0 if no exact match.
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
    if( gvn._opt_mode == 0 ) return null;
    assert _defs._len==_aliases._len;
    if( !(gvn.type(mem()) instanceof TypeMem) ) return null; // Generally 'any' for dead code

    // Collapse trivial
    if( _defs._len==1 ) return in(0);

    // Brute force back-to-back ideal collapse
    MemMergeNode mmm = ideal_collapse(gvn);
    if( mmm != null ) return mmm;

    return null;
  }

  // Having not gotten MemMerge ideal() (nor value()) semantics right after a
  // dozen tries, here comes a brute-force attempt at an optimal ideal() call.
  private MemMergeNode ideal_collapse( GVNGCM gvn ) {
    assert check();
    Node base = mem();

    // Build an array containing the Node used for each and every alias.
    int len = Env.DEFMEM._defs._len;
    Ary<Node> ins = new Ary<>(new Node[len]);
    ins.setX(1,base);
    for( int alias=2; alias<ins._len; alias++ )
      ins.set(alias,alias2node(alias));

    // "Peek" thru the base, to a prior MemMerge and go again (1-step).
    // Repeat until no more back-to-back MemMerge.
    while( base instanceof MemMergeNode ) {
      MemMergeNode mmm = (MemMergeNode)base;
      len = Math.max(len,mmm.max()+1);
      // Stretch alias list to cover the max set
      while( ins._len < len )
        ins.push(alias2node(ins._len));
      // Find instances of the base, and peek again
      for( int alias=1; alias<len; alias++ )
        if( ins.at(alias)==base )
          ins.set(alias,mmm.alias2node(alias));
      // Should have no instances of the base amongst the non-bases, just
      // step-thru the base.
      base=ins.at(1);
      assert gvn.type(base) instanceof TypeMem;
    } // Check for progress

    // Find any unused inputs, and set them to either the base (if unused
    // there) or to a constant unused.  Other constants (than UNUSED) do not
    // work, since they can lift to UNUSED but UNUSED can never lift again.
    Node unused=null;
    TypeMem tself = (TypeMem)gvn.self_type(this);
    TypeMem tbase = (TypeMem)gvn.self_type(base);
    for( int alias=2; alias<len; alias++ ) {
      if( _live.at(alias)==TypeObj.UNUSED ) {
        if( unused==null ) unused = gvn.con(TypeObj.UNUSED);
        ins.set(alias,unused);
      }
      // Use base instead of explicit unused set (folds up a lot of explicit sets)
      int par = BitsAlias.parent(alias);
      if( par>0 && ins.at(par)==base && tself.at(alias)==TypeObj.UNUSED && tbase.at(alias)==TypeObj.UNUSED ) {
        // Only legit if parent has no used kids after unused base
        boolean used_kids=false;
        for( int kid=alias; kid != 0; kid = BitsAlias.next_kid(alias,kid) )
          if( tbase.at(kid)!=TypeObj.UNUSED )
            { used_kids=true; break; }
        if( !used_kids ) ins.set(alias, base); // Use base instead of explicit set
      }
    }

    // Compact.  Copy minimal edges to preserve semantics.
    Ary<Node> outs = new Ary<>(new Node[_defs._len],0);
    AryInt alss = new AryInt(new int[_defs._len],0);
    AryInt adxs = new AryInt(new int[  ins._len],0);
    for( int alias=1; alias<ins._len; alias++ ) {
      // If the alias uses the same node as the parent, then compact away
      int par = BitsAlias.parent(alias);
      if( par==0 || ins.at(par)!=ins.at(alias) ) { // Need the edge
        adxs.setX(alias,outs._len);
        outs.push(ins.at(alias));
        alss.push(alias);
      }
    }

    // Check for progress.
    if( _defs   .equals(outs) &&
        _aliases.equals(alss) &&
        _aidxes .equals(adxs) ) {
      if( unused!=null )
        if( unused._uses._len==0 ) gvn.kill(unused);
        else unused._live = unused.live(gvn); // Unwind making it alive
      return null;              // No progress
    }
    // Crush/update & return.  Add before remove to avoid killing to early.
    for( Node nnn : outs ) add_def(nnn);
    while( _defs._len>outs._len ) remove(0,gvn);
    _aliases=alss;
    _aidxes =adxs;
    assert check();
    assert value(gvn).isa(tself); // Can lift type if some goes unused
    return this;
  }

  // Base memory (alias#1) comes in input#0.  Other inputs refer to other
  // aliases (see _aliases) and children follow parents (since alias#s are
  // sorted).  Each input merges their parent in just that subtree.
  @Override public Type value(GVNGCM gvn) {
    // Base memory type in slot 0
    Type t = gvn.type(mem());
    if( !(t instanceof TypeMem) ) return t.oob();
    TypeMem tm = (TypeMem)t;

    // Merge inputs with parent.
    TypeObj[] tpars = tm.alias2objs(); // Clone of base memory
    Ary<TypeObj> tos = new Ary<>(tpars.clone());
    for( int i=1; i<_defs._len; i++ ) {
      final int alias = alias_at(i);
      Type ta = gvn.type(in(i));

      for( int kid=alias; kid!=0; kid=BitsAlias.next_kid(alias,kid) ) {
        Type tax = ta instanceof TypeMem ? ((TypeMem)ta).at(kid) : ta;
        TypeObj tao = tax instanceof TypeObj ? (TypeObj)tax
          : (tax==null || tax.above_center() ? TypeObj.UNUSED : TypeObj.ISUSED); // Handle ANY, ALL
        if( tao!=TypeObj.UNUSED )
          tao = (TypeObj)tm.at(kid).meet(tao);
        tos.setX(kid, tao );
      }
    }
    return TypeMem.make0(tos._es);
  }
  @Override public boolean basic_liveness() { return false; }


  // Compute the liveness local contribution to def's liveness.  Ignores the
  // incoming memory types, as this is a backwards propagation of demanded
  // memory.
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) {
    if( _live==TypeMem.DEAD ) return TypeMem.DEAD;
    if( in(0)==def ) return _live; // Pass thru all requests.
    // Pass thru just the alias slice in question - which might appear more than once
    TypeMem rez = TypeMem.ANYMEM;
    for( int i=1; i<_defs._len; i++ )
      if( in(i)==def ) {
        int alias = alias_at(i);
        rez = rez.set(alias,_live.at(alias));
      }
    return rez;
  }

  @Override @NotNull public MemMergeNode copy( boolean copy_edges, GVNGCM gvn) {
    MemMergeNode mmm = (MemMergeNode)super.copy(copy_edges, gvn);
    mmm._aliases = new AryInt(_aliases._es.clone(),_aliases._len);
    mmm._aidxes  = new AryInt(_aidxes ._es.clone(),_aidxes ._len);
    return mmm;
  }
  void update_alias( Node copy, BitSet aliases, GVNGCM gvn ) {
    MemMergeNode cmem = (MemMergeNode)copy;
    assert gvn.touched(this);
    Node xobj = gvn.add_work(gvn.con(TypeObj.UNUSED));
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

