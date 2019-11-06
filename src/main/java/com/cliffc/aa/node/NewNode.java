package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.type.*;
import org.jetbrains.annotations.NotNull;

// Allocates a TypeObj in memory.  TypeStructs can hold pointers to other
// TypeStructs, and can be iteratively extended at PhiNodes to any depth.
// However, the actual depth only extends here, at the NewNode, thus a depth-
// check and approximation happens here also.  This is the only Node that can
// make recursive types.
//
// NewNode produces a Tuple type, with the TypeObj and a TypeMemPr.
//
// NewNodes have a unique alias class - they do not alias with any other
// NewNode, even if they have the same type.  Upon cloning both NewNodes get
// new aliases that inherit (tree-like) from the original alias.
//
// During Parsing we construct closures whose field names are discovered as we
// parse.  Hence we support a type which represents some concrete fields, and a
// choice of all possible remaining fields.  The _any choice means we can add
// fields, although the closure remains impossibly high until the lexical scope
// ends and no more fields can appear.

public class NewNode extends Node {
  // Unique alias class, one class per unique memory allocation site.
  // Only effectively-final, because the copy/clone sets a new alias value.
  int _alias;                   // Alias class
  TypeStruct _ts;               // base Struct
  private TypeName _name;       // If named, this is the name and _ts is the base

  // NewNodes can participate in cycles, where the same structure is appended
  // to in a loop until the size grows without bound.  If we detect this we
  // need to approximate a new cyclic type.
  public final static int CUTOFF=2; // Depth of types before we start forcing approximations

  public NewNode( ) {
    super(OP_NEW,(Node)null);   // no ctrl field
    _alias = BitsAlias.new_alias(BitsAlias.REC);
    _ts = TypeStruct.make_alias(_alias); // No fields
    _name =null;
  }
  String xstr() { return "New*"+_alias; } // Self short name
  String  str() { return "New"+xs(); } // Inline less-short name

  private int def_idx(int fld) { return fld+1; } // Skip ctrl in slot 0
  Node fld(int fld) { return in(def_idx(fld)); } // Node for field#
  private TypeObj xs() { return _name == null ? _ts : _name; }

  public Node get(String name) { return in(def_idx(_ts.find(name,-1))); }
  public boolean exists(String name) { return _ts.find(name,-1)!=-1; }
  public boolean is_mutable(String name) { return _ts._finals[_ts.find(name,-1)] == TypeStruct.frw(); }
  public boolean is_final  (String name) { return _ts._finals[_ts.find(name,-1)] == TypeStruct.ffinal(); }

  // Called when folding a Named Constructor into this allocation site
  void set_name( GVNGCM gvn, TypeName name ) {
    assert !name.above_center();
    // Name is a wrapper over _ts, except for alias because Name is probably a generic type.
    TypeName n2 = name.make(xs());
    assert n2._t == xs();       // wrapping exactly once
    assert n2._news.abit() == _alias;
    if( gvn.touched(this) ) {
      gvn.unreg(this);
      _name = n2;
      gvn.rereg(this,value(gvn));
    } else {
      _name = n2;
    }
  }

  // Create a field from parser
  public Node create( String name, Node val, GVNGCM gvn, byte mutable  ) {
    assert def_idx(_ts._ts.length)== _defs._len;
    assert _ts.find(name,-1) == -1;
    gvn.unreg(this);
    _ts = _ts.add_fld(name,gvn.type(val),mutable);
    if( _name != null ) _name = _name.make(_ts); // Re-attach name as needed
    add_def(val);
    gvn.rereg(this,value(gvn));
    return val;
  }
  // Update/modify a field
  public Node update( String name, int idx, Node val, GVNGCM gvn, byte mutable  ) {
    assert def_idx(_ts._ts.length)== _defs._len;
    int idx2 = _ts.find(name,idx);
    assert idx2 != -1;
    gvn.unreg(this);
    _ts = _ts.set_fld(idx2,gvn.type(val),mutable);
    if( _name != null ) _name = _name.make(_ts); // Re-attach name as needed
    set_def(def_idx(idx2),val,gvn);
    gvn.rereg(this,value(gvn));
    return val;
  }
  // Create or update as needed
  public void make_fld( String name, Node val, GVNGCM gvn, byte mutable ) {
    int idx = _ts.find(name,-1);
    if( idx == -1 ) create(name,    val,gvn,mutable);
    else            update(name,idx,val,gvn,mutable);
  }

  // Add a named FunPtr to a New.  Auto-inflates to a Unresolved as needed.
  public FunPtrNode add_fun( String name, FunPtrNode ptr, GVNGCM gvn ) {
    int idx = _ts.find(name,-1);
    if( idx == -1 ) {
      create(name,ptr,gvn,TypeStruct.ffinal());
    } else {
      Node n = _defs.at(def_idx(idx));
      if( n instanceof UnresolvedNode ) n.add_def(ptr);
      else n=new UnresolvedNode(n,ptr);
      update(name,idx,n,gvn,TypeStruct.ffinal());
    }
    return ptr;
  }

  // The current local scope ends, no more names will appear.  Forward refs
  // first found in this scope are assumed to be defined in some outer scope
  // and get promoted.  Other locals are no longer kept alive, but live or die
  // according to use.
  public void promote_forward(GVNGCM gvn, NewNode parent) {
    assert parent != null;
    TypeStruct ts = _ts;
    for( int i=0; i<ts._ts.length; i++ ) {
      Node n = fld(i);
      if( n != null && n.is_forward_ref() ) {
        parent.create(ts._flds[i],n,gvn,ts._finals[i]);
        gvn.remove_reg(this,def_idx(i));
        ts = ts.del_fld(i);
        i--;
      }
    }
    if( ts != _ts && _name != null ) _name = _name.make(ts); // Re-attach name as needed
    _ts = ts;
  }

  // Add PhiNodes and variable mappings for common definitions merging at the
  // end of an IfNode split.
  // - Errors are ignored for dead vars (ErrNode inserted into graph as instead
  //   of a syntax error)
  // - Unknown forward refs must be unknown on both branches and be immutable
  //   and will promote to the next outer scope.
  // - First-time defs on either branch must be defined on both branches.
  // - Both branches must agree on mutability
  // - Ok to be mutably updated on only one arm
  public void common( Parse P, GVNGCM gvn, Parse phi_errmsg, NewNode t, NewNode f, Node dull, Node t_sharp, Node f_sharp ) {
    // Unwind the sharpening
    for( int i=0; i<_ts._ts.length; i++ ) {
      if( in(def_idx(i))==dull ) {  // Found a use of 'dull'
        String name = _ts._flds[i]; // Field name sharpened in test
        // Find the matching field name in the true arm
        int tidx = def_idx(t._ts.find(name,-1));
        if( t.in(tidx)==t_sharp ) t.set_def(tidx,null,gvn);
        int fidx = def_idx(f._ts.find(name,-1));
        if( f.in(fidx)==f_sharp ) f.set_def(fidx,null,gvn);
      }
    }
    // Look for updates on either arm
    String[] tflds = t._ts._flds;
    String[] fflds = f._ts._flds;
    for( int idx=0; idx<tflds.length; idx++ ) {
      if( t.in(def_idx(idx))==null ) continue; // Unwound sharpening
      String name = tflds[idx];
      if( f._ts.find(name,-1) == -1 ) // If not on false side
        do_one_side(name,P,gvn,phi_errmsg,t,true);
      else
        do_both_sides(name,P,gvn,phi_errmsg,t,f);
    }
    for( int idx=0; idx<fflds.length; idx++ ) {
      if( f.in(def_idx(idx))==null ) continue; // Unwound sharpening
      String name = fflds[idx];
      if( t._ts.find(name,-1) == -1 ) // If not on true side
        do_one_side(name,P,gvn,phi_errmsg,f,false);
    }
  }

  // Called per name defined on only one arm of a trinary.
  // Produces the merge result.
  private void do_one_side(String name, Parse P, GVNGCM gvn, Parse phi_errmsg, NewNode x, boolean arm) {
    int xii = x._ts.find(name,-1);
    final byte xmut = x._ts._finals[xii];
    Node xn = x.in(def_idx(xii)), yn;
    ScopeNode scope = P.lookup_scope(name); // Find prior definition

    // Forward refs are not really a def, but produce a trackable definition
    // that must be immutable, and will eventually get promoted until it
    // reaches a scope where it gets defined.
    if( xn.is_forward_ref() ) { assert xmut == TypeStruct.ffinal(); create(name,xn,gvn,xmut); return; }

    // Check for mixed-mode updates.  'name' must be either fully mutable or
    // fully immutable at the merge point (or dead afterwards).  Since x was
    // updated on this branch, the variable was mutable beforehand.  Since it
    // was mutable and not changed on the other side, it remains mutable.
    if( scope == null )         // Found the prior definition.
      yn = fail(name,P,gvn,arm,xn,"defined");
    else if( xmut != TypeStruct.frw() )        // x-side is final but y-side is mutable.
      yn = fail(name,P,gvn,arm,xn,"final");
    else yn = scope.get(name);

    Node n = xn==yn ? xn : P.gvn(new PhiNode(phi_errmsg, P.ctrl(),xn,yn));
    (scope==null ? this : scope.stk()).make_fld(name,n,gvn,xmut);
  }

  private Node fail(String name, Parse P, GVNGCM gvn, boolean arm, Node xn, String msg) {
    return P.err_ctrl1("'"+name+"' not "+msg+" on "+!arm+" arm of trinary",gvn.type(xn).widen());
  }

  // Called per name defined on both arms of a trinary.
  // Produces the merge result.
  private void do_both_sides(String name, Parse P, GVNGCM gvn, Parse phi_errmsg, NewNode t, NewNode f) {
    int tii = t._ts.find(name,-1);
    int fii = f._ts.find(name,-1);
    byte tmut = t._ts._finals[tii];
    byte fmut = f._ts._finals[fii];
    Node tn = t.in(def_idx(tii));
    Node fn = f.in(def_idx(fii));
    byte mut_final= TypeStruct.ffinal();
    byte mut_ro   = TypeStruct.fro();
    byte mut_rw   = TypeStruct.frw();

    if( tn != null && tn.is_forward_ref() ) {
      assert tmut == mut_final;
      if( fn.is_forward_ref() ) {
        assert fmut == mut_final;
        throw AA.unimpl(); // Merge/U-F two forward refs
      }
      //update(name,P.err_ctrl1("'"+name+"' not defined on "+true+" arm of trinary",gvn.type(fn).widen()),gvn,TypeStruct.ffinal());
      //return;
      throw AA.unimpl();
    }
    if( fn != null && fn.is_forward_ref() ) {
      //update(name,P.err_ctrl1("'"+name+"' not defined on "+false+" arm of trinary",gvn.type(tn).widen()),gvn,TypeStruct.ffinal());
      //return;
      throw AA.unimpl();
    }

    // If either side does a final store, then the field is final afterwards
    if( tmut == mut_final || fmut == mut_final ) tmut = mut_final;
    else if( tmut == mut_ro || fmut == mut_ro ) tmut = mut_ro;
    else tmut = mut_rw;

    Node n = tn==fn ? fn : P.gvn(new PhiNode(phi_errmsg, P.ctrl(),tn,fn));
    make_fld(name,n,gvn,tmut);
  }

  // Replace uses of dull with sharp, used after an IfNode test
  void sharpen( GVNGCM gvn, Node dull, Node sharp, NewNode arm ) {
    assert dull != sharp;
    for( int i=0; i<_ts._ts.length; i++ ) // Fill in all fields
      if( in(def_idx(i))==dull ) {
        gvn.unreg(arm);
        arm.add_def(sharp);
        arm._ts = arm._ts.add_fld(_ts._flds[i],gvn.type(sharp),_ts._finals[i]);
        gvn.rereg(arm,arm.value(gvn));
      }
  }

  @Override public Node ideal(GVNGCM gvn) {
    // If the address is not looked at then memory contents cannot be looked at
    // and is dead.
    if( _uses._len==1 && _uses.at(0) instanceof OProjNode ) {
      boolean progress=false;
      for( int i=1; i<_defs._len; i++ )
        if( in(i)!=null )
          { set_def(i,null,gvn); progress=true; }
      return progress ? this : null;
    }
    return null;
  }

  // Produces a TypeMemPtr
  @Override public Type value(GVNGCM gvn) {
    // If the address is not looked at then memory contents cannot be looked at
    // and is dead.
    if( _uses._len==1 && _uses.at(0) instanceof OProjNode )
      return TypeTuple.make(TypeMem.XMEM,TypeMemPtr.OOP.dual());

    // Gather args and produce a TypeStruct
    Type[] ts = new Type[_ts._ts.length];
    for( int i=0; i<ts.length; i++ )
      // Limit type bounds, since error returns can be out-of-bounds
      ts[i] = gvn.type(fld(i)).bound(_ts.at(i));
    TypeStruct newt = TypeStruct.make(_ts._flds,ts,_ts._finals,_alias);

    // Check for TypeStructs with this same NewNode types occurring more than
    // CUTOFF deep, and fold the deepest ones onto themselves to limit the type
    // depth.  If this happens, the types become recursive with the
    // approximations happening at the deepest points.
    TypeStruct res = newt.approx(CUTOFF);
    TypeObj xs = _name == null ? res : _name.make(res); // Re-attach name as needed
    return TypeTuple.make(xs,TypeMemPtr.make(_alias,xs));
  }

  @Override public Type all_type() {
    return TypeTuple.make(xs(),TypeMemPtr.make(_alias,xs()));
  }

  // Clones during inlining all become unique new sites
  @Override @NotNull public NewNode copy( boolean copy_edges, GVNGCM gvn) {
    assert !_ts.above_center(); // Never in GCP when types are high
    // Split the original '_alias' class into 2 sub-aliases
    NewNode nnn = (NewNode)super.copy(copy_edges, gvn);
    nnn._alias = BitsAlias.new_alias(_alias); // Children alias classes, split from parent
    nnn._ts = _ts.make(false,BitsAlias.make0(nnn._alias));
    if( _name != null ) nnn._name = _name.make(nnn._ts); // Re-attach name as needed
    // The original NewNode also splits from the parent alias
    Type oldt = gvn.touched(this) ? gvn.type(this) : null;
    if( oldt != null ) gvn.unreg(this);
    _alias = BitsAlias.new_alias(_alias);
    _ts = _ts.make(false,BitsAlias.make0(_alias));
    if( _name != null ) _name = _name.make(_ts); // Re-attach name as needed
    if( oldt != null ) gvn.rereg(this,oldt);
    return nnn;
  }

  @Override public int hashCode() { return super.hashCode()+ _alias; }
  // Only ever equal to self, because of unique _alias.  We can collapse equal
  // NewNodes and join alias classes, but this is not the normal CSE and so is
  // not done by default.
  @Override public boolean equals(Object o) {  return this==o; }
}
