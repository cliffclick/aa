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
  public int _alias;          // Alias class
  TypeStruct _ts;             // base Struct
  boolean _is_closure;        // For error messages
  private TypeName _name;     // If named, this is the name and _ts is the base

  // NewNodes can participate in cycles, where the same structure is appended
  // to in a loop until the size grows without bound.  If we detect this we
  // need to approximate a new cyclic type.
  public final static int CUTOFF=2; // Depth of types before we start forcing approximations

  // NewNodes do not really need a ctrl; useful to bind the upward motion of
  // closures so variable stores can more easily fold into them.
  public NewNode( Node ctrl, boolean is_closure ) {
    super(OP_NEW,ctrl);
    _alias = BitsAlias.new_alias(BitsAlias.REC);
    _ts = TypeStruct.make_alias(_alias); // No fields
    _name =null;
    _is_closure = is_closure;
  }
  String xstr() { return "New*"+_alias; } // Self short name
  String  str() { return "New"+xs(); } // Inline less-short name

  private int def_idx(int fld) { return fld+1; } // Skip ctrl in slot 0
  Node fld(int fld) { return in(def_idx(fld)); } // Node for field#
  private TypeObj xs() { return _name == null ? _ts : _name; }

  public Node get(String name) { return fld(_ts.find(name)); }
  public boolean exists(String name) { return _ts.find(name)!=-1; }
  public boolean is_mutable(String name) { return _ts._finals[_ts.find(name)] == TypeStruct.frw(); }
  public boolean is_final(int idx) { return _ts._finals[idx] == TypeStruct.ffinal(); }

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

  // Create a field from parser for an inactive this
  public void create( String name, Node val, byte mutable, GVNGCM gvn  ) {
    gvn.unreg(this);
    create_active(name,val,mutable,gvn);
    for( Node use : _uses )
      gvn.setype(use,use.value(gvn));
    assert gvn.touched(this);
  }

  // Create a field from parser for an active this
  public void create_active( String name, Node val, byte mutable, GVNGCM gvn  ) {
    assert !gvn.touched(this);
    assert def_idx(_ts._ts.length)== _defs._len;
    assert _ts.find(name) == -1; // No dups
    _ts = _ts.add_fld(name,gvn.type(val),mutable);
    if( _name != null ) _name = _name.make(_ts); // Re-attach name as needed
    add_def(val);
  }
  // Update/modify a field, by field number
  public Node update( int fidx , Node val, byte mutable, GVNGCM gvn  ) {
    Type oldt = gvn.type(this);
    gvn.unreg(this);
    update_active(fidx,val,mutable,gvn);
    gvn.rereg(this,oldt);
    return val;
  }
  // Update/modify a field, by field number for an active this
  private void update_active( int fidx , Node val, byte mutable, GVNGCM gvn  ) {
    assert def_idx(_ts._ts.length)== _defs._len;
    assert fidx != -1;
    _ts = _ts.set_fld(fidx,gvn.type(val),mutable);
    if( _name != null ) _name = _name.make(_ts); // Re-attach name as needed
    set_def(def_idx(fidx),val,gvn);
  }

  // Add a named FunPtr to a New.  Auto-inflates to a Unresolved as needed.
  public FunPtrNode add_fun( Parse bad, String name, FunPtrNode ptr, GVNGCM gvn ) {
    int fidx = _ts.find(name);
    if( fidx == -1 ) {
      create_active(name,ptr,TypeStruct.ffinal(),gvn);
    } else {
      Node n = _defs.at(def_idx(fidx));
      if( n instanceof UnresolvedNode ) n.add_def(ptr);
      else n = new UnresolvedNode(bad,n,ptr);
      update_active(fidx,n,TypeStruct.ffinal(),gvn);
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
        parent.create(ts._flds[i],n,ts._finals[i],gvn);
        gvn.remove_reg(this,def_idx(i));
        ts = ts.del_fld(i);
        i--;
      }
    }
    if( ts != _ts && _name != null ) _name = _name.make(ts); // Re-attach name as needed
    _ts = ts;
  }

  @Override public Node ideal(GVNGCM gvn) {
    // If the address is not looked at then memory contents cannot be looked at
    // and is dead.
    if( _uses._len==1 && _uses.at(0) instanceof OProjNode ) {
      boolean progress=false;
      for( int i=1; i<_defs._len; i++ )
        if( in(i)!=null ) {
          set_def(i,null,gvn);
          progress=true;
          if( is_dead() ) break;
        }
      return progress ? this : null;
    }
    return null;
  }

  // Produces a TypeMemPtr
  @Override public Type value(GVNGCM gvn) {
    // If the address is not looked at then memory contents cannot be looked at
    // and is dead.
    if( _uses._len==1 && _uses.at(0) instanceof OProjNode )
      return all_type().dual();

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
