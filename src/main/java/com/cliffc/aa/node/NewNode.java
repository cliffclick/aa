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
// NewNode produces a Tuple type, one entry (and ProjNode) per field.  Each
// ProjNode (field) can go dead independently.
//
// NewNodes have a unique alias class - they do not alias with any other
// NewNode, even if they have the same type.

public class NewNode extends Node {
  // Unique alias class, one class per unique memory allocation site.
  // Only effectively-final, because the copy/clone sets a new alias value.
  private int _alias;           // Alias class
  TypeStruct _ts;               // Base result struct
  private TypeName _name;       // Optional name wrapper

  // NewNodes can participate in cycles, where the same structure is appended
  // to in a loop until the size grows without bound.  If we detect this we
  // need to approximate a new cyclic type.
  public final static int CUTOFF=2; // Depth of types before we start forcing approximations

  public NewNode( ) {
    super(OP_NEW,(Node)null);   // no ctrl field
    _alias = BitsAlias.new_alias(BitsAlias.REC);
    _name = null;
    _ts = TypeStruct.make_alias(_alias); // No fields
    //TypeStruct ts = (TypeStruct)obj.base();
    //// Reconstruct obj with 'this' _news
    //_ts = TypeStruct.make(ts._flds,ts._ts,ts._finals,BitsAlias.make0(_alias));
    //// If a TypeName wrapper, rewrap
    //if( obj instanceof TypeName ) obj = ((TypeName)obj).make(_ts);
    //else obj = _ts;
    //_obj = obj;
    //_ptr = TypeMemPtr.make(_alias,obj);
  }
  String xstr() { return "New*"+_alias; } // Self short name
  String  str() { return "New"+(_name==null ? _ts : _name); } // Inline less-short name

  private int def_idx(int fld) { return fld+1; } // Skip ctrl in slot 0
  Node fld(int fld) { return in(def_idx(fld)); } // Node for field#

  public Node get(String name) { return in(def_idx(_ts.find(name,-1))); }
  public boolean exists(String name) { return _ts.find(name,-1)!=-1; }
  public boolean is_mutable(String name) { return _ts._finals[_ts.find(name,-1)] == TypeStruct.frw(); }

  // Called when folding a Named Constructor into this allocation site
  void set_name( GVNGCM gvn, TypeName name ) {
    //TypeTuple oldt = (TypeTuple)gvn.type(this);
    //TypeStruct oldts = (TypeStruct)oldt.at(0);
    //TypeMemPtr poldt = (TypeMemPtr)oldt.at(1);
    //gvn.unreg(this);
    //TypeStruct ts = (TypeStruct)to.base();
    //// Reconstruct obj with 'this' _news
    //TypeStruct ts2 = TypeStruct.make(ts._flds,ts._ts,oldts._finals,BitsAlias.make0(_alias));
    //assert ts2.isa(_ts);
    //_ts = ts2;
    //_obj = to.make(_ts);
    //_ptr = TypeMemPtr.make(_alias,_obj);
    //TypeMemPtr nameptr = _ptr.make(to.make(poldt._obj));
    //gvn.rereg(this,nameptr);
    throw AA.unimpl();
  }
  TypeObj ptr() {
    throw AA.unimpl();
  }

  // Add a field to a New
  public void add_fld( String name, Type t, Node n, boolean mutable ) {
    assert !Env.GVN.touched(this);
    _ts = _ts.add_fld(name,t,mutable);
    if( _name != null ) _name = _name.make(_ts);
    add_def(n);
  }
  // Update/modify a field
  public Node update( String name, int idx, Node val, GVNGCM gvn, boolean mutable  ) {
    assert !Env.GVN.touched(this);
    assert def_idx(_ts._ts.length)== _defs._len;
    int idx2 = _ts.find(name,idx);
    if( idx2 == -1 ) {          // Insert in this scope
      add_fld(name,gvn.type(val),val,mutable);
    } else {                    // Overwrite in this scope
      _ts = _ts.set_fld(idx2,gvn.type(val),mutable);
      if( _name != null ) _name = _name.make(_ts);
      set_def(def_idx(idx2),val,gvn);
    }
    return val;
  }

  // Add a named FunPtr to a New.  Auto-inflates to a Unresolved as needed.
  public FunPtrNode add_fun( String name, FunPtrNode ptr ) {
    int idx = _ts.find(name,-1);
    if( idx == -1 ) {
      add_fld(name,ptr._t,ptr,false);
    } else {
      Node n = _defs.at(def_idx(idx));
      if( n instanceof UnresolvedNode ) n.add_def(ptr);
      else set_def(def_idx(idx),n=new UnresolvedNode(n,ptr),null);
      _ts = _ts.set_fld(idx,n.all_type(),false);
      if( _name != null ) _name = _name.make(_ts);
    }
    return ptr;
  }

  // The current local scope ends, no more names will appear.  Forward refs
  // first found in this scope are assumed to be defined in some outer scope
  // and get promoted.  Other locals are no longer kept alive, but live or die
  // according to use.
  public void promote_forward(GVNGCM gvn, NewNode parent) {
    assert parent != null;
    for( int i=0; i<_ts._ts.length; i++ ) {
      Node n = fld(i);
      if( n != null && n.is_forward_ref() ) {
        parent.update(_ts._flds[i],-1,n,gvn,false);
        set_def(def_idx(i),null,gvn);
      }
    }
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
    for( int i=1; i<_defs._len; i++ ) {
      if( in(i)==dull && t.in(i)==t_sharp ) t.set_def(i,null,gvn);
      if( in(i)==dull && f.in(i)==f_sharp ) f.set_def(i,null,gvn);
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
    boolean x_is_mutable = x._ts._finals[xii] == TypeStruct.frw();
    Node xn = x.in(def_idx(xii)), yn;
    ScopeNode scope = P.lookup_scope(name); // Find prior definition

    // Forward refs are not really a def, but produce a trackable definition
    // that must be immutable, and will eventually get promoted until it
    // reaches a scope where it gets defined.
    if( xn.is_forward_ref() ) { assert !x_is_mutable; update(name,-1,xn,gvn,false); return; }

    // Check for mixed-mode updates.  'name' must be either fully mutable or
    // fully immutable at the merge point (or dead afterwards).  Since x was
    // updated on this branch, the variable was mutable beforehand.  Since it
    // was mutable and not changed on the other side, it remains mutable.
    if( scope == null )         // Found the prior definition.
      yn = fail(name,P,gvn,arm,xn,"defined");
    else if( !x_is_mutable )        // x-side is final but y-side is mutable.
      yn = fail(name,P,gvn,arm,xn,"final");
    else yn = scope.get(name);

    (scope==null ? this : scope.stk()).update(name,-1,xn==yn ? xn : P.gvn(new PhiNode(phi_errmsg, P.ctrl(),xn,yn)),gvn,x_is_mutable);
  }

  private Node fail(String name, Parse P, GVNGCM gvn, boolean arm, Node xn, String msg) {
    return P.err_ctrl1("'"+name+"' not "+msg+" on "+!arm+" arm of trinary",gvn.type(xn).widen());
  }

  // Called per name defined on both arms of a trinary.
  // Produces the merge result.
  private void do_both_sides(String name, Parse P, GVNGCM gvn, Parse phi_errmsg, NewNode t, NewNode f) {
    int tii = t._ts.find(name,-1);
    int fii = f._ts.find(name,-1);
    boolean t_is_mutable = t._ts._finals[tii] == TypeStruct.frw();
    boolean f_is_mutable = f._ts._finals[fii] == TypeStruct.frw();
    Node tn = t.in(def_idx(tii));
    Node fn = f.in(def_idx(fii));

    if( tn != null && tn.is_forward_ref() ) {
      assert !t_is_mutable;
      if( fn.is_forward_ref() ) {
        assert !f_is_mutable;
        throw AA.unimpl(); // Merge/U-F two forward refs
      }
      //update(name,P.err_ctrl1("'"+name+"' not defined on "+true+" arm of trinary",gvn.type(fn).widen()),gvn,false);
      //return;
      throw AA.unimpl();
    }
    if( fn != null && fn.is_forward_ref() ) {
      //update(name,P.err_ctrl1("'"+name+"' not defined on "+false+" arm of trinary",gvn.type(tn).widen()),gvn,false);
      //return;
      throw AA.unimpl();
    }

    // Check for mixed-mode updates.  'name' must be either fully mutable
    // or fully immutable at the merge point (or dead afterwards).
    if( t_is_mutable != f_is_mutable ) {
      //update(name,P.err_ctrl1(" is only partially mutable",gvn.type(tn).widen()),gvn,false);
      //return;
      throw AA.unimpl();
    }

    update(name,-1,tn==fn ? fn : P.gvn(new PhiNode(phi_errmsg, P.ctrl(),tn,fn)),gvn,t_is_mutable);
  }

  // Replace uses of dull with sharp, used after an IfNode test
  void sharpen( Node dull, Node sharp, NewNode arm ) {
    assert dull != sharp;
    for( int i=1; i<_defs._len; i++ ) // Fill in all fields
      if( in(i)==dull )
        throw AA.unimpl();
      //arm.add_fld
      //arm.add_def(in(i)==dull ? sharp : null);
    // Update sharpen value lookup
    //for( String name : _vals.keySet() ) {
    //  int idx = _vals.get(name);
    //  if( in(idx)==dull ) {
    //    arm._vals.put(name,idx);
    //    if( _ms.get(idx) ) arm._ms.set(idx);
    //  }
    //}
  }

  @Override public Node ideal(GVNGCM gvn) { return null; }

  // Produces a TypeMemPtr
  @Override public Type value(GVNGCM gvn) {
    // Gather args and produce a TypeStruct
    Type[] ts = new Type[_ts._ts.length];
    for( int i=0; i<_ts._ts.length; i++ ) {
      Type t = ts[i] = gvn.type(fld(i));
      assert _ts.at(i).dual().isa(t) && t.isa(_ts.at(i));
    }
    TypeStruct newt = TypeStruct.make(_ts._flds,ts,_ts._finals,_alias);

    // Check for TypeStructs with this same NewNode types occurring more than
    // CUTOFF deep, and fold the deepest ones onto themselves to limit the type
    // depth.  If this happens, the types become recursive with the
    // approximations happening at the deepest points.
    TypeStruct res = newt.approx(CUTOFF);
    TypeObj res2 = _name == null ? res : _name.make(res);
    return TypeMemPtr.make(_alias,res2);
  }

  @Override public Type all_type() {
    return TypeMemPtr.make(_alias,_name==null ? _ts : _name);
  }

  // Clones during inlining all become unique new sites
  @Override @NotNull NewNode copy( GVNGCM gvn) {
    //// Split the original '_alias' class into 2 sub-classes
    //NewNode nnn = (NewNode)super.copy(gvn);
    //nnn._alias = BitsAlias.new_alias(_alias); // Children alias classes, split from parent
    //nnn._ptr = TypeMemPtr.make(nnn._alias,nnn._obj = _obj.realias(nnn._alias));
    //// The original NewNode also splits from the parent alias
    //Type oldt = gvn.type(this);
    //gvn.unreg(this);
    //_alias = BitsAlias.new_alias(_alias);
    //_ptr = TypeMemPtr.make(_alias,_obj = _obj.realias(_alias));
    //gvn.rereg(this,oldt);
    //return nnn;
    throw AA.unimpl();
  }

  @Override public int hashCode() { return super.hashCode()+ _alias; }
  // Only ever equal to self, because of unique _alias.  We can collapse equal
  // NewNodes and join alias classes, but this is not the normal CSE and so is
  // not done by default.
  @Override public boolean equals(Object o) {  return this==o; }
}
