package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.Util;
import org.jetbrains.annotations.NotNull;
import java.util.BitSet;

// Merge all the fields of an object.  Slot 0 is the base object, field-less.
public class ObjMergeNode extends Node {
  int _alias;
  private Ary<String> _flds;

  ObjMergeNode( Node obj, int alias ) {
    super(OP_OBJ,obj);
    assert alias!= BitsAlias.ALL && alias!= BitsAlias.REC;
    _alias=alias;
    _flds = new Ary<>(new String[1]);
  }
  @Override public void reset_to_init1(GVNGCM gvn) { _flds.set_len(_defs._len); }

  @Override String str() {
    SB sb = new SB().p('#').p(_alias).p('{');
    sb.p(in(0)._uid).p(":obj, ");
    for( int i=1; i<_defs._len; i++ )
      sb.p(in(i)==null?0:in(i)._uid).p(':').p(_flds.at(i)==null ? ""+i : _flds.at(i)).p(", ");
    return sb.unchar().unchar().p('}').toString();
  }

  // Search for the field by name, or if it is a number, use that number.
  // If not found, max length.
  private int fld_idx(String tok) {
    if( Parse.isDigit((byte)tok.charAt(0)) )
      return tok.charAt(0)-'0'+1;
    // Search by name
    for( int idx=1; idx<_flds._len; idx++ )
      if( Util.eq(tok,_flds.at(idx)) )
        return idx;
    return _flds._len;
  }

  // Return the index for a field.
  public int fld_idx(String tok, GVNGCM gvn) {
    // Search for the field by name, or if it is a number, use that number.
    int idx = fld_idx(tok);
    if( idx <_flds._len ) return idx;
    while( idx >= _flds._len ) {
      // Field does not exist, just append it.
      assert !gvn.touched(this);  // Not in GVN / HashMap
      _flds.push(tok);
      add_def(in(0));             // Clone from base object
    }
    return idx;
  }

  // Return the Node for a field, without extending the index
  public Node fld2node(String tok) {
    int idx = fld_idx(tok);
    return in(idx<_defs._len ? idx : 0);
  }
  
  @Override public Node ideal(GVNGCM gvn) {
    assert !(in(0) instanceof ObjMergeNode) || ((ObjMergeNode)in(0))._alias==_alias; // Should not happen
    // Remove redundant and dead merges
    for( int i=1; i<_defs._len; i++ )
      if( in(i)==in(0) || gvn.type(in(i)).isa(Type.XSCALAR) ) {
        del(i);
        _flds.del(i);
        i--;
      }

    // If coming from a MemMerge in slot 0, peek thru
    if( in(0) instanceof MemMergeNode )
      return set_def(0,((MemMergeNode)in(0)).obj(_alias,gvn),gvn);

    // Keep if making a skinny from a fat, but if single-entry and already skinny, toss it
    if( !gvn.type(in(0)).isa(TypeMem.MEM) && _defs._len==1 )
      return in(0);
    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    // This ObjMerge can pull from either undistinguished memory or from a
    // prior same-alias object.
    Type t = gvn.type(in(0));
    if( !(t instanceof TypeObj) ) { // Handle undistinguished memory
      if( !(t instanceof TypeMem) ) // Probably ANY/ALL from GCP
        return all_type(t);
      TypeMem tm = (TypeMem)t;
      TypeObj to = tm.at(_alias); // Get the specific memory type for this alias
      // Expect to get the right alias
      if( to._news.getbit()!=_alias )
        // TODO: this is conservative; really can set specific fields to known values.
        return all_type(to);
      t = to;
    }
    // This is a field merge, so we expect the type to be a collection of
    // fields... a TypeStruct.
    if( !(t instanceof TypeStruct) ) return all_type(t);
    TypeStruct ts = (TypeStruct)t;
    assert Math.abs(ts._news.getbit())==_alias;
    // Merge any modified fields.  These are precise updates.
    for( int i=1; i<_defs._len; i++ ) {
      String fld = _flds.at(i);
      Type tf = gvn.type(in(i));
      if( !(tf instanceof TypeStruct) ) // Field not well-type, so the merge is not well typed
        return all_type(ts);
      // Each field has the type of an entire struct, but we only want to the field.
      TypeStruct tfs = (TypeStruct)tf;
      int fidx = tfs.find(fld);     // Find the field
      if( fidx == -1 ) return all_type(ts); // No such field, types need to propagate
      byte fin = tfs._finals[fidx]; // Final update, or not
      Type tfv = tfs._ts[fidx];     // Field type
      // Result type is the base type, plus all merged modifications
      ts = (TypeStruct)ts.st(fin,fld,tfv);
    }
    return ts;
  }
  private Type all_type(Type t) { Type at = all_type(); return t.above_center() ? at.dual() : at; }
  @Override public Type all_type() { return TypeObj.make0(false,BitsAlias.make0(_alias)); }
  @Override public int hashCode() { return super.hashCode()+_alias+_flds.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof ObjMergeNode) ) return false;
    ObjMergeNode obj = (ObjMergeNode)o;
    return _alias==obj._alias && _flds.equals(obj._flds);
  }
  @Override @NotNull public ObjMergeNode copy( boolean copy_edges, GVNGCM gvn) {
    ObjMergeNode obj = (ObjMergeNode)super.copy(copy_edges, gvn);
    obj._flds = new Ary<>(_flds._es.clone(),_flds._len);
    return obj;
  }
  @Override void update_alias( Node copy, BitSet aliases, GVNGCM gvn ) {
    if( !aliases.get(_alias) ) return;
    int alias = BitsAlias.get_kid(_alias);
    ((ObjMergeNode)copy)._alias = alias;
    assert gvn.touched(this);
    Type oldt = gvn.unreg(this);
    _alias = alias+1;
    gvn.rereg(this,oldt);
  }
}
