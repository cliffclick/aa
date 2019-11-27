package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.Util;
import org.jetbrains.annotations.NotNull;

// Merge all the fields of an object.  Slot 0 is the base object, field-less.
public class ObjMergeNode extends Node {
  private final int _alias;
  private Ary<String> _flds;

  ObjMergeNode( Node obj, int alias ) {
    super(OP_OBJ,obj);
    assert alias!= BitsAlias.ALL && alias!= BitsAlias.REC;
    _alias=alias;
    _flds = new Ary<>(new String[1]);
  }
  public void reset_to_init1() { _flds.set_len(_defs._len); }

  @Override String str() {
    SB sb = new SB().p('{');
    sb.p(in(0)._uid).p(":obj, ");
    for( int i=1; i<_defs._len; i++ )
      sb.p(in(i)==null?0:in(i)._uid).p(':').p(_flds.at(i)==null ? ""+i : _flds.at(i)).p(", ");
    return sb.unchar().unchar().p('}').toString();
  }

  // Return the index for a field.
  public int fld_idx(String tok) {
    // Search for the field by name, or if it is a number, use that number.
    if( Parse.isDigit((byte)tok.charAt(0)) ) {
      int idx = tok.charAt(0)-'0'+1;
      if( idx >= _defs._len )
        throw AA.unimpl();      // tuples need to extend to support the field number
    }
    // Search by name
    int idx;
    for( idx=1; idx<_flds._len; idx++ )
      if( Util.eq(tok,_flds.at(idx)) )
        break;
    if( idx <_flds._len ) return idx;
    // Field does not exist, just append it.
    _flds.push(tok);
    add_def(in(0));             // Clone from base object
    return _defs._len-1;
  }

  @Override public Node ideal(GVNGCM gvn) {
    assert !(in(0) instanceof ObjMergeNode); // Should not happen
    // Remove redundant and dead merges
    for( int i=1; i<_defs._len; i++ )
      if( in(i)==in(0) || gvn.type(in(i)).isa(Type.XSCALAR) ) {
        del(i);
        _flds.del(i);
        i--;
      }
    // Keep if making a skinny from a fat
    if( gvn.type(in(0)).isa(TypeMem.MEM) )
      return null;
    // If not merging anything
    return _defs._len==1 ? in(0) : null;
  }
  @Override public Type value(GVNGCM gvn) {
    // This ObjMerge can pull from either undistinguished memory or from a
    // prior same-alias object.
    Type t = gvn.type(in(0));
    if( !(t instanceof TypeObj) ) { // Handle undistinguished memory
      if( !(t instanceof TypeMem) ) // Probably ANY/ALL from GCP
        return t.above_center() ? TypeObj.XOBJ : TypeObj.OBJ;
      TypeMem tm = (TypeMem)t;
      TypeObj to = tm.at(_alias); // Get the specific memory type for this alias
      // Expect to get the right alias
      if( to._news.getbit()!=_alias )
        // TODO: this is conservative; really can make a bottom-end type of the
        // correct alias#, and set specific fields to known values.
        return to.above_center() ? TypeObj.XOBJ : TypeObj.OBJ;
      t = to;
    }
    // This is a field merge, so we expect the type to be a collection of
    // fields... a TypeStruct.
    if( !(t instanceof TypeStruct) ) throw AA.unimpl();
    TypeStruct ts = (TypeStruct)t;
    assert Math.abs(ts._news.getbit())==_alias;
    // Merge any modified fields.  These are precise updates.
    for( int i=1; i<_defs._len; i++ ) {
      String fld = _flds.at(i);
      Type tf = gvn.type(in(i));
      if( !(tf instanceof TypeStruct) ) // Field not well-type, so the merge is not well typed
        return ts.above_center() ? TypeObj.XOBJ : TypeObj.OBJ;
      // Each field has the type of an entire struct, but we only want to the field.
      TypeStruct tfs = (TypeStruct)tf;
      int fidx = tfs.find(fld);     // Find the field
      byte fin = tfs._finals[fidx]; // Final update, or not
      Type tfv = tfs._ts[fidx];     // Field type
      // Result type is the base type, plus all merged modifications
      ts = (TypeStruct)ts.st(fin,fld,tfv);
    }
    return ts;
  }
  @Override public Type all_type() { return TypeObj.OBJ; }
  @Override @NotNull public ObjMergeNode copy( boolean copy_edges, GVNGCM gvn) {
    ObjMergeNode obj = (ObjMergeNode)super.copy(copy_edges, gvn);
    obj._flds = new Ary<>(_flds._es.clone(),_flds._len);
    return obj;
  }

}
