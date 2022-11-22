package com.cliffc.aa.tvar;

import com.cliffc.aa.type.TypeStruct;
import com.cliffc.aa.util.*;

import static com.cliffc.aa.AA.unimpl;

/** A type struct
 *
 */
public class TVStruct extends TV3 {

  // The set of field labels, 1-to-1 with TV3 field contents.
  // Most field operations are UNORDERED, so we generally need to search the fields by string
  private String[] _flds;       // Field labels
  // True if more fields can be added.  Generally false for a known Struct, and
  // true for a Field reference to an unknown struct.
  boolean _open;
  
  public TVStruct( Ary<String> flds ) {
    super(true,new TV3[flds.len()]);
    _open = false;              // Made from a StructNode; is closed
    // Set all field names
    _flds = flds.asAry();
  }

  // Used during cyclic construction
  public void set_fld(int i, TV3 fld) { _args[i] = fld; }

  // Return the TV3 for field 'fld' or null if missing
  public TV3 fld(String fld) {
    int i = Util.find(_flds,fld);
    return i<0 ? null : _find(i);
  }
  
  // -------------------------------------------------------------
  @Override void _union_impl(TV3 that) {
    if( !(that instanceof TVBase base) ) throw unimpl();
    throw unimpl();
  }

  @Override boolean _unify_impl(TV3 that, boolean test ) {
    throw unimpl();
  }
  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    // Find the clazz tag, if any
    String is_clz = null;
    for( String fld : _flds )
      if( fld.endsWith(":") && // A nomative tag becomes the clazz
          (is_clz==null || fld.length() > is_clz.length() ) )
        is_clz = fld;
    if( is_clz!=null) sb.p(is_clz);

    boolean is_tup = _flds.length==0 || Character.isDigit(_flds[0].charAt(0));
    sb.p(is_tup ? "(" : "@{");
    if( _args==null ) sb.p(", ");
    else {
      for( int idx : sorted_flds() ) {
        String fld = _flds[idx];
        if( Util.eq(fld,is_clz)) continue; // Clazz marker name, not currently used
        // Skip resolved field names in a tuple
        if( !is_tup || TVField.is_resolving(fld) )
          sb.p(fld).p("= ");
        _args[idx]._str(sb,visit,dups,debug).p(is_tup ? ", " : "; ");
      }
    }
    if( _open ) sb.p(" ..., ");
    sb.unchar(2);
    sb.p(!is_tup ? "}" : ")");
    return sb;
  }

  // Stoopid hand-rolled bubble sort
  private int[] sorted_flds() {
    int len = _flds.length;
    int[] is = new int[len];
    for( int i=0; i<len; i++ ) is[i] = i;
    for( int i=0; i<len; i++ )
      for( int j=i+1; j<len; j++ )
        if( _flds[is[j]].compareTo(_flds[is[i]]) < 0 )
          { int tmp = is[i]; is[i] = is[j]; is[j] = tmp; }
    return is;
  }

}
