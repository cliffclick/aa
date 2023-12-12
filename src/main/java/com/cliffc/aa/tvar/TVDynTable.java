package com.cliffc.aa.tvar;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.Arrays;

import static com.cliffc.aa.AA.TODO;
import static com.cliffc.aa.util.Util.uid;

/** A Type for offsets to a DynLoad.
 *
 * Layout is in pairs of fields of the TVStruct with interpretation of the
 * field labels.  Labels always end in a Syntax UID of either a DynField or or
 * an Apply.
 * - "Muid" - Match UID of a DynField.  Arg is the MATCH
 * - "Puid" - Pattern; UID is the same. Arg is the PATTERN
 * - "Auid" - Apply UID; arg is a nested TVDynTable
 * - "Buid" - Balanced other half of Apply, to keep the args in pairs.  Arg is null.
 */
public class TVDynTable extends TVStruct {

  private String[] _labels;
  
  public TVDynTable() { super(true); _labels = new String[0]; }

  @Override public TVDynTable as_dyn() { return this; }

  // Add a DynField reference to this table
  public void add_dyn( int uid, TV3 match, TV3 pattern ) {
    add_fld(uid("M",uid),match  ,true);
    add_fld(uid("P",uid),pattern,true);
    if( _labels.length < _flds.length )
      _labels = Arrays.copyOf(_labels,_flds.length);
  }

  // Add a Apply reference to this table
  public void add_apy( int uid, TV3 tv ) {
    add_fld(uid("A",uid),tv,true);
    add_fld(uid("B",uid),tv,true);
    if( _labels.length < _flds.length )
      _labels = Arrays.copyOf(_labels,_flds.length);
  }

  // Find a DynField reference at the top level
  public String find_label(int uid) {
    int idx = idx(uid("M",uid));
    return idx== -1 ? null : _labels[idx];
  }
  
  @Override int eidx() { return TVErr.XDYN; }

  // -------------------------------------------------------------

  // Resolve all pairs of inputs as DynTables
  private static final VBitSet VBS = new VBitSet();
  public boolean resolve(boolean test) { VBS.clear(); return _resolve(test); };
  private boolean _resolve( boolean test ) {
    if( VBS.tset(_uid) ) return false;
    boolean progress = false;
    for( int i=0; i<len(); i += 2 )
      if( fld(i).charAt(0)=='M' ) {
        progress |= resolve(i,arg(i),arg(i+1), test);
      } else {
        assert fld(i).charAt(0)=='A';
        if( arg(i) instanceof TVDynTable nest )
          progress |= nest._resolve(test);
      }
    return progress;
  }

  // Try to resolve the label; return true if progress
  private boolean resolve(int idx, TV3 matches, TV3 pat, boolean test) {
    if( !(matches instanceof TVStruct str) ) return false; // No progress until a TVStruct
    // Resolve field by field, removing resolved fields.  Should be 1 YES resolve in the end.
    boolean progress = false;
    for( int i=0; i<str.len(); i++ ) {
      // Trial unify
      TV3 match = str.arg(i);   // An individual match
      int rez = match.trial_unify_ok(pat);
      // 7=NO, 3=MAYBE, 1=YES
      if( rez!=3 ) {          // Either a YES or a NO
        if( test ) return true; // Always progress from here
        progress = true;
        str = handle_match(idx,rez,match,pat,str,i--);
        pat = pat.find();
      }
      // Pending MAYBEs remain, and need progress elsewhere
    }
    // TODO: Resolving with a single Maybe.
    // If, later this maybe turns into a Yes, we're just making a Yes sooner.
    // If, later this maybe turns into a No, then we're in an error situation already.
    // To get consistent errors, we need to always have the sane field be the Last Maybe
    if( str.len()==1 && _labels[idx]==null ) {
      if( test ) return true; // Gonna match the Last Maybe
      progress = true;
      handle_match(idx,1,str.arg(0),pat,str,0);
    }

    return progress;
  }

  private TVStruct handle_match( int idx, int rez, TV3 match, TV3 pat, TVStruct str, int i ) {
    if( rez==1 ) {        // YES: record the resolved field label
      String label = _labels[idx];
      if( label != null ) throw TODO("Two valid choices: "+label+" and "+str.fld(i));
      _labels[idx] = str.fld(i);
      // We got the One True Match, unify
      match.unify(pat,false);
    }
    // Fields that resolve as either YES or NO are removed from the list,
    // since they can never change their answer.  Make a fresh copy, and
    // remove the field.
    str = (TVStruct)str.fresh();
    str.del_fld0(i);
    _args[idx] = str;
    return str;
  }
  
  // True if ALL resolved
  public boolean all_resolved() { VBS.clear(); return _all_resolved(); };
  private boolean _all_resolved() {
    if( VBS.tset(_uid) ) return true;
    boolean resolved = true;
    for( int i=0; i<len(); i += 2 )
      if( fld(i).charAt(0)=='M' )
        resolved &= _labels[i]!=null;
      else {
        assert fld(i).charAt(0)=='A';
        if( arg(i) instanceof TVDynTable nest )
          resolved &= nest._all_resolved();
      }
    return resolved;
  }
  
  // -------------------------------------------------------------
  @Override public void _union_impl( TV3 tv3 ) {
    for( int i=0; i<_labels.length; i+=2 )
      if( _labels[i]!=null )
        throw TODO();
  }
  
  // -------------------------------------------------------------
  @Override boolean _fresh_unify_impl(TV3 tv3, boolean test) {
    throw TODO();
  }
  
  
  // -------------------------------------------------------------
  @Override int _trial_unify_ok_impl( TV3 pat ) {
    throw TODO();
  }

  @Override boolean _exact_unify_impl(TV3 tv3) {
    throw TODO();
  }
  @Override void _widen( byte widen ) {
    throw TODO();
  }
  
  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) {
    throw TODO();
  }

  @Override public TVDynTable copy() {
    TVDynTable tab = (TVDynTable)super.copy();
    tab._labels = _labels.clone();
    return tab;
  }

  private static final VBitSet HDVBS = new VBitSet();
  boolean hasDyn() { HDVBS.clear(); return _hasDyn(); };
  private boolean _hasDyn() {
    if( HDVBS.tset(_uid) ) return false;
    for( int i=0; i<len(); i+=2 )
      if( _flds[i].charAt(0)=='M' ||
          (arg(i) instanceof TVDynTable tdyn && tdyn._hasDyn()) )
        return true;
    return false;
  }
  
  @Override public VBitSet _get_dups_impl(VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    if( !hasDyn() ) return dups;
    for( int i=0; i<len(); i++ )
      _args[i]._get_dups(visit,dups,debug,prims);
    return dups;
  }
  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    if( !debug && !hasDyn() ) return sb.p("-");
    sb.p("[[  ");
    for( int i=0; i<len(); i+=2 ) {
      sb.p(_flds[i]).p(": ");
      if( _flds[i].charAt(0)=='M' ) {
        if( _labels[i]==null ) {
          _args[i  ]._str(sb,visit,dups,debug,prims);
          sb.p(" in ");
          _args[i+1]._str(sb,visit,dups,debug,prims);
        } else {
          // Fully resolved
          sb.p(_labels[i]).p('=');
          _args[i+1]._str(sb,visit,dups,debug,prims);
        }
      } else {
        _args[i+1]._str(sb,visit,dups,debug,prims);
      }
      sb.p(", ");
    }
    return sb.unchar(2).p("]]");
  }
}
