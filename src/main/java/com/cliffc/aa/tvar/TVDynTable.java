package com.cliffc.aa.tvar;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.Arrays;
import java.util.HashSet;
import java.util.function.IntSupplier;

import static com.cliffc.aa.AA.TODO;

/** A Type for offsets to a DynLoad.
 *
 * Args are in pairs; for a unresolved DynField its (match,pattern).
 * For a resolved DynField its (null,pattern) or ((),pattern).
 * For an Apply, its (apply,null) and the apply is either a Leaf (empty) or
 * nested a TVDynField.
 */
public class TVDynTable extends TV3 {

  private int _max;             // In-use count, for array-doubling.  Counts *pairs* in _args[].

  private IntSupplier[] _uids;  // Which Syntaxes/Nodes

  private long[] _cmps;         // Prior match results; 2 bits for (1,2,3) becomes (1,3,7 in trial_resolve)
  
  private String[] _labels;     // Resolved DynField labels

  public TVDynTable() { }

  // Keeping max as the number of conceptual entities, but DynFields need a
  // pair of TV3 edges.
  @Override public int len() { return _max*2; }
  private TV3 first(int idx) { return arg(idx*2  ); }
  private TV3 secnd(int idx) { return arg(idx*2+1); }
  private void set_match(int idx, TV3 match) { _args[idx*2] = match; }

  @Override public TVDynTable as_dyn() { return this; }

  // [match,pattern] pairs; if pattern is null this is an Apply (a nested
  // TVDynTable) else this is a DynField
  private boolean is_dyn(int idx) { return secnd(idx)!=null; }

  // Add a DynField reference to this table
  public boolean add_dyn( IntSupplier uid, TV3 match, TV3 pattern ) {
    assert !unified();
    if( _args==null ) {
      _args = new TV3[2];
      _uids = new IntSupplier[1];
      _cmps = new long[1];
      _labels = new String[1];
    }
    if( _max == _uids.length ) {
      int len = _max*2;
      _args  = Arrays.copyOf(_args  ,len*2);
      _uids  = Arrays.copyOf(_uids  ,len);
      _cmps  = Arrays.copyOf(_cmps ,len);
      _labels= Arrays.copyOf(_labels,len);
    }
    _args[len()  ] = match;
    _args[len()+1] = pattern;
    _uids[_max++ ] = uid;
    if( uid instanceof Node node )
      deps_add_deep(node);
    return true;
  }

  // Add a Apply reference to this table
  public boolean add_apy( IntSupplier uid, TV3 tv ) {  return add_dyn(uid,tv,null);  }

  private int idx(IntSupplier uid) {
    for( int i=0; i<_max; i++ )
      if( _uids[i]==uid )
        return i;
    return -1;
  }

  // Find TV3 reference for an Apply
  public TV3 find_apy(IntSupplier uid) {
    if( _uids==null ) return null;
    int idx = idx(uid);
    return idx== -1 ? null : first(idx);
  }

  // Find a DynField reference at the top level
  public String find_label(IntSupplier uid) {
    if( _uids==null ) return null;
    int idx = idx(uid);
    return idx== -1 ? null : _labels[idx];
  }

  @Override int eidx() { return TVErr.XDYN; }

  // All resolved field labels for a particular DynLoad/DynField
  public  HashSet<String>  fields(HashSet<String> labels, IntSupplier uid, boolean all) {  VBS.clear(); return _fields(labels,uid,all); }
  private HashSet<String> _fields(HashSet<String> labels, IntSupplier uid, boolean all) {
    if( VBS.tset(_uid) ) return labels;
    for( int idx=0; idx<_max; idx++ )
      if( is_dyn(idx) && _uids[idx]==uid ) {
        if( _labels[idx] != null )
          labels.add(_labels[idx]);
        else if( all ) {
          TVStruct ts = (TVStruct)first(idx);
          for( int i=0; i<ts.len(); i++ )
            labels.add(ts._flds[i]);
        }
      } else {
        if( first(idx) instanceof TVDynTable nest )
          nest._fields(labels,uid,all);
      }
    return labels;
  }

  
  // -------------------------------------------------------------

  // Resolve all pairs of inputs as DynTables
  private static final VBitSet VBS = new VBitSet();
  public boolean resolve(boolean test) { VBS.clear(); return _resolve(test); };
  private boolean _resolve( boolean test ) {
    if( VBS.tset(_uid) ) return false;
    boolean progress = false;
    for( int idx=0; idx<_max; idx++ )
      if( is_dyn(idx) ) {
        progress |= _resolve(idx, test);
      } else {
        if( first(idx) instanceof TVDynTable nest )
          progress |= nest._resolve(test);
      }
    return progress;
  }

  // UID must be found
  public boolean resolve(IntSupplier uid, boolean test) {
    return _resolve(idx(uid),test);
  };

  
  // Try to resolve the label; return true if progress
  private boolean _resolve(int idx, boolean test) {
    TV3 matches = first(idx);
    TV3 pattern = secnd(idx);
    if( !(matches instanceof TVStruct str) ) return false; // No progress until a TVStruct
    if( str.is_open() )  return false; // More matches are possible
    // Resolve field by field, removing resolved fields.  Should be 1 YES resolve in the end.
    int yess=0, maybes=0;
    int maybex = -1;
    boolean progress = false;
    for( int i=0; i<str.len(); i++ ) {
      // Trial unify
      TV3 match = str.arg(i);   // An individual match
      int rez = match.trial_unify_ok(pattern);
      int cmp = get_cmp(idx,i);
      if( !test ) set_cmp(idx,i,rez);

      switch( rez ) {
      case 3:
        assert cmp==0 || cmp==3;
        maybes++;
        maybex = i;
        break;
      case 7:
        assert cmp != 1;
        break;
        
      case 1:
        assert cmp != 7;
        yess++;
        if( match==pattern ) continue; // Already matched, no progress
        if( test ) return ptrue(); // Always progress from here
        progress = handle_match(idx,i,str,pattern);
        pattern = pattern.find();
        break;
        
      default: throw TODO();
      }
    }
    // Resolving with a single Maybe.
    // If, later this maybe turns into a Yes, we're just making a Yes sooner.
    // If, later this maybe turns into a No, then we're in an error situation already.
    // To get consistent errors, we need to always have the sane field be the Last Maybe
    if( yess==0 && maybes==1 ) {
      if( test ) return ptrue(); // Gonna match the Last Maybe
      set_cmp(idx,maybex,1);    // Treat as a YES
      progress = handle_match(idx,maybex,str,pattern);
    }

    return progress;
  }

  private boolean handle_match( int idx, int i, TVStruct matches, TV3 pattern ) {
    // Chosen field label
    String choice = matches.fld(i);
    // Grab chosen label before deleting entry from struct
    String label = _labels[idx];
    if( label != null && !label.equals(choice) ) throw TODO("Two valid choices: "+label+" and "+choice);
    _labels[idx] = choice;
    // We got the One True Match, unify
    return matches.arg(i).unify(pattern,false);
  }

  // cmps, 2 bits indexed by 'idx'.
  // goes from 0 -> maybe -> (yes,no)
  private static final int[] CMAP = new int[]{0,1,3,7};
  int get_cmp(int idx, int i) {
    long cmp = _cmps[idx];
    int bits = (int)((cmp>>(i*2))&3);
    return CMAP[bits];
  }

  private static final int[] MAPC = new int[]{0,1,-1,2,-1,-1,-1,3};
  void set_cmp(int idx, int i, int cmp) {
    long lcmp = _cmps[idx];
    long mask = 3L <<(i*2);
    long shf = (long) MAPC[cmp] <<(i*2);
    _cmps[idx] = (lcmp & ~mask) | shf;
    assert get_cmp(idx,i)==cmp;
  }

  
  // True if ALL resolved
  public boolean all_resolved() { VBS.clear(); return _all_resolved(); };
  private boolean _all_resolved() {
    if( VBS.tset(_uid) ) return true;
    boolean resolved = true;
    for( int i=0; i<_max; i++ )
      if( is_dyn(i) )
        resolved &= _labels[i]!=null;
      else {
        if( first(i) instanceof TVDynTable nest )
          resolved &= nest._all_resolved();
      }
    return resolved;
  }
  
  // -------------------------------------------------------------
  @Override public void _union_impl( TV3 tv3 ) {
  }
  
  // -------------------------------------------------------------
  @Override boolean _unify_impl( TV3 tv3 ) {
    TVDynTable that = (TVDynTable)tv3;

    // Unify this into that.  uids in this are either new or old in that.
    for( int i=0; i<_max; i++ ) {
      int idx = that.idx(_uids[i]); // Get match in RHS
      String slhs = _labels[i];
      if( idx == -1 ) {
        that.add_dyn(_uids[i], first(i),secnd(i));
        that._labels[that._max-1] = slhs;
      } else {
        // Merge labels
        String srhs = that._labels[idx];
        if( srhs==null )
          that._labels[idx] = slhs;
        else if( slhs!=null || !slhs.equals(srhs) )
          throw TODO();

        // Merge other args
        that._unify_half(idx*2  ,first(i));
        that._unify_half(idx*2+1,secnd(i));
      }
    }
    // uids in that not this, no need to check
    return ptrue();
  }
  
  private void _unify_half( int idx, TV3 lhs ) {
    if( lhs==null ) return;
    if( _args[idx]==null ) _args[idx] = lhs;
    else lhs._unify(arg(idx),false);
  }

  
  // -------------------------------------------------------------
  @Override boolean _fresh_unify_impl(TV3 tv3, boolean test) {
    TVDynTable that = (TVDynTable)tv3; // Invariant when called
    boolean progress = false;
    for( int i=0; i<_max; i++ ) {
      IntSupplier node = _uids[i];
      int idx = that.idx(node);
      if( idx == -1 ) throw TODO();
      else {
        assert is_dyn(i) == that.is_dyn(idx);
        if( is_dyn(i) ) {
          // Unify match on match
          progress |= first(i)._fresh_unify(that.first(idx),test);
          // Unify pattern on pattern; resolved patterns still should unify
          progress |= secnd(i)._fresh_unify(that.secnd(idx),test);
          if( test && progress ) return progress;

          // cmps have to align; a Y or N in "this" maps to a Y or N in "that",
          // and can force a MAYBE to a Y/N.  A MAYBE in "this" does not force.
          if( first(i) instanceof TVStruct str ) {
            for( int j=0; j<str.len(); j++ ) {
              int cmp = get_cmp(i,j);
              if( cmp==1 || cmp==7 ) { // Force
                TVStruct thatstr = (TVStruct)that.first(idx);
                int thatj = thatstr.idx(str.fld(j));
                int thatcmp = that.get_cmp(idx,thatj);
                if( cmp != thatcmp )
                  throw TODO(); 
              }
              else ;   // MAYBE does not force.
            }
          }
          if( _labels[i]!=null && _labels[i] != that._labels[idx] ) {
            progress = true;
            if( test ) return true;
            assert that._labels[idx]==null;
            that._labels[idx] = _labels[i];
          }
        
        } else {
          // Should be 2 Call/Apply table entries, recursively fresh first(i)/that.first(idx)
          progress |= first(i)._fresh_unify(that.first(idx),test);
        }
      }
    }
    return progress;
  }
  
  
  // -------------------------------------------------------------
  @Override int _trial_unify_ok_impl( TV3 pat ) {
    TVDynTable that = (TVDynTable) pat; // Invariant when called
    // Check all other arguments
    int cmp = 1;
    for( int i=0; i<_max; i++ ) {
      int idx = that.idx(_uids[i]);
      if( idx== -1 ) { cmp |= 3; continue; } // Missing is assumed maybe
      cmp |= _trial_unify_half(first(i),that.first(idx));
      cmp |= _trial_unify_half(secnd(i),that.secnd(idx));
      if( _labels[i]!=null && that._labels[i]!=null )
        throw TODO();           // just fail if both non-null and not-equal
      if( cmp == 7 ) return 7;    // Arg failed so trial fails
    }
    return cmp;                   // Trial result
  }

  private static int _trial_unify_half( TV3 lhs, TV3 rhs ) {
    if( lhs==null ) return 3;
    if( rhs==null ) return 3;
    return lhs._trial_unify_ok(rhs);
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
    tab._max    = _max;
    tab._uids   = _uids.clone();
    tab._cmps   = _cmps.clone();
    tab._labels = _labels.clone();
    return tab;
  }

  private static final VBitSet HDVBS = new VBitSet();
  boolean hasDyn() { HDVBS.clear(); return _hasDyn(); };
  private boolean _hasDyn() {
    if( HDVBS.tset(_uid) ) return false;
    for( int i=0; i<_max; i++ )
      if( is_dyn(i) ||
          ((first(i) instanceof TVDynTable tdyn) && tdyn._hasDyn() ) )
        return true;
    return false;
  }
  
  @Override public VBitSet _get_dups_impl(VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    if( !hasDyn() ) return dups;
    for( int i=0; i<len(); i++ )
      if( _args[i] != null )
        _args[i]._get_dups(visit,dups,debug,prims);
    return dups;
  }
  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    if( !debug && !hasDyn() ) return sb.p("-");
    sb.p("[[  ");
    for( int i=0; i<_max; i++ ) {
      sb.p(is_dyn(i) ? 'D' : 'A').p(_uids[i].getAsInt()).p(": ");
      if( is_dyn(i) ) {
        if( _labels[i]==null ) {
          _args[i*2  ]._str(sb,visit,dups,debug,prims);
          sb.p(" in ");
          _args[i*2+1]._str(sb,visit,dups,debug,prims);
        } else {
          // Fully resolved
          sb.p(_labels[i]).p('=');
          _args[i*2+1]._str(sb,visit,dups,debug,prims);
        }
      } else {
        _args[i*2]._str(sb,visit,dups,debug,prims);
      }
      sb.p(", ");
    }
    return sb.unchar(2).p("]]");
  }
}
