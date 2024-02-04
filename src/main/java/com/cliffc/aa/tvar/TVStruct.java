package com.cliffc.aa.tvar;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;

import java.util.Arrays;

import static com.cliffc.aa.AA.TODO;

/** A type struct.  
 *
 * Has (recursive) fields with labels.  A struct can be open or closed; open
 * structs allow more fields to appear.  Open structs come from FieldNodes
 * which know that a particular field must be present, and also maybe more.
 * Closed structs come from StructNodes which list all the present fields.  If
 * a field '^' is present it holds the super-Clazz for this struct, which may
 * in turn have another super-Clazz field.
 *
 * Fields may not shadow; caller (e.g. the Parser) must deBruijn rename as
 * needed to avoid collisions.
 *
 * if a struct is closed, all his supers are closed also.
 * if a struct is open, his super may be open or closed.
 *
 * When unifying:
 * - Recursively unify CLZ first; then there exists a common shared CLZ
 * - If a field on one side is found in the other, unify fields.
 * - If a field on one side is missing in a closed other, field is dropped.
 * - If a field on one side is missing in a open other, repeat lookup on common CLZ
 *
 * Fields in open structs may unify with a super-clazz field, open or closed.
 * Fields in closed structs may only unify with local fields
 *
 */
public class TVStruct extends TVExpanding {
  public static final String[] FLDS0 = new String[0];
  public static final TV3   [] TVS0  = new TV3   [0];
  public static final TVStruct STRCLZ = new TVStruct(false);
  
  // True if more fields can be added.  Generally false for a known Struct, and
  // true for a Field reference to an unknown struct.
  boolean _open;
  
  // The set of field labels, 1-to-1 with TV3 field contents.  Most field
  // operations are UNORDERED, so we generally need to search the fields by
  // string
  protected String[] _flds;       // Field labels
  
  private int _max;             // Max set of in-use flds/args

  // No fields
  public TVStruct(boolean open) { this(FLDS0,TVS0,open); }
  // Normal StructNode constructor, all pinned Leaf fields
  public TVStruct( Ary<String> flds ) {  this(flds.asAry(),leafs(flds.len()));  }
  public static TV3[] leafs(int len) {
    TV3[] ls = new TV3[len];
    for( int i=0; i<len; i++ ) ls[i] = new TVLeaf();
    return ls;
  }
  // Made from a StructNode; fields are known, so this is pinned closed
  public TVStruct( String[] flds, TV3[] tvs ) { this(flds,tvs,false); }
  // Made from a Field or SetField; fields are pinned known but might be open
  public TVStruct( String[] flds, TV3[] tvs, boolean open ) {
    super(tvs);
    _flds = flds;
    _open = open;
    _max = flds.length;
    assert tvs.length==_max;
  }

  public static TVStruct make_clzclz() {
    return new TVStruct(new String[]{TypeFld.CLZ},new TV3[]{ new TVBase(TypeNil.NIL)});
  }

  public boolean is_open() { return _open; }
  // Close if open
  public void close() {
    if( !_open ) return;
    _open=false;
    _deps_work_clear();
  }

  @Override public int len() { return _max; }  

  // Common accessor not called 'find' which already exists
  public int idx( String fld ) {
    for( int i=0; i<_max; i++ ) if( Util.eq(_flds[i],fld) ) return i;
    return -1;
  }

  public String fld( int i ) { assert !unified();  return _flds[i]; }
  
  // Return the TV3 for field 'fld' or null if missing
  public TV3 arg(String fld) {
    assert !unified();
    int i = idx(fld);
    return i>=0 ? arg(i) : null;
  }

  // Return the TV3 for field 'fld' or null if missing.
  // Searches the super class chain
  public TV3 arg_clz(String fld) {
    TV3 tv3 = arg(fld);         // Local search
    if( tv3 != null ) return tv3;
    TVPtr clz = pclz();
    return clz==null ? null : clz.load().arg_clz(fld);
  }

  
  // Return the TV3 for field 'fld' or null if missing, with OUT rollups
  public TV3 debug_arg(String fld) {
    int i = idx(fld);
    return i>=0 ? debug_arg(i) : null;
  }
  
  // Clazz for this struct, or null if none
  public TVPtr pclz() {
    return _max>0 && Util.eq(_flds[0],TypeFld.CLZ) ? (TVPtr)arg(0) : null;
  }

  @Override boolean can_progress() { throw TODO(); }
  
  public boolean add_fld(String fld, TV3 tvf ) {
    boolean is_clz = Util.eq(fld,TypeFld.CLZ);
    if( _open ) assert !is_clz;        // Never a clazz in open
    else assert (_max==0)==is_clz && arg_clz(fld)==null; // Clazz only in slow 0
    ptrue();
    if( _max == _flds.length ) {
      int len=1;
      while( len<=_max ) len<<=1;
      _flds = Arrays.copyOf(_flds,len);
      _args = Arrays.copyOf(_args,len);
    }
    _flds[_max] = fld;
    _args[_max] = tvf;
    _max++;
    // New field is just as wide
    tvf.widen(_widen,false);
    // Changed struct shape, move delayed-fresh updates to now
    move_delay();
    return true;
  }
  
  boolean del_fld(int idx) {
    assert !unified();
    assert !Util.eq(_flds[idx],TypeFld.CLZ); // Never remove clazz
    _args[idx] = _args[_max-1];
    _flds[idx] = _flds[_max-1];
    _max--;
    return ptrue();
  }


  @Override int eidx() { return TVErr.XSTR; }
  @Override public TVStruct as_struct() { return this; }

  // -------------------------------------------------------------
  @Override public void _union_impl( TV3 tv3 ) {
    TVStruct ts = tv3.as_struct(); // Invariant when called
    ts._open = ts._open & _open;
  }

  // Unify this into that.  Ultimately "this" will be U-F'd into "that" and so
  // all structure changes go into "that".
  @Override boolean _unify_impl( TV3 tv3 ) {
    assert !unified() && !tv3.unified();
    TVStruct that = (TVStruct)tv3; // Invariant when called
    // Open /open  unify
    if(  _open &&  that._open ) return _unify_impl_open (that);
    // close/close unify
    if( !_open && !that._open ) return _unify_impl_close(that);
    // open /close unify
    return _open ? _unify_impl_mix(that,false) : that._unify_impl_mix(this,true);
  }

  private boolean _unify_impl_open( TVStruct that ) {
    assert pclz()==null && that.pclz()==null; // No CLZ on open
    // Walk left, search right
    // If found, unify
    // else add right
    for( int i=0; i<_max; i++ ) { // Walk left
      TV3 fthat = that.arg(_flds[i]); // Search right 
      if( fthat != null )             // If found
        arg(i)._unify(fthat,false);   // Unify
      else
        that.add_fld(_flds[i],arg(i)); // Not found so add
    }
    return ptrue();
  }

  private boolean _unify_impl_close( TVStruct that ) {
    // Both have CLZ (or both are STRCLZ analogs)
    assert (_max==0 && that._max==0) || (pclz()!=null && that.pclz()!=null); 
    // Walk left, search right (local no CLZ)
    // If found, unify
    // else ignore (del right) & assert not in CLZ
    for( int i=0; i<_max; i++ ) {     // Walk left
      TV3 fthat = that.arg(_flds[i]); // Search right no CLZ
      if( fthat != null )             // If found
        arg(i)._unify(fthat,false);   // Unify
      // Else ignore (del right)
    }
    // Walk right, search left (local no CLZ)
    // if not found, del right
    for( int i=0; i<that._max; i++ ) { // Walk right
      TV3 fthis = arg(that._flds[i]);  // Search left no CLZ
      if( fthis == null )              // If not found
        that.del_fld(i--);             // Remove extras right
    }
    return ptrue();
  }

  private boolean _unify_impl_mix( TVStruct that, boolean flip ) {
    assert _open && pclz()==null;
    assert !that._open && that.pclz()!=null;
    // walk left (open), search right plus CLZ
    //  if found, unify
    //  else ERROR missing field
    for( int i=0; i<_max; i++ ) {         // Walk left
      TV3 fthat = that.arg_clz(_flds[i]); // Search right plus CLZ
      if( fthat != null )                 // If found
        arg(i)._unify(fthat,false);       // Unify
      else
        arg(i)._unify_err("Missing field "+_flds[i],null,null,false);
    }
    // Flip because keeping 'this' and not 'that'
    if( flip ) {
      _uid  = that._uid ;
      _max  = that._max ;
      _args = that._args;
      _flds = that._flds;
      _open = that._open;
      // TODO ALL THE REST OF THE FIELDS
      // OR REWRITE HOW UNION GETS CALLED
    }
    return ptrue();
  }
  
  // -------------------------------------------------------------

  
  // Fresh-Unify this into that.  Ultimately a clone of "this" will be U-F'd
  // into "that" and so all structure changes go into "that".
  @Override boolean _fresh_unify_impl(TV3 tv3, boolean test) {
    assert !unified() && !tv3.unified();
    TVStruct that = (TVStruct)tv3; // Invariant when called
    // Open /open  unify
    if(  _open &&  that._open ) return _fresh_unify_impl_open (that );
    // close/close unify
    if( !_open && !that._open ) return _fresh_unify_impl_close(that,test);
    // open /close unify
    return _open ? _fresh_unify_impl_mix_open(that,test) : _fresh_unify_impl_mix_close(that,test);
  }

  private boolean _fresh_unify_impl_open (TVStruct that ) {
    assert pclz()==null && that.pclz()==null; // No CLZ on open
    // Walk left, search right
    // If found, unify
    // else add right
    boolean progress = false;
    for( int i=0; i<_max; i++ ) {         // Walk left
      TV3 fthat = that.arg(_flds[i]);     // Search right
      progress |= fthat != null           // If found
        ? arg(i)._fresh_unify(fthat,false)// Unify
        : that.add_fld(_flds[i],arg(i)._fresh()); // Not found so add fresh
    }
    return progress;
  }

  private boolean _fresh_unify_impl_close(TVStruct that, boolean test) {
    assert pclz()!=null && that.pclz()!=null; // Both have CLZ (only fails for CLZCLZ which is always EQ so doesn't get here)
    // Walk left, search right (local no CLZ)
    // If found, fresh_unify
    // else ignore (del right) & assert not in CLZ
    boolean progress = false;
    for( int i=0; i<_max; i++ ) {     // Walk left
      TV3 fthat = that.arg(_flds[i]); // Search right
      if( fthat != null )
        progress |= arg(i)._fresh_unify(fthat,test);
    }
    // Walk right, search left (local no CLZ)
    // if not found, del right
    for( int i=0; i<that._max; i++ ) { // Walk right
      TV3 fthis = arg(that._flds[i]);  // Search left no CLZ
      if( fthis == null )              // If not found
        progress |= that.del_fld(i--); // Remove extras right
    }
    return progress;
  }

  private boolean _fresh_unify_impl_mix_open(TVStruct that, boolean test) {
    assert pclz()==null && that.pclz()!=null; // Open on left, closed on right
    // Walk left, search right (with CLZ)
    // If found, unify
    // else ignore (del right)
    boolean progress = false;
    for( int i=0; i<_max; i++ ) {         // Walk left
      TV3 fthat = that.arg_clz(_flds[i]); // Search right (with CLZ)
      if( fthat != null )
        progress |= arg(i)._fresh_unify(fthat,test);
    }
    return progress;
  }

  private boolean _fresh_unify_impl_mix_close(TVStruct that, boolean test) {
    assert pclz()!=null && that.pclz()==null; // Close on left, open on right
    if( test ) return ptrue();
    // Make a brand-new closed RHS as a clone of LHS, then normal _unify_impl_mix
    TVStruct lhs = new TVStruct(_flds.clone(),new TV3[_max],false);
    for( int i=0; i<_max; i++ )
      lhs._args[i] = arg(i)._fresh();
    // Fresh-copy the left, then normal _unify_impl_mix
    that._unify_impl_mix(lhs,false);
    return that.union(lhs);
  }


  // -------------------------------------------------------------

  @Override int _trial_unify_ok_impl( TV3 tv3 ) {
    TVStruct pat = tv3.as_struct(); // Invariant when called
    int cmp = 1;                     // Assume trial is a YES
    for( int i=0; i<pat._max; i++ ) {
      TV3 lhs = arg_clz(pat._flds[i]);// LHS lookup by field name, searching superclass
      TV3 rhs = pat.arg(i);
      if( lhs==rhs ) continue;          // Fast path
      if( lhs==null ) {                 // Missing in match
        cmp |= is_open() ? 3 : 7;       // If match is open, may appear later so maybe, else fail
      } else {
        cmp |= lhs._trial_unify_ok(rhs); // Trial unify recursively
      }
      if( cmp == 7 ) return cmp;  // Arg failed so trial fails
    }

    if( pat.is_open() )   
      return 3;            // If pattern is open, it may yet fail on new fields
    // Since pattern is closed, has to have matched all fields
    for( int i=0; i<_max; i++ )
      if( pat.arg_clz(_flds[i])==null ) // Missing key in RHS
        return 7;                       // Fails, no match for label in pattern
    return 1;                   // Since pattern is closed, all fields matched
  }


  @Override boolean _exact_unify_impl( TV3 tv3 ) {
    TVStruct ts = (TVStruct)tv3;
    return (!_open && !ts._open ) &&   // Both are closed (no adding unmatching fields)
      Arrays.equals(_flds,ts._flds);   // And all fields match
  }

  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) {
    Type t = ADUPS.get(_uid);
    if( t!=null )
      return t;     // Been there, done that
    TypeFld[] flds = TypeFlds.get(_max);
    for( int i=0; i<_max; i++ )
      flds[i] = TypeFld.malloc(_flds[i],null,TypeFld.Access.Final);
    Arrays.sort(flds,( tf0, tf1) -> TypeFld.scmp(tf0._fld,tf1._fld));
    TypeStruct ts = TypeStruct.malloc(false,false,false,Type.ANY.oob(is_open()),flds);
    ADUPS.put(_uid,ts);         // Stop cycles

    // Recursively type fields
    for( int i=0; i<_max; i++ )
      flds[i]._t = arg(i)._as_flow(dep);

    return ts;
  }
  @Override void _widen( byte widen ) {
    for( int i=0; i<len(); i++ )
      arg(i).widen(widen,false);
  }

  @Override public TVStruct copy() {
    TVStruct st = (TVStruct)super.copy();
    st._flds = _flds.clone();
    return st;
  }

  boolean is_int_clz() { return idx("!_"  ) >= 0; }
  boolean is_flt_clz() { return idx("sin" ) >= 0; }
  boolean is_str_clz() { return idx("#_"  ) >= 0; }
  boolean is_math_clz(){ return idx("pi"  ) >= 0; }
  boolean is_top_clz() { return idx("math") >= 0; }
  boolean is_prim() {
    return _max==2 && idx(TypeFld.CLZ)!= -1 && idx(TypeFld.PRIM)!= -1;
  }

  @Override public VBitSet _get_dups_impl(VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    TV3 clz = debug_arg(TypeFld.CLZ);
    if( !prims && is_int_clz() ) return dups;
    if( !prims && is_flt_clz() ) return dups;
    if( !prims && is_str_clz() ) return dups;
    if( !prims && is_math_clz()) return dups;
    if( !prims && is_top_clz() ) return dups;
    
    if( !debug && clz instanceof TVPtr zptr && _flds.length==2 && Util.eq(_flds[1],"0") ) {
      TVStruct zts = zptr.load();
      if( zts.is_int_clz() || zts.is_flt_clz() || zts.is_str_clz() )
        return _args[1]._get_dups(visit,dups,debug,prims);
    }
    for( int i=0; i<len(); i++ )
      _args[i]._get_dups(visit,dups,debug,prims);
    return dups;
  }

  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    if( _args==null  ) return sb.p(_open ? "(...)" : "()");
    if( !prims && is_int_clz() ) return sb.p("int");
    if( !prims && is_flt_clz() ) return sb.p("flt");
    if( !prims && is_str_clz() ) return sb.p("str");
    if( !prims && is_math_clz()) return sb.p("math");
    if( !prims && is_top_clz() ) return sb.p("TOP");

    // Special hack to print "int:(2)" as "2"
    TV3 clz = debug_arg(TypeFld.CLZ);
    if( clz instanceof TVPtr zptr && _max==2 && debug_arg(TypeFld.PRIM)!=null ) {
      TVStruct zts = zptr.load();
      if( zts.is_int_clz() || zts.is_flt_clz() || zts.is_str_clz() ) {
        zts._str(sb,visit,dups,debug,prims);
        return debug_arg(TypeFld.PRIM)._str(sb.p(":"),visit,dups,debug,prims);
      }
    }
    // Print clazz field up front.
    boolean is_tup = is_tup(debug), once=_open;
    sb.p(is_tup ? "( " : "@{ ");
    for( int idx : sorted_flds() ) {
      if( !is_tup && !Util.eq(_flds[idx],TypeFld.CLZ) ) { // Skip tuple field names
        sb.p(_flds[idx]);
        sb.p("=");
      }
      if( _args[idx] == null ) sb.p("___");
      else _args[idx]._str(sb,visit,dups,debug,prims);
      sb.p(is_tup ? ", " : "; ");
      once=true;
    }
    if( _open ) sb.p(" ..., ");
    if( once && is_tup ) sb.unchar(2);
    sb.p(!is_tup ? "}" : ")");
    return sb;
  }

  boolean is_tup(boolean debug) {
    if( _max==0 ) return true;
    boolean label=true;
    for( int i=0; i<len(); i++ ) {
      char c = _flds[i].charAt(0);
      if( debug && c=='&' ) return false;
      else if( Character.isDigit(c) ) label=false;
    }
    return !label;
  }

  // Stoopid hand-rolled bubble sort
  private int[] sorted_flds() {
    int[] is = new int[_max];
    for( int i=0; i<_max; i++ ) is[i] = i;
    for( int i=0; i<_max; i++ )
      for( int j=i+1; j<_max; j++ ) {
        String fi = _flds[is[i]];
        String fj = _flds[is[j]];
        if( fi!=null && !Util.eq(fi,TypeFld.CLZ) && (fj==null || Util.eq(fj,TypeFld.CLZ) || fj.compareTo(fi) < 0) )
          { int tmp = is[i]; is[i] = is[j]; is[j] = tmp; }
      }
    return is;
  }
  
  public static void reset_to_init0() {
    //EMPTY._deps = null;
  }
}
