package com.cliffc.aa.tvar;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.Util;
import com.cliffc.aa.util.VBitSet;

import java.util.Arrays;

import static com.cliffc.aa.AA.unimpl;

/** A type struct.
 *
 */
public class TVStruct extends TV3 {

  // True if more fields can be added.  Generally false for a known Struct, and
  // true for a Field reference to an unknown struct.
  boolean _open;
  
  // The set of field labels, 1-to-1 with TV3 field contents.
  // Most field operations are UNORDERED, so we generally need to search the fields by string
  private String[] _flds;       // Field labels

  private int _max;             // Max set of in-use flds/args
  
  public TVStruct( Ary<String> flds ) { this(flds.asAry(),new TV3[flds.len()]);  }
  // Made from a StructNode; fields are known, so this is closed
  public TVStruct( String[] flds, TV3[] tvs ) { this(flds,tvs,false); }
  // Made from a Field or SetField; fields are unknown so this is open
  public TVStruct( String[] flds, TV3[] tvs, boolean open ) {
    super(true,tvs);
    _flds = flds;
    _open = open;
    _max = flds.length;
    assert tvs.length==_max;
  }

  // Used during cyclic construction
  public void set_fld(int i, TV3 fld) { _args[i] = fld; }

  public boolean add_fld(String fld, TV3 tvf) {
    if( _max == _flds.length ) {
      int len=1;
      while( len<=_max ) len<<=1;
      _flds = Arrays.copyOf(_flds,len);
      _args = Arrays.copyOf(_args,len);
    }
    _flds[_max] = fld;
    _args[_max] = tvf;
    _max++;
    return true;
  }
  // Remove
  boolean del_fld(int i) {
    throw unimpl();
  }
  // Remove field; true if something got removed
  boolean del_fld(String fld) {
    int idx = Util.find(_flds,fld);
    if( idx== -1 ) return false;
    _args[idx] = _args[_max-1];
    _flds[idx] = _flds[_max-1];
    _max--;
    return true;
  }
  
  @Override public int len() { return _max; }  

  public String fld( int i ) { return _flds[i]; }
  
  // Return the TV3 for field 'fld' or null if missing
  public TV3 arg(String fld) {
    int i = Util.find(_flds,fld);
    return i>=0 ? arg(i) : null;
  }
  
  // Return the TV3 for field 'fld' or null if missing, with OUT rollups
  public TV3 debug_arg(String fld) {
    int i = Util.find(_flds,fld);
    return i>=0 ? debug_arg(i) : null;
  }

  public boolean is_open() { return _open; }
  
  // Partial unify two structs.  Unify matching fields in this with that.  If
  // field is missing in that and that is closed, remove the field from 'this'.
  // Skip a special field, if null.
  public boolean half_unify( TVStruct that, String skip, boolean test ) {
    boolean progress = false;
    for( int i=0; i<_max; i++ ) {
      if( test && progress ) return true;
      if( Util.eq(skip,_flds[i]) ) continue; // Skip field
      TV3 lhs = arg(i);
      TV3 rhs = that.arg(_flds[i]); // Match by field name, not position
      progress |= rhs==null ? _miss_fld(that,i,lhs,test) : lhs.unify(rhs,test);
    }
    return progress;
  }

  private boolean _miss_fld( TVStruct that, int i, TV3 lhs, boolean test ) {
    if( test ) return true;
    return that.is_open()
      ? that.add_fld(_flds[i],lhs)
      : this.del_fld(i);
  }
  
  // -------------------------------------------------------------
  @Override void _union_impl( TV3 tv3) {
    assert _uid > tv3._uid;
    TVStruct that = (TVStruct)tv3; // Invariant when called
    that._open &= _open;
  }

  @Override boolean _unify_impl( TV3 tv3 ) {
    TVStruct thsi = this;          // So we can update 'this'
    TVStruct that = (TVStruct)tv3; // Invariant when called
    if( trial_resolve_all(false) ) thsi = (TVStruct)thsi.find();
    assert !that.trial_resolve_all(true); // TODO: need a test case

    // Unify LHS fields into RHS
    boolean open = that.is_open();
    for( int i=0; i<thsi._max; i++ ) {
      String key = thsi._flds[i];
      TV3 fthis = thsi.arg(key);         // Field of this
      TV3 fthat = that.arg(key);         // Field of that
      if( fthat==null ) {                // Missing field in that
        if( open &&                      // RHS is open
            !Resolvable.is_resolving(key) ) // Do not add or remove until resolved
          that.add_fld(key,fthis);       // Add to RHS
      } else {
        fthis._unify(fthat,false); // Unify both into RHS
        // Progress may require another find()
        thsi = (TVStruct)thsi.find();
        that = (TVStruct)that.find();
      }
    }

    // Fields on the RHS are aligned with the LHS also
    if( !thsi.is_open() )
      for( int i=0; i<that._max; i++ ) {
        String key = that._flds[i];
        if( !Resolvable.is_resolving(key) && // Do not remove until resolved
            thsi.arg(key)==null )            // Fields in both already done
          that.del_fld(i);                   // Drop from RHS
      }

    assert !that.unified(); // Missing a find
    return true;
  }

  private boolean trial_resolve_all(boolean test) {
    boolean progress = false;
    for( int i=0; i<_max; i++ ) {
      String key = _flds[i];
      Resolvable res = TVField.FIELDS.get(key);
      if( res==null ) continue;  // Field is already resolved, or not a resolvable field
      // Field is still resolving?
      if( res.is_resolving() ) {
        if( !is_open() ) // More fields possible, so trial_resolve cannot be tried
          progress |= res.trial_resolve(arg(i),this,this,test); // Attempt resolve
      } else {
        throw unimpl();
      }
    }
    return progress;
  }

  @Override boolean _trial_unify_ok_impl( TV3 tv3, boolean extras ) {
    TVStruct that = (TVStruct)tv3; // Invariant when called
    for( int i=0; i<_max; i++ ) {
      TV3 lhs = arg(i);
      TV3 rhs = that.arg(_flds[i]); // RHS lookup by field name
      if( rhs==null ) {
        throw unimpl();         // Missing RHS, check for extras
      } else {
        if( !lhs._trial_unify_ok(rhs,extras) )
          return false;         // Child fails to unify
      }      
    }

    // Check for extras
    if( !is_open() ) {
      for( int i=0; i<that._max; i++ ) {
        TV3 lhs = that.arg(i);
        TV3 rhs = arg(that._flds[i]); // LHS lookup by field name
        if( rhs==null ) {
          throw unimpl();       // Extra on LHS
        }
      }
    }
    return true;                // Unifies OK
  }
  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    // Find any special instance tag fields, and print shortcuts.
    TV3 bang = debug_arg("!");
    if( bang instanceof TVPtr ptr ) {
      TVStruct proto = ptr.load();
      String clz=null;
      if( proto.arg("_&&_") != null ) clz = "int:";
      if( proto.arg("sin" ) != null ) clz = "flt:";
      if( clz!=null ) {
        sb.p(clz);
        TV3 prim = debug_arg(".");
        if( prim instanceof TVBase base ) return sb.p(base._t);
      }
    }

    boolean is_tup = _max==0 || Character.isDigit(_flds[0].charAt(0));
    sb.p(is_tup ? "(" : "@{");
    if( _args==null ) sb.p(", ");
    else {
      for( int idx : sorted_flds() ) {
        String fld = _flds[idx];
        // Skip resolved field names in a tuple
        if( !is_tup || Resolvable.is_resolving(fld) )
          sb.p(fld).p("= ");
        if( _args[idx] == null ) sb.p("_");
        else _args[idx]._str(sb,visit,dups,debug);
        sb.p(is_tup ? ", " : "; ");
      }
    }
    if( _open ) sb.p(" ..., ");
    sb.unchar(2);
    sb.p(!is_tup ? "}" : ")");
    return sb;
  }

  // Stoopid hand-rolled bubble sort
  private int[] sorted_flds() {
    int[] is = new int[_max];
    for( int i=0; i<_max; i++ ) is[i] = i;
    for( int i=0; i<_max; i++ )
      for( int j=i+1; j<_max; j++ ) {
        String fi = _flds[is[i]];
        String fj = _flds[is[j]];
        if( fi!=null && (fj==null || fj.compareTo(fi) < 0) )
          { int tmp = is[i]; is[i] = is[j]; is[j] = tmp; }
      }
    return is;
  }

}
