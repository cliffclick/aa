package com.cliffc.aa.tvar;

import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Oper;
import com.cliffc.aa.Parse;
import com.cliffc.aa.node.FieldNode;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.*;

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
  // Fields are pinned in this TVStruct, or UNPINNED and can unify on the RHS of a TVClz
  private boolean[] _pins;      // 

  private int _max;             // Max set of in-use flds/args
  
  public TVStruct( Ary<String> flds ) { this(true,flds.asAry(),new TV3[flds.len()]);  }
  // Made from a StructNode; fields are known, so this is closed
  public TVStruct( boolean is_copy, String[] flds, TV3[] tvs ) { this(is_copy,flds,tvs,false); }
  // Made from a Field or SetField; fields are unknown so this is open
  public TVStruct( boolean is_copy, String[] flds, TV3[] tvs, boolean open ) { this(is_copy,flds,pins(flds),tvs,open); }
  public TVStruct( boolean is_copy, String[] flds, boolean[] pins, TV3[] tvs, boolean open ) {
    super(is_copy,tvs);
    _flds = flds;
    _pins = pins;
    _open = open;
    _max = flds.length;
    assert tvs.length==_max;
  }

  // Used during cyclic construction
  public void set_pin_fld(int i, TV3 fld) { _args[i] = fld; _pins[i] = true; }
  public boolean is_pinned(String fld) { return _pins[Util.find(_flds,fld)]; }
  private static boolean[] pins( String[] flds ) {
    boolean[] pins = new boolean[flds.length];
    for( int i=0; i<flds.length; i++ )
      pins[i] = Oper.is_oper(flds[i]); // Operators pinned into clazz structs
    return pins;
  }

  public boolean add_fld(String fld, boolean pinned, TV3 tvf) {
    if( _max == _flds.length ) {
      int len=1;
      while( len<=_max ) len<<=1;
      _flds = Arrays.copyOf(_flds,len);
      _pins = Arrays.copyOf(_pins,len);
      _args = Arrays.copyOf(_args,len);
    }
    _flds[_max] = fld;
    _args[_max] = tvf;
    _pins[_max] = pinned;
    _max++;
    // Changed struct shape, move delayed-fresh updates to now
    move_delay_fresh();
    return true;
  }

  // Remove
  boolean del_fld(int idx) {
    _args[idx] = _args[_max-1];
    _pins[idx] = _pins[_max-1];
    _flds[idx] = _flds[_max-1];
    _max--;
    // Changed struct shape, move delayed-fresh updates to now
    move_delay_fresh();
    return true;
  }
  // Remove field; true if something got removed
  boolean del_fld(String fld) {
    int idx = Util.find(_flds,fld);
    return idx != -1 && del_fld(idx);
  }
  
  @Override public int len() { return _max; }  

  public String fld( int i ) { assert !unified();  return _flds[i]; }
  
  // Return the TV3 for field 'fld' or null if missing
  public TV3 arg(String fld) {
    assert !unified();
    int i = Util.find(_flds,fld);
    return i>=0 ? arg(i) : null;
  }
  
  // Return the TV3 for field 'fld' or null if missing, with OUT rollups
  public TV3 debug_arg(String fld) {
    int i = Util.find(_flds,fld);
    return i>=0 ? debug_arg(i) : null;
  }

  public boolean is_open() { return _open; }
  // Close if open
  public void close() {
    if( !_open ) return;
    _open=false;
    _deps_work_clear();
  }
  
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
      ? that.add_fld(_flds[i],_pins[i],lhs)
      : this.del_fld(i);
  }

  @Override int eidx() { return TVErr.XSTR; }
  @Override public TVStruct as_struct() { return this; }

  // -------------------------------------------------------------
  @Override void _union_impl( TV3 tv3 ) {
    //assert _uid > tv3._uid;
    if( tv3 instanceof TVStruct ts ) ts._open &= _open;
  }

  @Override boolean _unify_impl( TV3 tv3 ) {
    TVStruct that = (TVStruct)tv3; // Invariant when called
    this.trial_resolve_all(false);
    that.trial_resolve_all(false);

    // Unify LHS fields into RHS
    boolean open = that.is_open();
    for( int i=0; i<_max; i++ ) {
      TV3 fthis = arg(i);       // Field of this      
      String key = _flds[i];
      boolean pinned = _pins[i];
      int ti = Util.find(that._flds,key);
      if( ti == -1 ) {          // Missing field in that
        //if( Resolvable.is_resolving(key) ) continue; // Do not add or remove until resolved
        if( open || Resolvable.is_resolving(key) )
          that.add_fld(key,pinned,fthis);   // Add to RHS
        else
          that.del_fld(key);                // Remove from RHS
      } else {
        TV3 fthat = that.arg(ti);  // Field of that
        fthis._unify(fthat,false); // Unify both into RHS
        that._pins[ti] |= pinned;  // Unify pinned
        // Progress may require another find()
        that = (TVStruct)that.find();
        assert !unified();      // TODO: weave this thru
      }
    }

    // Fields on the RHS are aligned with the LHS also
    for( int i=0; i<that._max; i++ ) {
      String key = that._flds[i];
      if( arg(key)==null ) {                         // Missing field in this
        if( Resolvable.is_resolving(key) ) continue; // Do not remove until resolved
        if( is_open() ) add_fld(key,that._pins[i],that.arg(i)); // Add to LHS
        else del_fld(key);                                      // Drop from RHS
      }
    }

    assert !that.unified(); // Missing a find
    return true;
  }
  
  // -------------------------------------------------------------
  @Override boolean _fresh_unify_impl(TV3 tv3, boolean test) {
    boolean progress = false, missing = false;
    TVStruct that = (TVStruct)tv3; // Invariant checked before calling
    assert !unified() && !that.unified();
    
    // Any pending field resolutions
    progress |= this.trial_resolve_all(test);
    progress |= that.trial_resolve_all(test);
    that = (TVStruct)that.find(); // Might have to update
    assert !unified();       // TODO: update/find thsi,that

    for( int i=0; i<_max; i++ ) {
      TV3 lhs = arg(i);
      int ti = Util.find(that._flds,_flds[i]);
      if( ti== -1 && Resolvable.is_resolving(_flds[i]) ) {
        // Open RHS allows more fields which might add choices
        if( that._open ) continue;
        Resolvable res = TVField.FIELDS.get(_flds[i]);
        if( !res.trial_resolve(false,lhs,this,that,test) ) continue;
        if( test ) return true;
        progress = true;
        // Updated LHS args and RHS key
        lhs = arg(_flds[i]);
      }

      if( ti == -1 ) {          // Missing in RHS
        if( is_open() || that.is_open() ) {
          if( test ) return true; // Will definitely make progress
          TV3 nrhs = lhs._fresh();
          if( !that.is_open() ) // RHS not open, put copy of LHS into RHS with miss_fld error
            throw unimpl();
          progress |= that.add_fld(_flds[i],_pins[i],nrhs);
        } else missing = true; // Else neither side is open, field is not needed in RHS
      } else {
        TV3 rhs = that.arg(ti); // Lookup via field name
        progress |= lhs._fresh_unify(rhs,test);
        that._pins[ti] |= _pins[i];
      }
      that = (TVStruct)that.find(); // Might have to update
      assert !unified();            // TODO: update/find thsi,that
      if( progress && test ) return true;
    }

    // Fields in RHS and not the LHS are also merged; if the LHS is open we'd
    // just copy the missing fields into it, then unify the structs (shortcut:
    // just skip the copy).  If the LHS is closed, then the extra RHS fields
    // are removed.
    if( _max != that._max || missing )
      for( int i=0; i<that._max; i++ ) {
        if( Resolvable.is_resolving(that._flds[i]) ) continue;
        TV3 lhs = arg(that._flds[i]); // Lookup vis field name
        if( lhs==null ) {
          if( test ) return true;
          progress |= that.del_fld(i--);
        }
      }
    
    // If LHS is closed, force RHS closed
    if( !_open && that._open ) {
      if( test ) return true;
      that._open = false;
      progress = true;
    }
    return progress;
  }
  
  
  // -------------------------------------------------------------
  // TODO  move to Resolvable?
  private boolean trial_resolve_all(boolean test) {
    boolean progress = false;
    for( int i=0; i<_max; i++ ) {
      String key = _flds[i];
      Resolvable res = TVField.FIELDS.get(key);
      if( res==null ) continue;  // Field is already resolved, or not a resolvable field
      // Field is still resolving?
      if( res.is_resolving() ) {
        if( !is_open() ) // More fields possible, so trial_resolve cannot be tried
          progress |= res.trial_resolve(false,arg(i),this,this,test); // Attempt resolve
      } else {
        // key is resolving, but Field is already resolved
        if( test ) continue;
        TV3 old = arg(i);        // Old unresolved value
        del_fld(i);              // Remove resolving key
        TV3 t3 = arg(res.fld()); // Get resolved label, if any
        if( t3==null ) throw unimpl(); //_args.put(res._fld,old); // Insert resolved-label, even if this is open, since operation is a label replacement
        else progress |= old._unify(t3,test); // Unify into existing (fold labels together)
      }
    }
    return progress;
  }

  @Override boolean _trial_unify_ok_impl( TV3 tv3, boolean extras ) {
    if( this==tv3 ) return true;
    TVStruct that = (TVStruct)tv3; // Invariant when called
    for( int i=0; i<_max; i++ ) {
      TV3 lhs = arg(i);
      TV3 rhs = that.arg(_flds[i]); // RHS lookup by field name
      if( lhs!=rhs && rhs!=null && !lhs._trial_unify_ok(rhs,extras) )
        return false;           // Child fails to unify
    }

    // Allow unification with extra fields.  The normal unification path
    // will not declare an error, it will just remove the extra fields.
    return (extras || this.mismatched_child(that)) && (that.mismatched_child(this));
  }

  private boolean mismatched_child(TVStruct that ) {
    for( int i=0; i<_max; i++ )
      if( !Resolvable.is_resolving(_flds[i]) &&
          that.arg(_flds[i])==null ) // And missing key in RHS
        return false;          // Trial unification failed
    return true;
  }
  
  public ErrMsg err_resolve(Node in0, Parse loc, String msg) {
    if( msg.equals("No field resolves") ) {
      if( in0 instanceof FieldNode fld ) {
        if( Oper.is_oper(fld._fld) ) {
          String clz = FieldNode.clz_str(fld.val(0));
          return ErrMsg.unresolved(loc,"No operator "+(clz==null?"":clz)+fld._fld);
        }
        else throw unimpl();
      }
      return ErrMsg.unresolved(loc,msg);
    }
    SB sb = new SB().p(msg).p(", unable to resolve ");
    VBitSet dups = get_dups();
    VBitSet visit = new VBitSet();
    for( int i=0; i<len(); i++ )
      if( !Resolvable.is_resolving(_flds[i]) )
        arg(i)._str(sb,visit,dups,false).p(" and ");
    return ErrMsg.unresolved(loc,sb.unchar(5).toString());
  }

  
  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) { throw unimpl(); }  
  public boolean is_int_clz() { return  Util.find(_flds,"!_" ) >= 0; }
  public boolean is_flt_clz() { return  Util.find(_flds,"sin") >= 0; }
  public boolean is_str_clz() { return  Util.find(_flds,"#_" ) >= 0; }

  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug) {
    boolean is_tup = _max==0 || Character.isDigit(_flds[0].charAt(0));
    sb.p(is_tup ? "(" : "@{");
    if( _args==null ) sb.p(", ");
    else {
      for( int idx : sorted_flds() ) {
        String  fld = _flds[idx];
        boolean pin = _pins[idx];
        // Skip resolved field names in a tuple
        if( !is_tup || Resolvable.is_resolving(fld) || !pin )
          sb.p(fld).p(pin?"#":"").p("= ");
        if( _args[idx] == null ) sb.p("_");
        else _args[idx]._str(sb,visit,dups,debug);
        sb.p(is_tup ? ", " : "; ");
      }
    }
    if( _open ) sb.p(" ..., ");
    if( _args!=null && _args.length>0 ) sb.unchar(2);
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
