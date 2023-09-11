package com.cliffc.aa.tvar;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;

import java.util.Arrays;

import static com.cliffc.aa.AA.unimpl;

/** A type struct.  
 *
 * Has (recursive) fields with labels.  A struct can be open or closed; open
 * structs allow more fields to appear.  Open structs come from FieldNodes
 * which know that a particular field must be present, and also maybe more.
 * Closed structs come from StructNodes which list all the present fields.
 * If field #0 is present, it is named "." and holds the Clazz for this struct.
 * 
 * Fields may be pinned or not.  Pinned fields cannot lift to a superclazz, and
 * come from StructNodes.  Unpinned fields are not necessarily in the correct
 * struct, and may migrate up the superclazz chain.  
 */
public class TVStruct extends TVExpanding {
  public static final String[] FLDS0 = new String[0];
  public static final TV3   [] TVS0  = new TV3   [0];
  // Empty closed struct.  Used for e.g. no-class Structs.
  //public static final TVStruct EMPTY = new TVStruct(false);
  
  // True if more fields can be added.  Generally false for a known Struct, and
  // true for a Field reference to an unknown struct.
  boolean _open;
  
  // The set of field labels, 1-to-1 with TV3 field contents.  Most field
  // operations are UNORDERED, so we generally need to search the fields by
  // string - except for the clazz field "." always in slot 0.
  private String[] _flds;       // Field labels

  // Pinned fields do not lift to the super-clazz field.  Unpinned fields, if
  // deleted by unification, instead lift to the next open super-clazz or
  // delete if we hit the top of the super-clazz chain.
  private boolean[] _pins;
  
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
    _pins = new boolean[flds.length];
    Arrays.fill(_pins,true);
    _open = open;
    _max = flds.length;
    assert tvs.length==_max;
  }

  public static TVStruct make_clzclz() {
    return new TVStruct(new String[]{TypeFld.CLZ},new TV3[]{ TVBase.make(TypeNil.NIL)});
  }

  // TODO: Unclear if this API makes sense.
  //   ClzClz is closed and has a CLZ field with _tv3[0] being TVBase(nil).
  //   Other structs have a CLZ field, with _tv3[0] being an empty TVStruct (no known class yet)
  //                                                     OR  recursive again
  //
  // Clazz for this struct, or null for ClazzClazz
  public TVPtr pclz() {
    return _flds.length>0 && Util.eq(_flds[0],TypeFld.CLZ) &&
      arg(0) instanceof TVPtr ptr ? ptr : null;
  }
  
  @Override boolean can_progress() { throw unimpl(); }

  // Common accessor not called 'find' which already exists
  public int idx( String fld ) {
    for( int i=0; i<_max; i++ ) if( _flds[i]==fld ) return i;
    return -1;
  }
  
  public boolean add_fld(String fld, TV3 tvf, boolean pin) {
    if( _max == _flds.length ) {
      int len=1;
      while( len<=_max ) len<<=1;
      _flds = Arrays.copyOf(_flds,len);
      _args = Arrays.copyOf(_args,len);
      _pins = Arrays.copyOf(_pins,len);
    }
    _flds[_max] = fld;
    _args[_max] = tvf;
    _pins[_max] = pin;
    _max++;
    // New field is just as wide
    tvf.widen(_widen,false);
    // Changed struct shape, move delayed-fresh updates to now
    move_delay();
    return ptrue();
  }

  // Remove
  boolean del_fld0(int idx) {
    assert !unified();
    assert !Util.eq(_flds[idx],TypeFld.CLZ); // Never remove clazz
    _args[idx] = _args[_max-1];
    _flds[idx] = _flds[_max-1];
    _pins[idx] = _pins[_max-1];
    _max--;
    // Changed struct shape, move delayed-fresh updates to now
    move_delay();
    return ptrue();
  }
  
  boolean del_fld(int idx) {
    boolean pin = _pins[idx];
    String fld = _flds[idx];
    del_fld0(idx);
    // UN-Pinned fields are re-inserted into the next open super-clazz
    if( !pin && !Resolvable.is_resolving( fld ))
      throw unimpl();
    return ptrue();
  }
  // Remove field; true if something got removed
  public boolean del_fld(String fld) {
    int idx = idx(fld);
    return idx != -1 && del_fld(idx);
  }
  
  @Override public int len() { return _max; }  

  public String fld( int i ) { assert !unified();  return _flds[i]; }
  
  // Return the TV3 for field 'fld' or null if missing
  public TV3 arg(String fld) {
    assert !unified();
    int i = idx(fld);
    return i>=0 ? arg(i) : null;
  }
  
  // Return the TV3 for field 'fld' or null if missing, with OUT rollups
  public TV3 debug_arg(String fld) {
    int i = idx(fld);
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
      if( test && progress ) return progress;
      if( Util.eq(skip,_flds[i]) ) continue; // Skip field
      TV3 lhs = arg(i);
      TV3 rhs = that.arg(_flds[i]); // Match by field name, not position
      progress |= rhs==null ? _miss_fld(that,i,lhs,test) : lhs.unify(rhs,test);
    }
    return progress;
  }

  private boolean _miss_fld( TVStruct that, int i, TV3 lhs, boolean test ) {
    if( test ) return ptrue();
    return that.is_open()
      ? that.add_fld(_flds[i],lhs,_pins[i])
      : this.del_fld(i);
  }

  @Override int eidx() { return TVErr.XSTR; }
  @Override public TVStruct as_struct() { return this; }

  // -------------------------------------------------------------
  @Override public void _union_impl( TV3 tv3 ) {
    TVStruct ts = (TVStruct)tv3; // Invariant when called
    ts._open = ts._open & _open;
  }

  // Unify this into that.  Ultimately "this" will be U-F'd into "that" and so
  // all structure changes go into "that".
  @Override boolean _unify_impl( TV3 tv3 ) {
    TVStruct that = (TVStruct)tv3; // Invariant when called
    assert !this.unified() && !that.unified();
    TVStruct thsi = this;
    
    // Unify LHS CLZ into RHS CLZ
    TVPtr pclz0 = this.pclz(), pclz1 = that.pclz();
    TVStruct clz;
    // Basically 3 choices: both have one, only one CLZ but the other is open, no CLZ.
    if( pclz0==null ) {          // No LHS CLZ
      clz = pclz1==null ? null : pclz1.load(); // Shared CLZ is only RHS
    } else {
      if( pclz1==null ) {        // CLZ only on LHS
        clz=pclz0.load();
        that.add_fld( TypeFld.CLZ, pclz0, this._pins[0] ); // Move shared CLZ into RHS
      } else {
        // Both, unify
        clz = pclz1.load();
        pclz0._unify(pclz1,false);
      }
    }
    thsi = (TVStruct)thsi.find();
    that = (TVStruct)that.find();

    // Unify LHS fields into RHS.  None in are the CLZ
    for( int i=0; i<thsi._max; i++ ) {
      assert !thsi.unified();
      String key  = thsi._flds[i];
      TV3 fthis   = thsi.arg(i);
      boolean pin = thsi._pins[i];
      if( Util.eq(key,TypeFld.CLZ) ) continue; // Already unified CLZ
      // Fold into the shared CLZ, if possible
      if( clz!=null && (clz=clz.find().as_struct()).do_into_clz(key,fthis,pin,false,false)!=0 ) {
        thsi = (TVStruct)thsi.find();
        that = (TVStruct)that.find();
        continue;               // Leave field in LHS, its gonna unify anyways
      }

      // Check RHS
      int ti = that.idx(key);
      if( ti == -1 ) {          // Missing field in that
        if( that.is_open() ) {
          that.add_fld(key,fthis,pin); // Add to RHS
        } else if( Resolvable.is_resolving(key) ) {
          add_delay_resolve(that);
          that.add_fld(key,fthis,pin); // Add to RHS
        } else {
          that.del_fld(key);    // Remove from RHS
        }
      } else {
        fthis._unify(that.arg(ti),false); // Unify fields
      }
      thsi = (TVStruct)thsi.find();
      that = (TVStruct)that.find();
    }

    // Fields on the RHS are aligned with the LHS also
    assert !that.unified(); // Missing a find
    for( int i=0; i<that._max; i++ ) {
      assert !that.unified(); // Missing a find
      String key = that._flds[i];
      if( Util.eq(key,TypeFld.CLZ) ) continue; // Already unified CLZ
      if( clz!=null && clz.do_into_clz(key,that.arg(i),that._pins[i], false, false)!=0 ) {
        thsi = (TVStruct)thsi.find();
        that = (TVStruct)that.find();
        that.del_fld0(i--);          // Nuke field from RHS, folded into CLZ
        assert !that.unified(); // Missing a find
        continue;
      }
      int idx = thsi.idx(key);
      if( idx== -1 ) {                               // Missing field in this
        if( Resolvable.is_resolving(key) ) continue; // Do not remove until resolved
        if( !is_open() )
          thsi.del_fld(key); // Drop from RHS to match LHS
        assert !that.unified(); // Missing a find
      }                      // Else, since field already in RHS do nothing
    }
    
    assert !that.unified(); // Missing a find
    return ptrue();
  }

  // If field i exists in clz (recursively) then
  //   if field is not pinned, remove from here and unify there.
  //   else dup-field error
  // Returns 0 if not found, -1 if found & no progress, 1 if found & progress
  // If not-fresh, then only returns 0 or 1
  int do_into_clz( String fld, TV3 tvf, boolean pin, boolean test, boolean fresh ) {
    TV3 arg = arg(fld);         // Find in CLZ
    if( arg != null ) {
      if( pin ) throw unimpl(); // Found in CLZ but pinned here - so dup-field error
      boolean progress = fresh ? tvf._fresh_unify(arg,test) : tvf._unify(arg,test); // Unify (and return true)
      return progress ? 1 : -1;
    }
    TVPtr pclz = pclz();
    if( pclz==null ) return 0;
    return pclz.load().do_into_clz( fld, tvf, pin, test, fresh );
  }
  
  // -------------------------------------------------------------
  @Override boolean _fresh_unify_impl(TV3 tv3, boolean test) {
    boolean progress = false, missing = false;
    assert !unified() && !tv3.unified();    
    TVStruct that = (TVStruct)tv3.find();
    
    // Unify LHS CLZ into RHS CLZ
    TVPtr pclz0 = this.pclz(), pclz1 = that.pclz();
    TVStruct clz;
    // Basically 3 choices: both have one, only one CLZ but the other is open, no CLZ.
    if( pclz0==null ) {          // No LHS CLZ
      clz = pclz1==null ? null : pclz1.load(); // Shared CLZ is only RHS
    } else {
      if( pclz1==null ) {        // CLZ only on LHS
        that.add_fld( TypeFld.CLZ, pclz1 = (TVPtr)pclz0._fresh(), this._pins[0] ); // Move shared CLZ into RHS
        progress = true;
      } else {
        // Both, unify into RHS clz
        progress |= pclz0._fresh_unify(pclz1,false);
        that = (TVStruct)that.find(); // Might have to update
      }
      // RHS CLZ changed; check to see if any local fields move into CLZ
      clz = pclz1.find().as_ptr().load();
      if( progress ) {
        for( int i=0; i<that._max; i++ ) {
          String key = that._flds[i];
          if( !Util.eq(key,TypeFld.CLZ) && // Already unified CLZ
              clz.do_into_clz(key,that.arg(i),that._pins[i],test,false) != 0 ) { // Hit in clazz, done with unify
            that.del_fld0( i-- ); // Nuke field from RHS, folded into CLZ
          }
        }
      }
    }

    // Now do non-CLZ fields
    for( int i=0; i<_max; i++ ) {
      String key = _flds[i];

      if( Util.eq(key,TypeFld.CLZ) ) continue; // Already unified CLZ
      // Fold into the shared CLZ, if possible
      TV3 lhs = arg(i);
      if( clz!=null ) {
        clz = clz.find().as_struct();
        int rez = clz.do_into_clz(key,lhs,_pins[i],test,true);
        if( rez!=0 ) { progress |= rez>0; continue; } // Hit in clazz, done with unify
      }
      
      int ti = that.idx(key);
      if( ti == -1 ) {          // Missing in RHS

        if( that.is_open() || Resolvable.is_resolving(key) ) {
          if( test ) {
            if( that.is_open() ) return ptrue(); // Will definitely make progress
            else continue;
          }
          // If that is open and missing, just force a copy in.  If that is
          // closed, but the fresh field is resolving, force it in anyways and
          // demand that RHS resolves.
          if( !that.is_open() && Resolvable.is_resolving( key) )
            that.add_delay_resolve( that );
          progress |= that.add_fld(key,lhs._fresh(),_pins[i]);
        } else if( is_open() ) // RHS not open, put copy of LHS into RHS with miss_fld error
          throw unimpl();       // miss_fld
        else missing = true; // Else neither side is open, field is not needed in RHS
        
      } else {
        TV3 rhs = that.arg(ti); // Lookup via field name
        progress |= lhs._fresh_unify(rhs,test);
        that._pins[ti] |= _pins[i];        
      }
      assert !unified();      // If LHS unifies, VARS is missing the unified key
      that = (TVStruct)that.find(); // Might have to update
      if( progress && test ) return progress;
    }

    // Fields in RHS and not the LHS are also merged; if the LHS is open we'd
    // just copy the missing fields into it, then unify the structs (shortcut:
    // just skip the copy).  If the LHS is closed, then the extra RHS fields
    // are removed.
    if( !is_open() && (_max != that._max || missing) )
      for( int i=0; i<that._max; i++ ) {
        String key = that._flds[i];
        if( Util.eq(key,TypeFld.CLZ) ) continue; // Already unified CLZ
        if( Resolvable.is_resolving(key) )
          throw unimpl();
          //continue;
        
        TV3 lhs = arg(key); // Lookup vis field name
        if( lhs==null ) {
          if( test ) return ptrue();
          progress |= that.del_fld(i--);
        }
      }

    // If LHS is closed, force RHS closed
    if( !_open && that._open ) {
      progress = ptrue();
      if( test ) return progress;
      that._open = false;
    }

    //if( trial_resolve_all(false,that) ) {
    //  progress = ptrue();
    //  trial_resolve_all(false,this);
    //}
    
    if( _open ) add_delay_fresh(); // If this Struct can add fields, must fresh-unify that Struct
    
    return progress;
  }
  
  
  // -------------------------------------------------------------
  // TODO  move to Resolvable?
  // Attempt to resolve any unresolved fields.
  // Remove any pre-resolved fields.
  public static boolean trial_resolve_all( boolean outie, TVStruct t ) {
    boolean progress = false;
    for( int i=0; i<t._max; i++ ) {
      t = ((TVStruct)t.find());
      String key = t._flds[i];
      if( !Resolvable.is_resolving(key) ) continue; // Resolving key?
      Resolvable res = TVField.FIELDS.get(key);
      if( res==null ) continue;  // Field is already resolved, or not a resolvable field
      // Field is still resolving?
      if( res.is_resolving() ) {
        if( !t.is_open() && // More fields possible, so trial_resolve cannot be tried
            res.trial_resolve(outie,t.arg(i),t, false) ) { // Attempt resolve
          progress = true;
          t = t.find().as_struct();
          i--;                  // Rerun after removing resolved field
        }
      } else {
        progress = true;
        // key is resolving, but Field is already resolved
        TV3 old = t.arg(i);        // Old unresolved value
        t.del_fld(i);              // Remove resolving key
        TV3 t3 = t.arg(res.fld()); // Get resolved label, if any
        if( t3==null ) t.add_fld(res.fld(),old,true); // Insert resolved-label, even if this is open, since operation is a label replacement
        else if( outie ) old.unify(t3, false); // Unify into existing (fold labels together)
        else old._unify(t3, false); // Unify into existing (fold labels together)
      }
    }
    return progress;
  }

  @Override int _trial_unify_ok_impl( TV3 tv3 ) {
    TVStruct that = tv3.as_struct(); // Invariant when called
    int cmp = 1;                     // Assume trial is a YES
    for( int i=0; i<_max; i++ ) {
      TV3 lhs = arg(i);
      TV3 rhs = that.arg(_flds[i]); // RHS lookup by field name
      if( lhs!=rhs && rhs!=null ) {
        int acmp = lhs._trial_unify_ok(rhs);
        if( acmp == -1 ) return -1; // Arg failed so trial fails
        cmp &= acmp;                // Maybe arg makes trial a maybe
      }
    }

    // Allow unification with extra fields.  The normal unification path
    // will not declare an error, it will just remove the extra fields.
    return cmp & this.mismatched_child(that) & that.mismatched_child(this);
  }

  private int mismatched_child(TVStruct that ) {
    if( that.is_open() ) return 0; // Missing fields maybe add later
    for( int i=0; i<_max; i++ )
      if( that.arg(_flds[i])==null ) // Missing key in RHS
        return -1;                   // Trial unification failed
    return 1;
  }

  @Override boolean _exact_unify_impl( TV3 tv3 ) {
    TVStruct ts = (TVStruct)tv3;
    return (!_open && !ts._open ) &&   // Both are closed (no adding unmatching fields)
      Arrays.equals(_flds,ts._flds) && // And all fields match
      Arrays.equals(_pins,ts._pins);   // And all fields match
  }

  // -------------------------------------------------------------
  @Override Type _as_flow( Node dep ) {
    Type t = ADUPS.get(_uid);
    if( t!=null )
      return t;     // Been there, done that
    TypeFld[] flds = TypeFlds.get(_max);
    for( int i=0; i<_max; i++ )
      flds[i] = TypeFld.malloc(_flds[i],null,TypeFld.Access.Final);
    TypeStruct ts = TypeStruct.malloc(false,false,false,Type.ALL.oob(is_open()),flds);
    ADUPS.put(_uid,ts);         // Stop cycles

    // Recursively type fields
    for( int i=0; i<_max; i++ )
      flds[i]._t = arg(i)._as_flow(dep);

    return ts;
  }
  @Override void _widen( byte widen ) {
    for( int i=0; i<len(); i++ )
      if( !Resolvable.is_resolving(_flds[i]) )
        arg(i).widen(widen,false);
  }

  @Override public TVStruct copy() {
    TVStruct st = (TVStruct)super.copy();
    st._flds = _flds.clone();
    st._pins = _pins.clone();
    return st;
  }

  boolean is_int_clz() { return idx("!_"  ) >= 0; }
  boolean is_flt_clz() { return idx("sin" ) >= 0; }
  boolean is_str_clz() { return idx("#_"  ) >= 0; }
  boolean is_math_clz(){ return idx("pi"  ) >= 0; }
  boolean is_top_clz() { return idx("math") >= 0; }

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
    for( int i=0; i<len(); i++ ) {
      if( !debug && Resolvable.is_resolving(_flds[i]) ) continue;
      _args[i]._get_dups(visit,dups,debug,prims);
    }
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
    if(clz instanceof TVPtr zptr && _flds.length==2 && Util.eq(_flds[1],TypeFld.PRIM) ) {
      TVStruct zts = zptr.load();
      if( zts.is_int_clz() || zts.is_flt_clz() || zts.is_str_clz() ) {
        zts._str(sb,visit,dups,debug,prims);
        return _args[1]._str(sb.p(":"),visit,dups,debug,prims);
      }
    }
    // Print clazz field up front.
    boolean is_tup = is_tup(debug), once=_open;
    sb.p(is_tup ? "(" : "@{");
    for( int idx : sorted_flds() ) {
      if( !debug && Resolvable.is_resolving(_flds[idx]) ) continue;
      if( !is_tup ) {                         // Skip tuple field names
        sb.p(_flds[idx]);
        sb.p("= ");
      }
      if( _args[idx] == null ) sb.p("___");
      else _args[idx]._str(sb,visit,dups,debug,prims);
      sb.p(is_tup ? ", " : "; ");
      once=true;
    }
    if( _open ) sb.p(" ..., ");
    if( once ) sb.unchar(2);
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
