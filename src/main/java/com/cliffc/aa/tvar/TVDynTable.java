package com.cliffc.aa.tvar;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import static com.cliffc.aa.AA.TODO;

/** A type for offsets to a DynLoad.
 */
public class TVDynTable extends TV3 {
  public static class DYN {
    // Instead of the Node here - trying to keep a nice split between TV3 and
    // Node - I'm recording the Node unique id, and a flag for DynLoad vs Ident
    boolean _dyn;              // True for DynLoad, False for Ident
    int _uid;                  // Unique node id for the DynLoad
    // If this table entry is for a Ident node, the label is null and
    // the TVar will turn into a nested DynTable.
    // Else this entry is for a DynLoad and this is the TVStruct to match.
    TV3 _tvar;                 // Type to match against; usually a TVStruct
    // 
    TV3 _pat;                  // Pattern type
    // Resolved to this label
    public String _label;
    
    DYN( boolean dyn, int uid, TV3 tvar, TV3 pat ) {
      _dyn = dyn;
      _uid = uid;
      _tvar = tvar;
      _pat = pat;
    }

    // Try to resolve the label; return true if progress
    boolean resolve() {
      assert _dyn;
      if( !(tvar() instanceof TVStruct str) ) return false; // No progress until a TVStruct
      // Resolve field by field, removing resolved fields.  Should be 1 YES resolve in the end.
      boolean progress = false;
      for( int i=0; i<str.len(); i++ ) {
        // Trial unify
        int rez = str.arg(i).trial_unify_ok(pat());
        // 7=NO, 3=MAYBE, 1=YES
        if( rez!=3 ) {          // Either a YES or a NO
          progress = true;      // Progress
          if( rez==1 ) {        // YES: record the resolved field label
            if( _label != null ) throw TODO("Two valid choices: "+_label+" and "+str.fld(i));
            _label = str.fld(i);
          }
          // Fields that resolve as either YES or NO are removed from the list,
          // since they can never change their answer.  Make a fresh copy, and
          // remove the field.
          _tvar = str = (TVStruct)str.fresh();
          str.del_fld0(i--);
        }
        // Pending MAYBEs remain, and need progress elsewhere
      }
      return progress;
    }

    TV3 tvar() { return _tvar.unified() ? (_tvar = _tvar.find()) : _tvar; }
    TV3 pat () { return _pat .unified() ? (_pat  = _pat .find()) : _pat ; }

    // Report errors
    public void errors() {
      if( !_dyn )
        throw TODO();           // Recurse
      if( !(tvar() instanceof TVStruct str) )
        throw TODO("Trying to load from "+tvar()+", which is not a struct");
      if( _label==null )
        throw TODO("No choice resolved");
      if( str.len()>0 )
        throw TODO("Have ambiguous choices");
      
    }

    @Override public String toString() { return str(new SB(),null,null,true,false).toString(); }
    SB str(SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
      if( visit==null ) {
        assert dups==null;
        _tvar._get_dups(visit=new VBitSet(),dups=new VBitSet(),debug,prims);
        _pat ._get_dups(visit              ,dups              ,debug,prims);
        visit.clear();
      }
      sb.p(_dyn?'D':'F').p(_uid);
      if( _label!=null ) sb.p(".").p(_label);
      if( visit.tset(_uid) ) return sb;
      sb.p("=");
      _pat.str(sb,visit,dups,debug,prims);
      TV3 tvar = _tvar.debug_find();
      return tvar instanceof TVStruct str && str.len()==0 ? sb
        : tvar.str(sb.p(" in "),visit,dups,debug,prims);
    }
  }

  // DynLoad table.  Entries are either for a DynLoad/TVStruct/label or a
  // Ident/nested-TVDynTable
  final Ary<DYN> _tab;

  public TVDynTable() {
    _tab = new Ary<>(DYN.class);
  }

  // Add a DynField reference to this table
  public void add( boolean dyn, int uid, TV3 tvar, TV3 pat ) {
    _tab.add(new DYN(dyn,uid,tvar,pat));
  }

  // Find a DynField reference at the top level
  public DYN find(int uid) {
    for( DYN dyn : _tab )
      if( dyn._uid==uid ) {
        assert dyn._dyn;
        return dyn;  
      }
    return null;
  }
  DYN find0(int uid) {
    for( DYN dyn : _tab )
      if( dyn._uid==uid )
        return dyn;  
    return null;
  }
  
  @Override int eidx() { return TVErr.XDYN; }

  // Report errors
  public void errors() {
    for( DYN dyn : _tab )
      dyn.errors();
  }
  
  // -------------------------------------------------------------
  //public static TVDynTable merge( TVDynTable tab0, TVDynTable tab1 ) {
  //  if( tab0==null ) return tab1;
  //  if( tab1==null ) return tab0;
  //  // Union tab0 into tab1 and return it
  //  for( DYN dyn : tab0._tab ) {
  //    assert tab1.find0(dyn._uid)==null;
  //    tab1._tab.push(dyn);
  //  }
  //  tab0.union(tab1);
  //  return tab1;
  //}
  
  // -------------------------------------------------------------
  // Resolve all embedded 
  public boolean resolve( ) {
    boolean progress = false;
    for( DYN dyn : _tab )
      progress |= dyn.resolve();
    return progress;
  }
  
  // -------------------------------------------------------------
  @Override public void _union_impl( TV3 tv3 ) { }

  // Unify this into that.  Ultimately "this" will be U-F'd into "that" and so
  // all structure changes go into "that".
  @Override boolean _unify_impl( TV3 tv3 ) {
    TVDynTable that = (TVDynTable)tv3;
    boolean progress = false;
    for( DYN dyn : _tab ) {
      DYN dyn2 = that.find0(dyn._uid);
      if( dyn2 != null ) throw TODO();
      that._tab.push(dyn);
      progress = true;
    }
    return progress;
  }
  
  // -------------------------------------------------------------
  @Override boolean _fresh_unify_impl(TV3 tv3, boolean test) {
    throw TODO();
  }
  
  
  // -------------------------------------------------------------
  @Override int _trial_unify_ok_impl( TV3 tv3 ) {
    for( DYN dyn : _tab )
      throw TODO();
    return 1;                   // No conflicts, hard-yes
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

  @Override public VBitSet _get_dups_impl(VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    for( DYN dyn : _tab )
      dyn._tvar._get_dups(visit,dups,debug,prims);
    return dups;
  }

  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    sb.p("[[  ");
    for( DYN dyn : _tab )
      dyn.str(sb,visit,dups,debug,prims).p(", ");
    return sb.unchar(2).p("]]");
  }
  
  public static void reset_to_init0() {
    //EMPTY._deps = null;
  }
}
