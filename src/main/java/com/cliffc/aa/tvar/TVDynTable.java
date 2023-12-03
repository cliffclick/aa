package com.cliffc.aa.tvar;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.NonBlockingHashMapLong;
import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.VBitSet;

import java.util.Arrays;

import static com.cliffc.aa.AA.TODO;

/** A type for offsets to a DynLoad.
 */
public class TVDynTable extends TV3 {

  public static class DYN {
    final int _idx;      // Index into args array for pair of match and pattern
    
    // Instead of the Node here - trying to keep a nice split between TV3 and
    // Node - I'm recording the Node unique id, and a flag for DynLoad vs Ident
    final boolean _dyn;         // True for DynLoad, False for Ident
    final int _uid;             // Unique node id for the DynLoad
    
    // Resolved to this label
    public String _label;
    
    DYN( int idx, boolean dyn, int uid ) {
      _idx = idx;
      _dyn = dyn;
      _uid = uid;
    }

    // Try to resolve the label; return true if progress
    boolean resolve(TVDynTable dyn) {
      assert _dyn;
      if( !(match(dyn) instanceof TVStruct str) ) return false; // No progress until a TVStruct
      // Resolve field by field, removing resolved fields.  Should be 1 YES resolve in the end.
      boolean progress = false;
      for( int i=0; i<str.len(); i++ ) {
        // Trial unify
        int rez = str.arg(i).trial_unify_ok(pattern(dyn));
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
          str = (TVStruct)str.fresh();
          str.del_fld0(i--);
          set_match(dyn,str);
        }
        // Pending MAYBEs remain, and need progress elsewhere
      }
      return progress;
    }

    TV3 match  (TVDynTable tab) { return tab.arg(_idx+0); }
    TV3 pattern(TVDynTable tab) { return tab.arg(_idx+1); }
    void set_match(TVDynTable tab, TVStruct ts) { tab._args[_idx+0]=ts; }

    // Report errors
    public void errors(TVDynTable dyn) {
      if( !_dyn )
        throw TODO();           // Recurse
      if( !(match(dyn) instanceof TVStruct str) )
        throw TODO("Trying to load from "+match(dyn)+", which is not a struct");
      if( _label==null )
        throw TODO("No choice resolved");
      if( str.len()>0 )
        throw TODO("Have ambiguous choices");
    }

    @Override public String toString() { return str(null,new SB(),null,null,true,false).toString(); }
    SB str(TVDynTable tab, SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
      sb.p(_dyn?'D':'F').p(_uid);
      if( _label!=null ) sb.p(".").p(_label);
      if( tab==null ) return sb;
      sb.p("=");
      pattern(tab).str(sb,visit,dups,debug,prims);
      TV3 tvar = match(tab);
      return tvar instanceof TVStruct str && str.len()==0 ? sb
        : tvar.str(sb.p(" in "),visit,dups,debug,prims);
    }
  }

  // DynLoad table.  Entries are either for a DynLoad/TVStruct/label or a
  // Ident/nested-TVDynTable
  private NonBlockingHashMapLong<DYN> _dyns;

  private int _max;
  
  public TVDynTable() { _dyns = new NonBlockingHashMapLong<>(); _max=0; }

  @Override public int len() { return _max; }  

  // Add a DynField reference to this table
  public void add( boolean dyn, int uid, TV3 tvar, TV3 pat ) {
    _dyns.put(uid,new DYN(len(),dyn,uid));

    if( _args==null ) _args = new TV3[2];
    if( _max == _args.length ) {
      int len=1;
      while( len<=_max ) len<<=1;
      _args = Arrays.copyOf(_args,len);
    }
    _args[_max++] = tvar;
    _args[_max++] = pat ;
  }

  // Find a DynField reference at the top level
  public String find_label(int uid) {
    DYN dyn = _dyns.get(uid);
    return dyn==null ? null : dyn._label;
  }
  
  @Override int eidx() { return TVErr.XDYN; }

  // Report errors
  public void errors() {
    for( DYN dyn : _dyns.values() )
      dyn.errors(this);
  }
  
  // -------------------------------------------------------------
  // Resolve all embedded 
  public boolean resolve( ) {
    boolean progress = false;
    for( DYN dyn : _dyns.values() )
      progress |= dyn.resolve(this);
    return progress;
  }
  
  // -------------------------------------------------------------
  @Override public void _union_impl( TV3 tv3 ) { }

  // Unify this into that.  Ultimately "this" will be U-F'd into "that" and so
  // all structure changes go into "that".
  @Override boolean _unify_impl( TV3 tv3 ) {
    TVDynTable that = (TVDynTable)tv3;
    for( DYN dyn : _dyns.values() ) {
      DYN dyn2 = that._dyns.get(dyn._uid);
      if( dyn2 != null ) {
        if( dyn._label!=dyn2._label && !dyn._label.equals(dyn2._label) )  throw TODO(); // Labels agree
        // Unify parts
        dyn.match  (this)._unify(dyn2.match  (that),true);
        dyn.pattern(this)._unify(dyn2.pattern(that),true);
      } else {
        that.add(dyn._dyn,dyn._uid,dyn.match(this),dyn.pattern(this));
      }
    }
    return true;
  }
  
  // -------------------------------------------------------------
  @Override boolean _fresh_unify_impl(TV3 tv3, boolean test) {
    throw TODO();
  }
  
  
  // -------------------------------------------------------------
  @Override int _trial_unify_ok_impl( TV3 tv3 ) {
    for( DYN dyn : _dyns.values() )
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

  @Override public TVDynTable copy() {
    TVDynTable dyn = (TVDynTable)super.copy();
    dyn._dyns = _dyns.clone();
    return dyn;
  }
  
  @Override SB _str_impl(SB sb, VBitSet visit, VBitSet dups, boolean debug, boolean prims) {
    sb.p("[[  ");
    for( DYN dyn : _dyns.values() )
      dyn.str(this,sb,visit,dups,debug,prims).p(", ");
    return sb.unchar(2).p("]]");
  }
  
  public static void reset_to_init0() {
  }
}
