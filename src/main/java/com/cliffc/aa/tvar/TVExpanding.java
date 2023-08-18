package com.cliffc.aa.tvar;

import com.cliffc.aa.node.FreshNode;
import com.cliffc.aa.util.Ary;

import static com.cliffc.aa.AA.unimpl;

abstract public class TVExpanding extends TV3 {

  // This is used Fresh against that.
  // If it ever changes (add_fld to TVStruct, or TVLeaf unify), we need to re-Fresh the deps.
  static Ary<DelayFresh> DELAY_FRESH  = new Ary<>(new DelayFresh[1],0);
  // If this TV expands, we need to re-check resolving fields in these structs
  static Ary<TVStruct> DELAY_RESOLVE  = new Ary<>(new TVStruct[1],0);

  // This TV3 is used Fresh against another TV3.
  // If it ever changes, we need to re-Fresh the dependents.
  // - Leaf expands/unions
  // - Base type drops
  // - Struct adds/dels fields
  // - Ptr becomes may/use-nil
  // - Lambda becomes may/use-nil
  private Ary<DelayFresh> _delay_fresh;

  // This Leaf/Base is used to resolve a field.
  // If it ever changes, we need to re-check the resolves
  private Ary<TVStruct> _delay_resolve;

  TVExpanding() { this(null); }
  TVExpanding( TV3[]tvs ) { super(tvs); }
  
  // -----------------
  // Delayed-Fresh-Unify of LHS vs RHS.  LHS was a leaf and so imparted no
  // structure to RHS.  When LHS changes to a non-leaf, the RHS needs to
  // re-Fresh-Unify.
  static class DelayFresh {
    TV3 _lhs, _rhs;
    TV3[] _nongen;
    DelayFresh _next;
    FreshNode _frsh;
    DelayFresh(TV3 lhs, TV3 rhs, TV3[] nongen, FreshNode frsh) {
      assert !lhs.unified() && !rhs.unified();
      _lhs=lhs;
      _rhs=rhs;
      _nongen=nongen;
      _frsh = frsh;
    }
    boolean update() {
      if( !_lhs.unified() && ! _rhs.unified() ) return false;
      _lhs = _lhs.find();
      _rhs = _rhs.find();
      return true;              // Requires dup-check
    }
    boolean eq( DelayFresh df ) {
      if( this==df ) return true;
      if( _lhs!=df._lhs || _rhs!=df._rhs ) return false;
      if( _frsh!=df._frsh ) return false;
      assert eq_nongen(df);
      return true;
    }
    // Deep equality check nongen
    private boolean eq_nongen( DelayFresh df ) {
      if( _nongen == df._nongen ) return true;
      if( _nongen.length != df._nongen.length ) return false;
      for( int i=0; i<_nongen.length; i++ )
        if( _nongen[i].find()!=df._nongen[i].find() )
          return false;
      return true;
    }
    @Override public String toString() {
      return "delayed_fresh_unify["+_lhs+" to "+_rhs+", "+_nongen+"]";
    }
  }

  // Used by FreshNode to mark delay_fresh on all nongen parts
  public void make_nongen_delay(TV3 rhs, TV3[] nongen, FreshNode frsh ) {
    assert !rhs.unified();
    DelayFresh df = new DelayFresh(this,rhs,nongen,frsh);
    for( TV3 ng : nongen )
      if( ng instanceof TVExpanding tex )
        tex.add_delay_fresh(df);
  }

  // Called from Combo after a Node unification; allows incremental update of
  // Fresh unification.
  public static void do_delay_fresh() {
    int cnt=0;
    while( DELAY_FRESH.len() > 0 ) {
      DelayFresh df = DELAY_FRESH.pop();
      boolean progress = df._lhs.find().fresh_unify(df._frsh,df._rhs.find(),df._nongen,false);
      df._frsh.add_flow();
      assert cnt++ < 20;
    }
  }
  public static void do_delay_resolve() {
    // TODO: Do not have delayed resolve sorted out right
    //if( Combo.HM_AMBI ) // Having failed alread, will never result
    //  DELAY_RESOLVE.clear();
    //else
    while( DELAY_RESOLVE.len() > 0 )
      TVStruct.trial_resolve_all(true,DELAY_RESOLVE.pop().find().as_struct());
  }

  // Union this into that.  Merge the delay worklist
  @Override public void _union_delay(TV3 that) {
    that.merge_delay_fresh(_delay_fresh);
    move_delay();
  }

  // Move delayed-fresh updates onto not-delayed update list.
  void move_delay() {
    _move_delay(DELAY_FRESH  ,_delay_fresh  );
    _move_delay(DELAY_RESOLVE,_delay_resolve);
    if( _may_nil && _use_nil && _widen==2 && !can_progress() ) {
      if( _delay_fresh  !=null ) _delay_fresh  .clear();
      if( _delay_resolve!=null ) _delay_resolve.clear();
    }
  }
  // Copy from src to dst, stripping dups
  static void _move_delay( Ary dst, Ary src ) {
    if( src!=null )
      for( Object x : src )
        if( dst.find(x)== -1 )
          dst.push(x);
  }

  @Override void merge_delay_fresh(Ary<DelayFresh>dfs) {
    if( dfs==null || dfs.len()==0 ) return;
    if( _delay_fresh==null ) _delay_fresh = dfs;
    else {
      // If no progress on the first element, we already added and do not try
      // to add the rest again - AND we stop the cyclic add-all-fields.
      if( !add_delay_fresh(dfs.at(0)) ) return;
      for( DelayFresh df : dfs )
        add_delay_fresh(df);
    }
    super.merge_delay_fresh(dfs);
  }

  // True if this TV3 can progress in-place.
  // Leafs unify and so become some other thing - so cannot update-in-place.
  // Ptr/Bases can fall, until the Type hits bottom, e.g. TypeInt.INT64.
  // Structs can add fields while open, can close, and then can remove fields
  // until empty.
  abstract boolean can_progress();

  // Record that on the delayed fresh list and return that.  If `this` ever
  // unifies to something, we need to Fresh-unify the something with `that`.
  @Override void add_delay_fresh() { if( FRESH_ROOT!=null ) add_delay_fresh(FRESH_ROOT); }
  private boolean add_delay_fresh( DelayFresh df ) {
    df.update();
    // Lazy make a list to hold
    if( _delay_fresh==null ) _delay_fresh = new Ary<>(new DelayFresh[1],0);
    // Dup checks: no dups upon insertion, but due to later unification we
    // might get more dups.  Every time we detect some progress, re-filter for
    // dups.
    for( int i=0; i<_delay_fresh._len; i++ ) {
      DelayFresh dfi = _delay_fresh.at(i);
      if( dfi.update() ) {      // Progress?  Do a dup-check
        for( int j=0; j<i; j++ ) {
          if( _delay_fresh.at(j) == dfi )
            throw unimpl();     // 'i' became a dup, remove 'j'
        }
      }
      // Inserting ROOT, unless a dup
      if( df.eq(dfi) )
        return false;           // Dup, do not insert
    }
    _delay_fresh.push(df);
    assert _delay_fresh.len()<=10; // Switch to worklist format
    return true;
  }

  void add_delay_resolve(TVStruct tvs) {
    if( _delay_resolve==null ) _delay_resolve = new Ary<>(new TVStruct[1],0);
    if( _delay_resolve.find(tvs)== -1 )
      _delay_resolve.push(tvs);
  }

  @Override public TVExpanding copy() {
    TVExpanding tex = (TVExpanding)super.copy();
    tex._delay_fresh = null;
    tex._delay_resolve = null;
    return tex;
  }

  public static void reset_to_init0() {
    DELAY_FRESH.clear();
    DELAY_RESOLVE.clear();
  }
}
