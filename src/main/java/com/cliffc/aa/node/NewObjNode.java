package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;

// Allocates a TypeStruct and produces a Tuple with the TypeStruct and a TypeMemPtr.
//
// During Parsing we construct closures whose field names are discovered as we
// parse.  Hence we support a type which represents some concrete fields, and a
// choice of all possible remaining fields.  The _any choice means we can add
// fields, although the closure remains impossibly low until the lexical scope
// ends and no more fields can appear.

public class NewObjNode extends NewNode<TypeStruct> {
  public final boolean _is_closure; // For error messages
  public       Parse[] _fld_starts; // Start of each tuple member; 0 for the display
  // NewNodes do not really need a ctrl; useful to bind the upward motion of
  // closures so variable stores can more easily fold into them.
  public NewObjNode( boolean is_closure, TypeStruct disp, Node clo ) {
    this(is_closure, BitsAlias.RECORD, disp, clo);
  }
  // Called by IntrinsicNode.convertTypeNameStruct
  public NewObjNode( boolean is_closure, int par_alias, TypeStruct ts, Node clo ) {
    super(OP_NEWOBJ,par_alias,ts,clo);
    _is_closure = is_closure;
    assert ts._ts[0].is_display_ptr();
  }
  public Node get(String name) { int idx = _ts.find(name);  assert idx >= 0; return fld(idx); }
  public boolean exists(String name) { return _ts.find(name)!=-1; }
  public boolean is_mutable(String name) {
    byte fmod = _ts.fmod(_ts.find(name));
    return fmod == TypeStruct.FRW;
  }
  // Called when folding a Named Constructor into this allocation site
  void set_name( TypeStruct name ) { assert !name.above_center();  sets_in(name); }

  // No more fields
  public void no_more_fields() { sets_in(_ts.close()); }

  // Create a field from parser for an inactive this
  public void create( String name, Node val, byte mutable, GVNGCM gvn) {
    assert !Util.eq(name,"^"); // Closure field created on init
    gvn.unreg(this);
    create_active(name,val,mutable);
    gvn.rereg(this,value(gvn._opt_mode)); // Re-insert with field added
    for( Node use : _uses ) {
      use.xval(gvn._opt_mode);  // Record "downhill" type for OProj, DProj
      gvn.add_work_uses(use);   // Neighbors on worklist
    }
    assert touched();
  }

  // Create a field from parser for an active this
  public void create_active( String name, Node val, byte mutable ) {
    assert !touched();
    assert def_idx(_ts._ts.length)== _defs._len;
    assert _ts.find(name) == -1; // No dups
    add_def(val);
    sets_out(_ts.add_fld(name,mutable,mutable==TypeStruct.FFNL ? val._val : Type.SCALAR));
  }
  public void update( String tok, byte mutable, Node val, GVNGCM gvn  ) { update(_ts.find(tok),mutable,val,gvn); }
  // Update the field & mod
  public void update( int fidx, byte mutable, Node val, GVNGCM gvn  ) {
    assert def_idx(_ts._ts.length)== _defs._len;
    gvn.set_def_reg(this,def_idx(fidx),val);
    sets_in(_ts.set_fld(fidx,mutable==TypeStruct.FFNL ? val._val : Type.SCALAR,mutable));
  }
  // Update default value.  Used by StoreNode folding into a NewObj initial
  // state.  Used by the Parser when updating local variables... basically
  // another store.
  public void update_active( int fidx, byte mutable, Node val, GVNGCM gvn  ) {
    assert !touched();
    assert def_idx(_ts._ts.length)== _defs._len;
    set_def(def_idx(fidx),val,gvn);
    sets_out(_ts.set_fld(fidx,mutable==TypeStruct.FFNL ? val._val : Type.SCALAR,mutable));
  }


  // Add a named FunPtr to a New.  Auto-inflates to a Unresolved as needed.
  public FunPtrNode add_fun( Parse bad, String name, FunPtrNode ptr, GVNGCM gvn ) {
    int fidx = _ts.find(name);
    if( fidx == -1 ) {
      create_active(name,ptr,TypeStruct.FFNL);
    } else {
      Node n = _defs.at(def_idx(fidx));
      if( n instanceof UnresolvedNode ) n.add_def(ptr);
      else n = new UnresolvedNode(bad,n,ptr);
      n.xval(gvn._opt_mode); // Update the input type, so the _ts field updates
      update_active(fidx,TypeStruct.FFNL,n,gvn);
    }
    return ptr;
  }

  // The current local scope ends, no more names will appear.  Forward refs
  // first found in this scope are assumed to be defined in some outer scope
  // and get promoted.  Other locals are no longer kept alive, but live or die
  // according to use.
  public void promote_forward(GVNGCM gvn, NewObjNode parent) {
    assert parent != null;
    TypeStruct ts = _ts;
    for( int i=0; i<ts._ts.length; i++ ) {
      Node n = fld(i);
      if( n != null && n.is_forward_ref() ) {
        // Make field in the parent
        parent.create(ts._flds[i],n,ts.fmod(i),gvn);
        // Stomp field locally to XSCALAR
        gvn.set_def_reg(this,def_idx(i),gvn.con(Type.XSCALAR));
        sets_in(_ts.set_fld(i,Type.XSCALAR,TypeStruct.FFNL));
      }
    }
  }

  @Override public Node ideal(GVNGCM gvn, int level) {
    Node n = super.ideal(gvn,level);
    if( n != null ) return n;

    // If a field is unused, remove it.  Right now limited to the field being a
    // pointer to a dead New.
    boolean progress = false;
    for( int i=1; i<_defs._len; i++ )
      if( in(i) instanceof ProjNode && in(i).in(0) instanceof NewNode ) {
        NewNode nnn = (NewNode)in(i).in(0);
        if( nnn.is_unused() )
          { set_def(i,gvn.con(Type.ANY),gvn); progress=true; }
      }
    if( progress ) return this;

    // If the value lifts a final field, so does the default lift.
    if( _val instanceof TypeTuple ) {
      TypeTuple ts1 = (TypeTuple)_val;
      TypeObj ts3 = (TypeObj)ts1.at(0);
      if( ts3 != TypeObj.UNUSED ) {
        TypeStruct ts4 = _ts.make_from(((TypeStruct)ts3)._ts);
        TypeStruct ts5 = ts4.crush();
        assert ts4.isa(ts5);
        if( ts5 != _crushed && ts5.isa(_crushed) ) {
          sets_in(ts4);
          return this;
        }
      }
    }
    return null;
  }

  @Override TypeObj valueobj() {
    // Gather args and produce a TypeStruct
    Type[] ts = Types.get(_ts._ts.length);
    for( int i=0; i<ts.length; i++ )
      ts[i] = fld(i)._val;
    return _ts.make_from(ts);  // Pick up field names and mods
  }
  @Override TypeStruct dead_type() { return TypeStruct.ANYSTRUCT; }
  // All fields are escaping
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) { return TypeMem.ESCAPE; }
  @Override public TypeMem live(GVNGCM.Mode opt_mode) {
    // The top scope is always alive, and represents what all future unparsed
    // code MIGHT do.
    if( _keep==1 && _uses._len==0 )
      return TypeMem.ALIVE;
    return super.live(opt_mode);
  }
}
