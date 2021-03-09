package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;

import static com.cliffc.aa.AA.MEM_IDX;

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
    this(is_closure, BitsAlias.REC, disp, clo);
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
  void set_name( TypeStruct name ) { assert !name.above_center();  setsm(name); }

  // No more fields
  public void no_more_fields() { setsm(_ts.close()); }

  // Create a field from parser for an inactive this
  public void create( String name, Node val, byte mutable ) {
    assert !Util.eq(name,"^"); // Closure field created on init
    create_active(name,val,mutable);
  }

  // Create a field from parser for an active this
  public void create_active( String name, Node val, byte mutable ) {
    assert def_idx(_ts._ts.length)== _defs._len;
    assert _ts.find(name) == -1; // No dups
    add_def(val);
    setsm(_ts.add_fld(name,mutable,mutable==TypeStruct.FFNL ? val._val : Type.SCALAR));
    Env.GVN.add_flow(this);
  }
  public void update( String tok, byte mutable, Node val ) { update(_ts.find(tok),mutable,val); }
  // Update the field & mod
  public void update( int fidx, byte mutable, Node val ) {
    assert def_idx(_ts._ts.length)== _defs._len;
    set_def(def_idx(fidx),val);
    sets(_ts.set_fld(fidx,mutable==TypeStruct.FFNL ? val._val : Type.SCALAR,mutable));
    tvar().reset_at(_ts._flds[fidx]);
    xval();
    Env.GVN.add_flow_uses(this);
  }


  // Add a named FunPtr to a New.  Auto-inflates to a Unresolved as needed.
  public FunPtrNode add_fun( Parse bad, String name, FunPtrNode ptr ) {
    int fidx = _ts.find(name);
    if( fidx == -1 ) {
      create_active(name,ptr,TypeStruct.FFNL);
    } else {
      Node n = _defs.at(def_idx(fidx));
      if( n instanceof UnresolvedNode ) n.add_def(ptr);
      else n = new UnresolvedNode(bad,n,ptr);
      n.xval(); // Update the input type, so the _ts field updates
      update(fidx,TypeStruct.FFNL,n);
    }
    return ptr;
  }

  // The current local scope ends, no more names will appear.  Forward refs
  // first found in this scope are assumed to be defined in some outer scope
  // and get promoted.  Other locals are no longer kept alive, but live or die
  // according to use.
  public void promote_forward( NewObjNode parent ) {
    assert parent != null;
    TypeStruct ts = _ts;
    for( int i=0; i<ts._ts.length; i++ ) {
      Node n = fld(i);
      if( n != null && n.is_forward_ref() ) {
        // Remove current display from forward-refs display choices.
        assert Env.LEX_DISPLAYS.test(_alias);
        TypeMemPtr tdisp = TypeMemPtr.make(Env.LEX_DISPLAYS.clear(_alias),TypeObj.ISUSED);
        n.set_def(1,Node.con(tdisp)); // TODO: BUGGY?  NEEDS TO CRAWL THE DISPLAY 1 LEVEL?
        n.xval();
        // Make field in the parent
        String fld = ts._flds[i];
        parent.create(fld,n,ts.fmod(i));
        // Stomp field locally to ANY
        set_def(def_idx(i),Env.ANY);
        setsm(_ts.set_fld(i,Type.ANY,TypeStruct.FFNL));
        tvar().reset_at(fld);
        Env.GVN.add_flow_uses(n);
      }
    }
  }

  @Override public Node ideal_mono() {
    // If the value lifts a final field, so does the default lift.
    if( _val instanceof TypeTuple ) {
      TypeObj ts3 = (TypeObj)((TypeTuple)_val).at(MEM_IDX);
      if( ts3 != TypeObj.UNUSED ) {
        TypeStruct ts4 = _ts.make_from(((TypeStruct)ts3)._ts);
        TypeStruct ts5 = ts4.crush();
        assert ts4.isa(ts5);
        if( ts5 != _crushed && ts5.isa(_crushed) ) {
          setsm(ts4);
          return this;
        }
      }
    }
    return null;
  }
  @Override public void add_flow_extra(Type old) {
    Env.GVN.add_mono(this); // Can update crushed
  }

  @Override TypeObj valueobj() {
    // Gather args and produce a TypeStruct
    Type[] ts = Types.get(_ts._ts.length);
    for( int i=0; i<ts.length; i++ )
      ts[i] = (_ts._open && i>0) ? Type.ALL : fld(i)._val;
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

  @Override public TV2 new_tvar(String alloc_site) { return TV2.make("Obj",this,alloc_site); }

  @Override public boolean unify( boolean test ) {
    // Self should always should be a TObj
    TV2 tvar = tvar();
    if( tvar.is_dead() ) return false;
    assert tvar.isa("Obj");
    // Structural unification on all fields
    boolean progress=false;
    for( int i=0; i<_ts._flds.length; i++ ) {
      progress |= tvar.unify_at(_ts._flds[i],tvar(def_idx(i)),test);
      if( progress && test ) return true;
    }
    return progress;
  }

  public Node[] parms() {
    throw com.cliffc.aa.AA.unimpl(); // TODO: yank this
    //return Arrays.copyOfRange(_defs._es,1,_defs._len); // All defs
  }
}
