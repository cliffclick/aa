package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;

import static com.cliffc.aa.AA.MEM_IDX;
import static com.cliffc.aa.type.TypeFld.Access;

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
    super(OP_NEWOBJ,BitsAlias.REC,disp);
    add_def(clo);
    _is_closure = is_closure;
    assert disp.fld(0).is_display_ptr();
  }
  // Called by IntrinsicNode.convertTypeNameStruct
  public NewObjNode( boolean is_closure, int alias, TypeStruct ts, Node clo ) {
    super(OP_NEWOBJ,alias,ts,clo);
    _is_closure = is_closure;
    assert ts.fld(0).is_display_ptr();
  }
  public Node get(String name) { int idx = _ts.fld_find(name);  assert idx >= 0; return fld(idx); }
  public boolean exists(String name) { return _ts.fld_find(name)!=-1; }
  public boolean is_mutable(String name) {
    return _ts.fld(_ts.fld_find(name))._access==Access.RW;
  }
  //public Access mutable(String name) { return _ts.fmod(_ts.find(name)); }

  // Called when folding a Named Constructor into this allocation site
  void set_name( TypeStruct name ) { assert !name.above_center();  setsm(name); }

  // No more fields
  public void no_more_fields() { setsm(_ts.close()); }

  // Create a field from parser for an inactive this
  public void create( String name, Node val, Access mutable ) {
    assert !Util.eq(name,"^"); // Closure field created on init
    create_active(name,val,mutable);
  }

  // Create a field from parser for an active this
  public void create_active( String name, Node val, Access mutable ) {
    assert def_idx(_ts.len())== _defs._len;
    assert _ts.fld_find(name) == -1; // No dups
    add_def(val);
    setsm(_ts.add_fld(name,mutable,mutable==Access.Final ? val._val : Type.SCALAR));
    Env.GVN.add_flow(this);
  }
  public void update( String tok, Access mutable, Node val ) { update(_ts.fld_find(tok),mutable,val); }
  // Update the field & mod
  public void update( int fidx, Access mutable, Node val ) {
    assert def_idx(_ts.len())== _defs._len;
    set_def(def_idx(fidx),val);
    sets(_ts.set_fld(fidx,mutable==Access.Final ? val._val : Type.SCALAR,mutable));
    xval();
    Env.GVN.add_flow_uses(this);
  }


  // Add a named FunPtr to a New.  Auto-inflates to a Unresolved as needed.
  public FunPtrNode add_fun( Parse bad, String name, FunPtrNode ptr ) {
    int fidx = _ts.fld_find(name);
    if( fidx == -1 ) {
      create_active(name,ptr,Access.Final);
    } else {
      Node n = _defs.at(def_idx(fidx));
      if( n instanceof UnresolvedNode ) n.add_def(ptr);
      else n = new UnresolvedNode(bad,n,ptr);
      n.xval(); // Update the input type, so the _ts field updates
      update(fidx,Access.Final,n);
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
    for( int i=0; i<ts.len(); i++ ) {
      Node n = fld(i);
      if( n != null && n.is_forward_ref() ) {
        // Remove current display from forward-refs display choices.
        assert Env.LEX_DISPLAYS.test(_alias);
        TypeMemPtr tdisp = TypeMemPtr.make(Env.LEX_DISPLAYS.clear(_alias),TypeObj.ISUSED);
        n.set_def(1,Node.con(tdisp)); // TODO: BUGGY?  NEEDS TO CRAWL THE DISPLAY 1 LEVEL?
        n.xval();
        // Make field in the parent
        TypeFld fld = ts.fld(i);
        parent.create(fld._fld,n,fld._access);
        // Stomp field locally to ANY
        set_def(def_idx(i),Env.ANY);
        setsm(_ts.set_fld(i,Type.ANY,Access.Final));
        Env.GVN.add_flow_uses(n);
      }
    }
  }

  @Override public Node ideal_mono() {
    // If the value lifts a final field, so does the default lift.
    if( _val instanceof TypeTuple ) {
      TypeObj ts3 = (TypeObj)((TypeTuple)_val).at(MEM_IDX);
      if( ts3 != TypeObj.UNUSED ) {
        TypeStruct ts4 = _ts.make_from_flds((TypeStruct)ts3);
        TypeStruct ts5 = ts4.crush();
        assert ts4.isa(ts5);
        if( ts5 != _crushed && ts5.isa(_crushed) ) {
          setsm(ts4);
          Env.GVN.add_flow(Env.DEFMEM);
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
    TypeFld[] ts = TypeFlds.get(_ts.len());
    for( int i=0; i<ts.length; i++ )
      ts[i] = _ts.fld(i).make_from((_ts._open && i>0) ? Type.ALL : fld(i)._val);
    return _ts.make_from(ts);  // Pick up field names and mods
  }
  @Override TypeStruct dead_type() { return TypeStruct.ANYSTRUCT; }

  // Only alive fields in the MrgProj escape
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    TypeObj to = _live.at(_alias);
    if( !(to instanceof TypeStruct) ) return to.above_center() ? TypeMem.DEAD : TypeMem.ESCAPE;
    int idx = _defs.find(def)-1;
    Type t = ((TypeStruct)to).at(idx);
    return t.above_center() ? TypeMem.DEAD : (t==Type.NSCALR ? TypeMem.LESC_NO_DISP : TypeMem.ESCAPE);
  }

  //@Override public boolean unify( boolean test ) {
  //  // Self should always should be a TObj
  //  TV2 tvar = tvar();
  //  if( tvar.is_dead() ) return false;
  //  assert tvar.isa("Obj");
  //  // Structural unification on all fields
  //  boolean progress=false;
  //  for( int i=0; i<_ts._flds.length; i++ ) {
  //    progress |= tvar.unify_at(_ts._flds[i],tvar(def_idx(i)),test);
  //    if( progress && test ) return true;
  //  }
  //  return progress;
  //}
}
