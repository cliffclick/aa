package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.Util;

import java.util.IdentityHashMap;

import static com.cliffc.aa.AA.*;
import static com.cliffc.aa.type.TypeFld.Access;


// Allocates a TypeStruct and produces a Tuple with the TypeStruct and a TypeMemPtr.
//
// During Parsing we construct closures whose field names are discovered as we
// parse.  Hence we support a type which represents some concrete fields, and a
// choice of all possible remaining fields.  The _any choice means we can add
// fields, although the closure remains impossibly low until the lexical scope
// ends and no more fields can appear.

public class NewObjNode extends NewNode<TypeStruct> {
  // Map from field names to Node indices
  public final IdentityHashMap<String,Integer> _idxs;
  public final boolean _is_closure; // For error messages
  public       Parse[] _fld_starts; // Start of each tuple member; 0 for the display
  // NewNodes do not really need a ctrl; useful to bind the upward motion of
  // closures so variable stores can more easily fold into them.
  public NewObjNode( boolean is_closure, TypeStruct disp, Node clo ) {
    super(OP_NEWOBJ,BitsAlias.REC,disp);
    assert disp.fld_find("^").is_display_ptr();
    _idxs = new IdentityHashMap<>();
    _is_closure = is_closure;
    add_def(clo);
    _idxs.put("^",_defs._len-1);
  }
  // Called by IntrinsicNode.convertTypeNameStruct
  public NewObjNode( boolean is_closure, int alias, TypeStruct ts, Node clo ) {
    super(OP_NEWOBJ,alias,ts,clo);
    assert ts.fld_find("^").is_display_ptr();
    _idxs = new IdentityHashMap<>();
    _is_closure = is_closure;
    _idxs.put("^",_defs._len-1);
  }
  public Node get(String name) { return in(_idxs.get(name)); }
  public boolean exists(String name) { return _ts.fld_find(name)!=null; }
  public boolean is_mutable(String name) { return access(name)==Access.RW; }
  public Access access(String name) { return _ts.fld_find(name)._access; }

  // Called when folding a Named Constructor into this allocation site
  void set_name( TypeStruct name ) { assert !name.above_center();  setsm(name); }

  // No more fields
  public void no_more_fields() { setsm(_ts.close()); }

  // Create a field from parser for an inactive this
  public void create( String name, Node val, Access mutable ) {
    assert !Util.eq(name,"^") && !Util.eq(name,TypeFld.fldBot); // Closure field created on init
    create_active(name,val,mutable);
  }
  // Create a field from parser for an active this
  public void create_active( String name, Node val, Access mutable ) {
    assert def_idx(_ts.len())== _defs._len;
    assert _ts.fld_find(name) == null; // No dups
    setsm(_ts.add_fld(name,mutable,mutable==Access.Final ? val._val : Type.SCALAR));
    create_edge(name,val);
  }
  // Used by IntrinsicNode
  public void create_edge( String name, Node val ) {
    _idxs.put(name,_defs._len);
    add_def(val);
    Env.GVN.add_flow(this);
  }
  public void update( String tok, Access mutable, Node val ) { update(_idxs.get(tok),tok,mutable,val); }
  // Update the field & mod
  private void update( int idx, String name, Access mutable, Node val ) {
     assert def_idx(_ts.len())== _defs._len;
     set_def(idx,val);
     sets(_ts.set_fld(name,mutable,mutable==Access.Final ? val._val : Type.SCALAR));
     xval();
     Env.GVN.add_flow_uses(this);
  }


  // Add a named FunPtr to a New.  Auto-inflates to a Unresolved as needed.
  public FunPtrNode add_fun( Parse bad, String name, FunPtrNode ptr ) {
    TypeFld fld = _ts.fld_find(name);
    if( fld == null ) {
      create_active(name,ptr,Access.Final);
    } else {
      int idx = _idxs.get(name);
      Node n = in(idx);
      if( n instanceof UnresolvedNode ) n.add_def(ptr);
      else n = new UnresolvedNode(bad,n,ptr);
      n.xval(); // Update the input type, so the _ts field updates
      update(idx,name,Access.Final,n);
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
    for( TypeFld fld : _ts.flds() ) {
      int idx = _idxs.get(fld._fld);
      Node n = in(idx);
      if( n != null && n.is_forward_ref() ) {
        // Remove current display from forward-refs display choices.
        assert Env.LEX_DISPLAYS.test(_alias);
        TypeMemPtr tdisp = TypeMemPtr.make(Env.LEX_DISPLAYS.clear(_alias),TypeObj.ISUSED);
        n.set_def(1,Node.con(tdisp)); // TODO: BUGGY?  NEEDS TO CRAWL THE DISPLAY 1 LEVEL?
        n.xval();
        // Make field in the parent
        parent.create(fld._fld,n,fld._access);
        // Stomp field locally to ANY
        set_def(idx,Env.ANY);
        setsm(_ts.set_fld(fld._fld,Access.Final,Type.ANY));
        Env.GVN.add_flow_uses(n);
      }
    }
  }

  @Override public Node ideal_mono() {
    // If the value lifts a final field, so does the default lift.
    if( _val instanceof TypeTuple ) {
      TypeObj ts3 = (TypeObj)((TypeTuple)_val).at(MEM_IDX);
      if( ts3 != TypeObj.UNUSED ) {
        TypeStruct ts4 = _ts.make_from((TypeStruct)ts3);
        TypeStruct ts5 = _ts.crush();
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

  private static final Ary<TypeFld> FLDS = new Ary<>(TypeFld.class);
  @Override TypeObj valueobj() {
    assert FLDS.isEmpty();
    // Gather args and produce a TypeStruct
    for( TypeFld fld : _ts.flds() ) {
      // Open NewObjs assume all field types are crushed to error, except the
      // display which is required (and not crushable) for parsing.
      Type t = _ts._open && !Util.eq(fld._fld,"^") ? Type.ALL : val(_idxs.get(fld._fld));
      FLDS.push(fld.make_from(t));
    }
    TypeStruct ts = _ts.make_from(FLDS);
    FLDS.clear();
    return ts;
  }
  @Override TypeStruct dead_type() { return TypeStruct.ANYSTRUCT; }

  // Only alive fields in the MrgProj escape
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    TypeObj to = _live.at(_alias);
    if( !(to instanceof TypeStruct) ) return to.above_center() ? TypeMem.DEAD : TypeMem.ESCAPE;
    // TODO: Could use an inverted map here
    String name = null;
    for( String n : _idxs.keySet() )
      if( in(_idxs.get(n))==def )
        { name=n; break; }
    Type t = ((TypeStruct)to).at(name);
    return t.above_center() ? TypeMem.DEAD : (t==Type.NSCALR ? TypeMem.LESC_NO_DISP : TypeMem.ESCAPE);
  }

  // As formals to a call.
  TypeTuple as_formals() {
    Type[] ts2 = Types.get(_ts.len()+DSP_IDX);
    ts2[CTL_IDX] = Type.CTRL;
    ts2[MEM_IDX] = TypeMem.ALLMEM;
    for( TypeFld fld : _ts.flds() )
      ts2[DSP_IDX+_idxs.get(fld._fld)-1] = fld._t;
    return TypeTuple.make(ts2);
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
