package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.Util;

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
  public final boolean _is_closure; // For error messages
  public       Parse[] _fld_starts; // Start of each tuple member; 0 for the display
  // NewNodes do not really need a ctrl; useful to bind the upward motion of
  // closures so variable stores can more easily fold into them.
  public NewObjNode( boolean is_closure, TypeStruct disp, Node clo ) {
    super(OP_NEWOBJ,BitsAlias.REC,disp);
    assert disp.fld_find("^").is_display_ptr();
    _is_closure = is_closure;
    add_def(clo);
  }
  // Called by IntrinsicNode.convertTypeNameStruct
  public NewObjNode( boolean is_closure, int alias, TypeStruct ts, Node clo ) {
    super(OP_NEWOBJ,alias,ts,clo);
    assert ts.fld_find("^").is_display_ptr();
    _is_closure = is_closure;
  }
  public Node get(String name) { return in(_ts.fld_find(name)._order); }
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
    setsm(_ts.add_fld(name,mutable,mutable==Access.Final ? val._val : Type.SCALAR,_defs._len));
    create_edge(val);
  }
  // Used by IntrinsicNode
  public void create_edge( Node val ) {
    add_def(val);
    Env.GVN.add_flow(this);
  }
  public void update( String tok, Access mutable, Node val ) { update(_ts.fld_find(tok),mutable,val); }
  // Update the field & mod
  private void update( TypeFld fld, Access mutable, Node val ) {
     set_def(fld._order,val);
     sets(_ts.replace_fld(fld.make_from(mutable==Access.Final ? val._val : Type.SCALAR,mutable)));
     xval();
     Env.GVN.add_flow_uses(this);
  }


  // Add a named FunPtr to a New.  Auto-inflates to a Unresolved as needed.
  public FunPtrNode add_fun( Parse bad, String name, FunPtrNode ptr ) {
    TypeFld fld = _ts.fld_find(name);
    if( fld == null ) {
      create_active(name,ptr,Access.Final);
    } else {
      Node n = in(fld._order);
      if( n instanceof UnresolvedNode ) n.add_def(ptr);
      else n = new UnresolvedNode(bad,n,ptr);
      n.xval(); // Update the input type, so the _ts field updates
      update(fld,Access.Final,n);
    }
    return ptr;
  }

  // The current local scope ends, no more names will appear.  Forward refs
  // first found in this scope are assumed to be defined in some outer scope
  // and get promoted.  Other locals are no longer kept alive, but live or die
  // according to use.
  public void promote_forward( NewObjNode parent ) {
    assert parent != null;
    for( TypeFld fld : _ts.flds() ) {
      Node n = in(fld._order);
      if( n != null && n.is_forward_ref() ) {
        // Remove current display from forward-refs display choices.
        assert Env.LEX_DISPLAYS.test(_alias);
        TypeMemPtr tdisp = TypeMemPtr.make(Env.LEX_DISPLAYS.clear(_alias),TypeObj.ISUSED);
        n.set_def(1,Node.con(tdisp)); // TODO: BUGGY?  NEEDS TO CRAWL THE DISPLAY 1 LEVEL?
        n.xval();
        // Make field in the parent
        parent.create(fld._fld,n,fld._access);
        // Stomp field locally to ANY
        set_def(fld._order,Env.ANY);
        setsm(_ts.replace_fld(fld.make_from(Type.ANY,Access.Final)));
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
  @Override public void add_work_extra(Work work,Type old) {
    super.add_work_extra(work,old);
    Env.GVN.add_mono(this); // Can update crushed
  }

  private static final Ary<TypeFld> FLDS = new Ary<>(TypeFld.class);
  @Override TypeObj valueobj() {
    assert FLDS.isEmpty();
    // Gather args and produce a TypeStruct
    for( TypeFld fld : _ts.flds() ) {
      // Open NewObjs assume all field types are crushed to error, except the
      // display which is required (and not crushable) for parsing.
      Type t = _ts._open && !Util.eq(fld._fld,"^") ? Type.ALL : val(fld._order);
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
    int idx=0;  while( in(idx)!=def ) idx++; // Index of node
    Type t = ((TypeStruct)to).fld_idx(idx)._t;
    return t.above_center() ? TypeMem.DEAD : (t==Type.NSCALR ? TypeMem.LESC_NO_DISP : TypeMem.ESCAPE);
  }

  @Override public TV2 new_tvar(String alloc_site) { return TV2.make_struct(this,alloc_site); }

  @Override public boolean unify( Work work ) {
    TV2 rec = tvar();
    if( rec.is_err() ) return false;
    assert rec.is_struct();

    // One time (post parse) pick up the complete field list.
    if( rec.open() )
      return work==null ||      // Cutout before allocation if testing
        rec.unify(TV2.make_struct(this,"NewObj_unify",_ts,_defs),work);

    // Extra fields are unified as Error since they are not created here:
    // error to load from a non-existing field.
    boolean progress = false;
    if( !is_unused() )
      for( String key : rec.args() )
        if( _ts.fld_find(key)==null && !rec.get(key).is_err() ) {
          if( work==null ) return true;
          progress |= rec.get(key).unify(rec.miss_field(this,key,"NewObj_err"),work);
          if( (rec=rec.find()).is_err() ) return true;
        }

    // Unify existing fields.  Ignore extras on either side.
    for( TypeFld fld : _ts.flds() ) {
      TV2 tvfld = rec.get(fld._fld);
      if( tvfld != null &&      // Limit to matching fields
          (progress |= tvfld.unify(tvar(fld._order),work)) &&
          work==null )
        return true; // Fast cutout if testing
    }
    rec.push_dep(this);
    return progress;
  }
}
