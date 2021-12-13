package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
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
    assert disp.get("^")!=null;
    _is_closure = is_closure;
    add_def(clo);
  }
  // Called by IntrinsicNode.convertTypeNameStruct
  public NewObjNode( boolean is_closure, int alias, TypeStruct ts, Node clo ) {
    super(OP_NEWOBJ,alias,ts,clo);
    assert ts.get("^")!=null;
    _is_closure = is_closure;
  }
  public Node get(String name) { return in(_ts.get(name)._order); }
  public boolean exists(String name) { return _ts.get(name)!=null; }
  public boolean is_mutable(String name) { return access(name)==Access.RW; }
  public Access access(String name) { return _ts.get(name)._access; }

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
  public void update( String tok, Access mutable, Node val ) { update(_ts.get(tok),mutable,val); }
  // Update the field & mod
  private void update( TypeFld fld, Access mutable, Node val ) {
     set_def(fld._order,val);
     sets(_ts.replace_fld(fld.make_from(mutable==Access.Final ? val._val : Type.SCALAR,mutable)));
     xval();
     Env.GVN.add_flow_uses(this);
  }


  // Add a named FunPtr to a New.  Auto-inflates to a Unresolved as needed.
  public void add_fun( Parse bad, String name, FunPtrNode ptr ) {
    TypeFld fld = _ts.get(name);
    if( fld == null ) {
      create_active(name,ptr,Access.Final);
    } else {
      // TODO: Problem: keep taking stores until scope closes, and tpye keeps falling
      Node n = in(fld._order);
      UnresolvedNode unr = n==Env.XNIL
        ? new UnresolvedNode(name,bad).scoped()
        : (UnresolvedNode)n;
      unr.add_fun(ptr);
      update(fld,Access.Final,unr);
    }
  }

  // The current local scope ends, no more names will appear.  Forward refs
  // first found in this scope are assumed to be defined in some outer scope
  // and get promoted.  Other locals are no longer kept alive, but live or die
  // according to use.
  public void promote_forward( NewObjNode parent ) {
    assert parent != null;
    for( TypeFld fld : _ts.flds() ) {
      Node n = in(fld._order);
      if( n.is_forward_ref() ) {
        // Is this Unresolved defined in this scope, or some outer scope?
        if( ((UnresolvedNode)n).is_scoped() ) {
          // Definitely defined here, and all stores are complete; all fcns added
          ((UnresolvedNode)n).define();
          Env.GVN.add_unuse(n);
        } else {
          // Make field in the parent
          parent.create(fld._fld,n,fld._access);
          // Stomp field locally to ANY
          set_def(fld._order,Env.ANY);
          setsm(_ts.replace_fld(fld.make_from(Type.ANY,Access.Final)));
          Env.GVN.add_flow_uses(n);
        }
      }
    }
  }

  @Override public Node ideal_reduce() {
    Node x = super.ideal_reduce();
    if( x!=null ) return x;
    if( is_prim() ) return null;
    // Dead fields are set to ANY
    TypeObj to = _live.at(_alias);
    if( !(to instanceof TypeStruct) ) return null;
    TypeStruct ts = (TypeStruct)to;
    Node progress = null;
    for( TypeFld tfld : _ts.flds() ) {
      TypeFld lfld = ts.get(tfld._fld);
      if( lfld !=null && lfld._t==Type.XSCALAR ) {
        int idx = lfld._order;
        if( in(idx) != Env.ANY )
          progress = set_def(idx,Env.ANY);
      }
    }
    return progress;
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
          return this;
        }
      }
    }
    return null;
  }
  @Override public void add_flow_extra(Type old) {
    super.add_flow_extra(old);
    Env.GVN.add_mono(this); // Can update crushed
  }

  private static final Ary<TypeFld> FLDS = new Ary<>(TypeFld.class);
  @Override TypeObj valueobj() {
    assert FLDS.isEmpty();
    // Gather args and produce a TypeStruct
    for( TypeFld fld : _ts.flds() ) {
      // TODO: why assume crushed to error?  primitive scope is open and do not want it crushed
      Type t = val(fld._order);
      FLDS.push(fld.make_from(t));
    }
    TypeStruct ts = _ts.make_from(FLDS);
    FLDS.clear();
    return ts;
  }
  @Override TypeStruct dead_type() { return TypeStruct.ANYSTRUCT; }

  // Only alive fields in the MrgProj escape
  @Override public TypeMem live_use(Node def ) {
    TypeObj to = _live.at(_alias);
    if( !(to instanceof TypeStruct) ) return to.oob(TypeMem.ALIVE);
    int idx=0;  while( in(idx)!=def ) idx++; // Index of node
    TypeFld fld = ((TypeStruct)to).fld_idx(idx);
    if( fld==null ) return TypeMem.DEAD; // No such field is alive
    Type t = fld._t;
    return t.oob(TypeMem.ALIVE);
  }

  @Override public TV2 new_tvar(String alloc_site) { return TV2.make_struct(this,alloc_site); }

  @Override public boolean unify( boolean test ) {
    TV2 rec = tvar();
    if( rec.is_err() ) return false;
    assert rec.is_struct();

    // One time (post parse) pick up the complete field list.
    if( rec.open() )
      return test ||            // Cutout before allocation if testing
        rec.unify(TV2.make_struct(this,"NewObj_unify",_ts,_defs),test);

    // Extra fields are unified as Error since they are not created here:
    // error to load from a non-existing field.
    boolean progress = false;
    if( !is_unused() )
      for( String key : rec.args() )
        if( _ts.get(key)==null && !rec.get(key).is_err() ) {
          if( test ) return true;
          progress |= rec.get(key).unify(rec.miss_field(this,key,"NewObj_err"),test);
          if( (rec=rec.find()).is_err() ) return true;
        }

    // Unify existing fields.  Ignore extras on either side.
    for( TypeFld fld : _ts.flds() ) {
      TV2 tvfld = rec.get(fld._fld);
      if( tvfld != null &&      // Limit to matching fields
          (progress |= tvfld.unify(tvar(fld._order),test)) &&
          test )
        return true; // Fast cutout if testing
    }
    rec.push_dep(this);
    return progress;
  }
}
