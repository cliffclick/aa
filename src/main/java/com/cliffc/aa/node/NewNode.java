package com.cliffc.aa.node;

import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMemPtr;
import com.cliffc.aa.type.TypeStruct;

import static com.cliffc.aa.AA.unimpl;

// Allocates a TypeStruct
//
// NewNodes have a unique alias class - they do not alias with any other
// NewNode, even if they have the same type.  Upon cloning both NewNodes get
// new aliases that inherit (tree-like) from the original alias.
//
// The inputs mirror the standard input pattern; CTL_IDX is null, MEM_IDX is
// null, DSP_IDX is the display field, and the other fields follow.
//
// NewNodes can be forward_refs; this is temporary until the definition is
// complete.
//
// NewNodes can be used as "stack frames" for closures.  All fields up until
// nargs are incoming parameters (and HM treats as lambda arguments).  All
// fields after nargs are treated as normal let-bound definitions.
//
// NewNodes can be used as "records" or "class instances".  All the fields are
// treated by HM as record fields.  These can be named or unnamed; unnamed
// records are basically C-style structs.
//
// NewNodes can further be broken into value types vs reference types.
// Value types have ONLY final fields, and are copied by value.  They have no
// memory state, no unique memory id, no "pointer" nor "address".  Reference
// types DO have memory state, and a unique pointer (memory id).
//
// Named NewNodes have their globally unique mangled name in Env.PROTOS.  All
// eager-final-fields are moved into the prototype, and non-final fields are in
// the local instances.  In particular, locally defined function assignments
// are all eager-final and moved into the PROTOS and take no local space.
// Loads against an instance check to see if the field is eager-final or not,
// and load against either the local instance or the prototype as needed.  No
// runtime check needed for local vs PROTOs.

public class NewNode extends Node {
  // Unique alias class, one class per unique memory allocation site.
  // Only effectively-final, because the copy/clone sets a new alias value.
  public int _alias, _reset_alias; // Alias class

  // For closures, the number of fields which are initial incoming arguments
  // (Lambda args) vs local assignments (Let bound args).  Effectively final
  // AFTER all the args are added.

  // For non-closure value objects, is the default argment count to the
  // constructor.
  //public int _nargs;

  // A list of field names and field-mods, folded into the initial state of
  // this New.  These can come from initializers at parse-time, or stores
  // folded in.  There are no types stored here; types come from the inputs.
  //public TypeStruct _ts; // Base object type, representing all possible future values

  // Just TMP.make(_alias,ISUSED)
  public TypeMemPtr _tptr;
  // Prototype name (with the ':') or null
  public final String _tname;

  // Takes an alias only
  public NewNode( boolean closure, boolean forward_ref, String tname, int alias ) {
    super(OP_NEW, null, null);
    assert !closure || tname==null;
    _reset_alias = alias;       // Allow a reset, if this alias splits and then we want to run a new test
    //_forward_ref = forward_ref;
    //_tname=tname;
    //_init( alias, TypeStruct.EMPTY);
    throw unimpl();
  }

  private void _init(int alias, TypeStruct ts) {
    if( _elock ) unelock();    // Unlock before changing hash
    _alias = alias;
    //assert ts._name.isEmpty() || Util.eq(ts._name,_tname);
    //if( ts._name.isEmpty() && _tname!=null ) ts = ts.set_name(_tname);
    //TypeStruct flat = TypeStruct.ISUSED;
    //if( _tname!=null ) flat = flat.set_name(_tname);
    //_tptr = TypeMemPtr.make(BitsAlias.make0(alias),flat);
    //sets(ts);
    throw unimpl();
  }
  private void sets(TypeStruct ts) {
    //_ts = ts;
    //Env.DEF_MEM.set_alias(_alias,ts.oob(TypeStruct.ISUSED));
    //xval();
    throw unimpl();
  }
  @Override public String xstr() { return "New"+"*"+_alias; } // Self short name
  @Override void walk_reset0() { assert is_prim(); _init(_reset_alias,null/*_ts*/); }

  public MrgProjNode mem() {
//    for( Node use : _uses ) if( use instanceof MrgProjNode mrg ) return mrg;
//    return null;
    throw unimpl();
  }
  public void set_nargs(int nargs) {
    //assert _nargs==0; assert _is_closure || _is_val; _nargs=nargs;
    throw unimpl();
  }

//  public int find(String name) {
//    throw unimpl();
//    //int idx = _ts.find(name); return idx==-1 ? -1 : idx+DSP_IDX;
//  }
//  public Node in(String name) { return in(find(name)); } // Error if not found
//  //  public Node in(TypeFld fld) { return in(fld._fld); } // Error if not found
//  public TypeFld get(String name) {
//    throw unimpl();
//    //return _ts.get(name);
//  }
//
////
//
  @Override public Type value() {
    //return _is_val ? _tptr.make_from(valueobj()) : _tptr;
    throw unimpl();
  }
//  // Used by MrgProj
//  TypeStruct valueobj() {
//    TypeStruct lv = _live.ld(_tptr);
//    TypeStruct ts = TypeStruct.malloc(_ts._name,_ts.above_center());
//    for( TypeFld fld : _ts ) {
//      TypeFld lvfld = lv.get(fld._fld);
//      boolean alive = !(lvfld==null ? lv : lvfld).above_center();
//      ts.add_fld(fld.make_from(alive ? in(fld)._val : Type.ANY, alive ? fld._access : Access.NoAccess));
//    }
//    return ts.hashcons_free();
//  }
//  // Liveness changes in NewNode, impacts value in NewNode and MrgProj
//  @Override public void add_flow_extra(Type old) {
//    if( old instanceof TypeMem ) { // Must be a liveness change
//      Env.GVN.add_flow(this);      // Self value changes as fields become alive
//      Env.GVN.add_flow(mem());     // MrgProj updates values (dead values are ANY)
//      Env.GVN.add_reduce(this);    // Self might drop an input
//    }
//  }
//  // Some input changed, so the struct in MrgProj changes
//  @Override public void add_flow_use_extra(Node chg) {
//    Env.GVN.add_flow(mem());
//  }
//
//  // Uses Full memory liveness, to track field liveness.
//  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }
//
//  @Override public TypeMem live() {
//    // Kept alive as prototype, until Combo resolves all Load-uses.
//    if( Env.PROTOS.containsKey(_ts._name) || _forward_ref || _is_val )
//      return TypeMem.ALLMEM;
//
//    MrgProjNode mrg=null; boolean has_ptr=false;
//    for( Node use : _uses ) {
//      if( use instanceof MrgProjNode mrg2 ) { assert mrg==null; mrg=mrg2; }
//      else has_ptr=true;            // Pointer usage
//    }
//    // No pointers, so entire thing is dead
//    if( !has_ptr ) return TypeMem.DEAD;
//    // No memory uses, so GENSYM usage only.
//    if( mrg==null ) return TypeMem.ANYMEM;
//    // Has pointers and memory uses; use memory aliveness.
//    return mrg._live;
//  }
//
//  // Only alive fields in the MrgProj escape
//  @Override public TypeMem live_use( Node def ) {
//    TypeStruct ts = _live.at(_alias);
//    if( ts==TypeStruct.ISUSED ) return TypeMem.ALIVE;
//    if( ts==TypeStruct.UNUSED ) return TypeMem.DEAD ;
//    int idx=DSP_IDX;  while( in(idx)!=def ) idx++; // Index of node
//    TypeFld fld = ts.get(idx-DSP_IDX);
//    if( fld==null )  return TypeMem.DEAD; // No such field is alive
//    return fld._t.oob(TypeMem.ALIVE);
//  }
//
//  @Override public void add_flow_def_extra(Node chg) {
//    if( chg instanceof MrgProjNode && chg._live.at(_alias)==TypeStruct.UNUSED )
//      Env.GVN.add_reduce(chg);
//  }
//
//  @Override public TV2 new_tvar(String alloc_site) {
//    TV2 old = _tvar;   // Stop recursive self-cycles
//    for( Node n : _defs )
//      if( n!=null )  n.walk_initype(); // Force tvar
//    TV2 rez = TV2.make_struct(this,alloc_site);
//    if( old !=null ) old.unify(rez,false);
//    return rez;
//  }
//
//  @Override public boolean unify( boolean test ) {
//    TV2 rec = tvar();
//    if( rec.is_err() ) return false;
//    if( len()<=1 ) return false; // Killed NewNode, makes no HM changes
//    assert rec.is_obj() && check_fields(rec);
//
//    // Unify existing fields.  Ignore extras on either side.
//    boolean progress = false;
//    for( TypeFld fld : _ts ) {
//      TV2 tvfld = rec.arg(fld._fld);
//      //if( tvfld != null ) progress |= tvfld.unify(tvar(fld._order),test);
//      //if( test && progress ) return true; // Fast cutout if testing
//      // TODO: Access input by field name
//      throw com.cliffc.aa.AA.unimpl();
//    }
//    rec.push_dep(this);
//    return progress;
//  }
//
//  // Extra fields are unified with ERR since they are not created here:
//  // error to load from a non-existing field
//  private boolean check_fields(TV2 rec) {
//    if( rec._args == null ) return true;
//    for( String id : rec._args.keySet() ) {
//      // Field is the class prototype name
//      if( id.charAt(id.length()-1)==':' && Util.eq(id,_tptr._obj._name) )
//         continue;             // This is fine
//      // Field is missing and not in error
//      if( _ts.get(id)==null && !rec.arg(id).is_err() )
//        return false;
//    }
//    return true;
//  }
//
//  @Override public Node ideal_reduce() {
//    if( _forward_ref ) return null; // Not defined yet
//    if( _is_val ) return null; // will die with no pointers as normal
//    // If either the address or memory is not looked at then the memory
//    // contents are dead.  The object might remain as a 'gensym' or 'sentinel'
//    // for identity tests.
//    if( mem()==null || _uses._len==1 ) {
//      // only memory (no pointers) or no memory (perhaps pointers)
//      if( len() <= 1 ) return null; /// Already killed
//      // KILL!
//      while( !is_dead() && len() > 1 )  pop(); // Kill all fields
//      _tptr = _tptr.make_from(_ts);
//      sets(TypeStruct.UNUSED.set_name(_ts._name));
//      xval();
//      if( is_dead() ) return this;
//      for( Node use : _uses )
//        Env.GVN.add_flow_uses(Env.GVN.add_reduce(use)); // Get FPtrs from MrgProj, and dead Ptrs into New
//      return this;
//    }
//
//    // Field-by-field kill
//    TypeStruct lv = _live.ld(_tptr);
//    boolean progress=false;
//    for( TypeFld fld : _ts ) {
//      TypeFld lvfld = lv.get(fld._fld);
//      boolean alive = !(lvfld==null ? lv : lvfld).above_center();
//      if( !alive && in(fld)!=Env.ANY )
//        { set_fld(fld.make_from(Type.ANY,Access.NoAccess),Env.ANY); progress=true; }
//    }
//    if( progress ) return this;
//
//    return null;
//  }
//
//  //@Override BitsAlias escapees() { return _tptr._aliases; }
//  //boolean is_unused() { return _ts==TypeStruct.ANYSTRUCT; }
//  //// Kill all inputs, inform all users
//  //void kill2() {
//  //  unelock();
//  //  while( !is_dead() && _defs._len > 1 )
//  //    pop();                    // Kill all fields
//  //  _ts = dead_type();
//  //  _tptr = TypeMemPtr.make(BitsAlias.make0(_alias),TypeObj.UNUSED);
//  //  //Env.GVN.revalive(this,ProjNode.proj(this,0));
//  //  xval();
//  //  if( is_dead() ) return;
//  //  for( Node use : _uses )
//  //    Env.GVN.add_flow_uses(Env.GVN.add_reduce(use)); // Get FPtrs from MrgProj, and dead Ptrs into New
//  //}
//  //
//  //// Basic escape analysis.  If no escapes and no loads this object is dead.
//  //private boolean captured( ) {
//  //  if( _uses._len==0 ) return false; // Dead or being created
//  //  Node mem = _uses.at(0);
//  //  // If only either address or memory remains, then memory contents are dead
//  //  if( _uses._len==1 )
//  //    return mem instanceof MrgProjNode; // No pointer, just dead memory
//  //  Node ptr = _uses.at(1);
//  //  if( ptr instanceof MrgProjNode ) ptr = _uses.at(0); // Get ptr not mem
//  //
//  //  // Scan for memory contents being unreachable.
//  //  // Really stupid!
//  //  for( Node use : ptr._uses )
//  //    if( !(use instanceof IfNode) )
//  //      return false;
//  //  // Only used to nil-check (always not-nil) and equality (always unequal to
//  //  // other aliases).
//  //  return true;
//  //}
//
//  // clones during inlining all become unique new sites
//  @SuppressWarnings("unchecked")
//  @Override @NotNull public NewNode copy( boolean copy_edges) {
//    // Split the original '_alias' class into 2 sub-aliases
//    NewNode nnn = (NewNode)super.copy(copy_edges);
//    nnn._init(BitsAlias.new_alias(_alias),_ts);      // Children alias classes, split from parent
//    _init(BitsAlias.new_alias(_alias),_ts); // The original NewNode also splits from the parent alias
//    Env.GVN.add_flow(this);     // Alias changes flow
//    return nnn;
//  }
//
//  // Freeing a dead alias requires an (expensive) touch of everybody holding on
//  // to a mapping for the old alias (all TypeMems), but it allows the alias to
//  // be immediately recycled.
//  void free() {
//    // TODO: premature opt?
//  }
//
//  @Override public int hashCode() { return super.hashCode()+ _alias; }
//  // Only ever equal to self, because of unique _alias.  We can collapse equal
//  // NewNodes and join alias classes, but this is not the normal CSE and so is
//  // not done by default.
//  // TODO: Allow CSE if all fields are final at construction.
//  @Override public boolean equals(Object o) {  return this==o; }
}
