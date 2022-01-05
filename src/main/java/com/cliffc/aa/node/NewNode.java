package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;
import org.jetbrains.annotations.NotNull;

import java.util.Arrays;

import static com.cliffc.aa.AA.DSP_IDX;
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
  public final boolean _is_closure; // For error messages
  public       boolean _is_val;     // Value type (no memory)
  public       Parse[] _fld_starts; // Start of each tuple member; 0 for the display

  // Unique alias class, one class per unique memory allocation site.
  // Only effectively-final, because the copy/clone sets a new alias value.
  public int _alias, _reset_alias; // Alias class

  // For closures, the number of fields which are initial incoming arguments
  // (Lambda args) vs local assignments (Let bound args).  Effectively final
  // AFTER all the args are added.
  public int _nargs;

  // A list of field names and field-mods, folded into the initial state of
  // this New.  These can come from initializers at parse-time, or stores
  // folded in.  There are no types stored here; types come from the inputs.
  public TypeStruct _ts; // Base object type, representing all possible future values

  // Just TMP.make(_alias,ISUSED)
  public TypeMemPtr _tptr;
  // Prototype name (with the ':') or null
  public final String _tname;

  // Still adding fields or not.
  private boolean _closed;

  // True if forward-ref
  private boolean _forward_ref;

  // Takes an alias only
  public NewNode( boolean closure, boolean is_val, boolean forward_ref, String tname, int alias ) {
    super(OP_NEW, null, null);
    assert !closure || tname==null;
    _is_closure = closure;
    _is_val = is_val;
    _forward_ref = forward_ref;
    _tname=tname;
    _init( alias, TypeStruct.EMPTY);
  }

  private void _init(int alias, TypeStruct ts) {
    if( _elock ) unelock();    // Unlock before changing hash
    _alias = alias;
    assert ts._name.isEmpty() || Util.eq(ts._name,_tname);
    if( ts._name.isEmpty() && _tname!=null ) ts = ts.set_name(_tname);
    _ts = ts;
    TypeStruct flat = TypeStruct.ISUSED;
    if( _tname!=null ) flat = flat.set_name(_tname);
    _tptr = TypeMemPtr.make(BitsAlias.make0(alias),flat);
  }
  @Override public String xstr() { return "New"+"*"+_alias; } // Self short name
  String  str() { return "New"+_ts; } // Inline less-short name
  @Override void record_for_reset() { _reset_alias=_alias; }
  void reset() { assert is_prim(); _init(_reset_alias,_ts); }
  @Override public boolean is_forward_type() { return _forward_ref; }
  public void define() { assert _forward_ref && _closed; _forward_ref=false; }
  public boolean is_closed() { return _closed; }
  public NewNode close() { assert !_closed; _closed=true; return this; }
  // Strip the ':' off to make a value name from a type name.
  // Error if not a named NewNode.
  public String as_valname() { return _tname.substring(0,_tname.length()-1).intern(); }

  public MrgProjNode mem() {
    for( Node use : _uses ) if( use instanceof MrgProjNode mrg ) return mrg;
    return null;
  }
  public void set_nargs() { assert _nargs==0; _nargs=len(); }

  public int find(String name) { int idx = _ts.find(name); return idx==-1 ? -1 : idx+DSP_IDX; }
  public Node get(String name) { return in(find(name)); } // Error if not found
  public TypeFld fld(String name) { return _ts.get(name); }

  // True if field exists
  public boolean exists(String name) { return _ts.find(name)!=-1; }
  public void add_fld( TypeFld fld, Node val, Parse badt ) {
    assert !Util.eq(fld._fld,TypeFld.fldBot);
    assert !_closed;
    assert _ts.len()+DSP_IDX==len();
    if( _fld_starts==null ) _fld_starts = new Parse[1];
    while( _fld_starts.length <= _ts.len() ) _fld_starts = Arrays.copyOf(_fld_starts,_fld_starts.length<<1);
    _fld_starts[_ts.len()]=badt;
    _ts = _ts.add_fldx(fld);     // Will also assert no-dup field names
    add_def(val);
    xval(); // Eagerly update the type
    Env.GVN.add_flow(this);
    Env.GVN.add_flow_uses(this);
  }

  // Add a named FunPtr to a New.  Auto-inflates to a Unresolved as needed.
  public void add_fun( Parse bad, String name, ValFunNode ptr ) {
    assert !_closed;
    TypeFld fld = _ts.get(name);
    Node n = in(fld._order);
    UnresolvedNode unr = n instanceof UnresolvedNode
      ? (UnresolvedNode)n
      : new UnresolvedNode(name,bad).scoped();
    unr.add_fun(ptr);           // Checks all formals are unambiguous
    set_fld(fld.make_from(fld._t,TypeFld.Access.Final),unr);
  }

  public void set_fld( TypeFld fld, Node n ) {
    _ts = _ts.replace_fld(fld);
    set_def(fld._order,n);
    Env.GVN.add_flow(mem());
  }
  public void pop_fld() { throw unimpl(); }

  // The current local scope ends, no more names will appear.  Forward refs
  // first found in this scope are assumed to be defined in some outer scope
  // and get promoted.  Other locals are no longer kept alive, but live or die
  // according to use.
  public void promote_forward( NewNode parent ) {
    assert parent != null;
    for( TypeFld fld : _ts ) {
      Node n = in(fld._order);
      if( n.is_forward_ref() ) {
        // Is this Unresolved defined in this scope, or some outer scope?
        if( ((UnresolvedNode)n).is_scoped() ) {
          // Definitely defined here, and all stores are complete; all fcns added
          ((UnresolvedNode)n).define();
          Env.GVN.add_unuse(n);
        } else {
          // Make field in the parent
          parent.add_fld(TypeFld.make(fld._fld,fld._t,parent.len()), n, null /*TODO: Copy forward the error*/);
          // Stomp field locally to ANY
          set_fld(fld.make_from(Type.ANY, TypeFld.Access.Final),Env.ANY);
          Env.GVN.add_flow_uses(this);
        }
      }
    }
  }


  @Override public Type value() { return _is_val ? _tptr.make_from(valueobj()) : _tptr; }
  // Used by MrgProj
  TypeStruct valueobj() { return _ts.make_from(this::val); }

  // Some input changed, so the struct in MrgProj changes
  @Override public void add_flow_use_extra(Node chg) {
    Env.GVN.add_flow(mem());
  }

  // Uses Full memory liveness, to track field liveness.
  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }

  @Override public TypeMem live() {
    // Kept alive as prototype, until Combo resolves all Load-uses.
    if( Env.PROTOS.containsKey(_ts._name) || _forward_ref || _is_val )
      return TypeMem.ALLMEM;

    MrgProjNode mrg=null; boolean has_ptr=false;
    for( Node use : _uses ) {
      if( use instanceof MrgProjNode mrg2 ) { assert mrg==null; mrg=mrg2; }
      else has_ptr=true;            // Pointer usage
    }
    // No pointers, so entire thing is dead
    if( !has_ptr ) return TypeMem.DEAD;
    // No memory uses, so GENSYM usage only.
    if( mrg==null ) return TypeMem.ANYMEM;
    // Has pointers and memory uses; use memory aliveness.
    return mrg._live;
  }

  // Only alive fields in the MrgProj escape
  @Override public TypeMem live_use(Node def ) {
    TypeStruct ts = _live.at(_alias);
    if( ts==TypeStruct.ISUSED ) return TypeMem.ALIVE;
    if( ts==TypeStruct.UNUSED ) return TypeMem.DEAD ;
    int idx=DSP_IDX;  while( in(idx)!=def ) idx++; // Index of node
    TypeFld fld = ts.fld_idx(idx-DSP_IDX);
    if( fld==null )  return TypeMem.DEAD; // No such field is alive
    return fld._t.oob(TypeMem.ALIVE);
  }

  @Override public void add_flow_def_extra(Node chg) {
    if( chg instanceof MrgProjNode && chg._live.at(_alias)==TypeStruct.UNUSED )
      Env.GVN.add_reduce(chg);
  }

  @Override public TV2 new_tvar(String alloc_site) {
    for( Node n : _defs )
      if( n!=null )  n.walk_initype(); // Force tvar
    return TV2.make_struct(this,alloc_site);
  }

  @Override public boolean unify( boolean test ) {
    TV2 rec = tvar();
    if( rec.is_err() ) return false;
    assert rec.is_obj() && check_fields(rec);

    // Unify existing fields.  Ignore extras on either side.
    boolean progress = false;
    for( TypeFld fld : _ts ) {
      TV2 tvfld = rec.arg(fld._fld);
      if( tvfld != null ) progress |= tvfld.unify(tvar(fld._order),test);
      if( test && progress ) return true; // Fast cutout if testing
    }
    rec.push_dep(this);
    return progress;
  }

  // Extra fields are unified with ERR since they are not created here:
  // error to load from a non-existing field
  private boolean check_fields(TV2 rec) {
    if( rec._args == null ) return true;
    for( String id : rec._args.keySet() ) {
      // Field is the class prototype name
      if( id.charAt(id.length()-1)==':' && Util.eq(id,_tptr._obj._name) )
         continue;             // This is fine
      // Field is missing and not in error
      if( _ts.get(id)==null && !rec.arg(id).is_err() )
        return false;
    }
    return true;
  }

  @Override public Node ideal_reduce() {
    if( _forward_ref ) return null; // Not defined yet
    if( _is_val ) return null; // will die with no pointers as normal
    // If either the address or memory is not looked at then the memory
    // contents are dead.  The object might remain as a 'gensym' or 'sentinel'
    // for identity tests.
    if( mem()==null || _uses._len==1 ) {
      // only memory (no pointers) or no memory (perhaps pointers)
      if( len() <= 1 ) return null; /// Already killed
      // KILL!
      while( !is_dead() && len() > 1 )  pop(); // Kill all fields
      _ts = TypeStruct.UNUSED.set_name(_ts._name);
      _tptr = _tptr.make_from(_ts);
      xval();
      if( is_dead() ) return this;
      for( Node use : _uses )
        Env.GVN.add_flow_uses(Env.GVN.add_reduce(use)); // Get FPtrs from MrgProj, and dead Ptrs into New
      return this;
    }
    return null;
  }

  //@Override BitsAlias escapees() { return _tptr._aliases; }
  //boolean is_unused() { return _ts==TypeStruct.ANYSTRUCT; }
  //// Kill all inputs, inform all users
  //void kill2() {
  //  unelock();
  //  while( !is_dead() && _defs._len > 1 )
  //    pop();                    // Kill all fields
  //  _ts = dead_type();
  //  _tptr = TypeMemPtr.make(BitsAlias.make0(_alias),TypeObj.UNUSED);
  //  //Env.GVN.revalive(this,ProjNode.proj(this,0));
  //  xval();
  //  if( is_dead() ) return;
  //  for( Node use : _uses )
  //    Env.GVN.add_flow_uses(Env.GVN.add_reduce(use)); // Get FPtrs from MrgProj, and dead Ptrs into New
  //}
  //
  //// Basic escape analysis.  If no escapes and no loads this object is dead.
  //private boolean captured( ) {
  //  if( _uses._len==0 ) return false; // Dead or being created
  //  Node mem = _uses.at(0);
  //  // If only either address or memory remains, then memory contents are dead
  //  if( _uses._len==1 )
  //    return mem instanceof MrgProjNode; // No pointer, just dead memory
  //  Node ptr = _uses.at(1);
  //  if( ptr instanceof MrgProjNode ) ptr = _uses.at(0); // Get ptr not mem
  //
  //  // Scan for memory contents being unreachable.
  //  // Really stupid!
  //  for( Node use : ptr._uses )
  //    if( !(use instanceof IfNode) )
  //      return false;
  //  // Only used to nil-check (always not-nil) and equality (always unequal to
  //  // other aliases).
  //  return true;
  //}

  // clones during inlining all become unique new sites
  @SuppressWarnings("unchecked")
  @Override @NotNull public NewNode copy( boolean copy_edges) {
    // Split the original '_alias' class into 2 sub-aliases
    NewNode nnn = (NewNode)super.copy(copy_edges);
    nnn._init(Env.new_alias(_alias),_ts);      // Children alias classes, split from parent
    _init(Env.new_alias(_alias),_ts); // The original NewNode also splits from the parent alias
    Env.GVN.add_flow(this);     // Alias changes flow
    return nnn;
  }

  // Freeing a dead alias requires an (expensive) touch of everybody holding on
  // to a mapping for the old alias (all TypeMems), but it allows the alias to
  // be immediately recycled.
  void free() {
    // TODO: premature opt?
  }

  @Override public int hashCode() { return super.hashCode()+ _alias; }
  // Only ever equal to self, because of unique _alias.  We can collapse equal
  // NewNodes and join alias classes, but this is not the normal CSE and so is
  // not done by default.
  // TODO: Allow CSE if all fields are final at construction.
  @Override public boolean equals(Object o) {  return this==o; }
}
