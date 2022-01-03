package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;
import org.jetbrains.annotations.NotNull;

import static com.cliffc.aa.type.TypeFld.Access;
import static com.cliffc.aa.AA.*;

// Allocates a TypeStruct
//
// NewNodes have a unique alias class - they do not alias with any other
// NewNode, even if they have the same type.  Upon cloning both NewNodes get
// new aliases that inherit (tree-like) from the original alias.
//
// The inputs mirror the standard input pattern; CTL_IDX is null, MEM_IDX is
// null, DSP_IDX is the display field, and the other fields follow.

public class NewNode extends Node {
  public final boolean _is_closure; // For error messages
  public       Parse[] _fld_starts; // Start of each tuple member; 0 for the display
  
  // Unique alias class, one class per unique memory allocation site.
  // Only effectively-final, because the copy/clone sets a new alias value.
  public int _alias, _reset_alias; // Alias class

  // For closures, the number of fields which are initial incoming arguments
  // (Lambda args) vs local assignments (Let bound args).  Effectively final
  // AFTER all the args are added.
  public int _nargs;
  
  // A list of field names and field-mods, folded into the initial state of
  // this NewObj.  These can come from initializers at parse-time, or stores
  // folded in.  There are no types stored here; types come from the inputs.
  public TypeStruct _ts; // Base object type, representing all possible future values

  // Just TMP.make(_alias,OBJ)
  public TypeMemPtr _tptr;

  // Still adding fields or not
  private boolean _closed;
  
  
  // Takes an alias only
  public NewNode( boolean closure, int alias ) {
    super(OP_NEW, null, null);
    _is_closure = closure;
    _init( alias, TypeStruct.EMPTY);
  }
  
  private void _init(int alias, TypeStruct ts) {
    if( _elock ) unelock();    // Unlock before changing hash
    _alias = alias;
    _ts = ts;
    _tptr = TypeMemPtr.make(BitsAlias.make0(alias),TypeStruct.ISUSED);
  }
  @Override public String xstr() { return "New"+"*"+_alias; } // Self short name
  String  str() { return "New"+_ts; } // Inline less-short name
  @Override void record_for_reset() { _reset_alias=_alias; }
  void reset() { assert is_prim(); _init(_reset_alias,_ts); }

  public MrgProjNode mem() { throw unimpl(); }
  public void set_nargs() { throw unimpl(); }
  public void set_type_name(String name) {
    assert _ts._name=="";
    _ts = _ts.set_name(name);
    _tptr = TypeMemPtr.make(_tptr._aliases,TypeStruct.ISUSED.set_name(name));
  }
  public int find(String name) { int idx = _ts.find(name); return idx==-1 ? -1 : idx+DSP_IDX; }
  public Node get(String name) { return in(find(name)); } // Error if not found
  public TypeFld fld(String name) { return _ts.get(name); }

  // True if field exists
  public boolean exists(String name) { return _ts.find(name)!=-1; }
  public void add_fld( TypeFld fld, Node val, Parse badt ) {
    assert !Util.eq(fld._fld,TypeFld.fldBot);
    assert !_closed;
    _ts = _ts.add_fld(fld);     // Will also assert no-dup field names
    //_tptr = _tptr.make_from(TypeStruct.ISUSED.set_name(ts._name));
    // _fld_starts[idx]=badt; // TODO: Save badt and report it if fields do not type
    //add_def(val);
    //Env.GVN.add_flow(this);    
    throw unimpl();
  }

  // Add a named FunPtr to a New.  Auto-inflates to a Unresolved as needed.
  public void add_fun( Parse bad, String name, ValFunNode ptr ) {
    TypeFld fld = _ts.get(name);
    assert fld._t instanceof TypeFunPtr; // TODO: not sure when this gets set
    Node n = in(fld._order);
    UnresolvedNode unr = n==Env.XNIL
      ? new UnresolvedNode(name,bad).scoped()
      : (UnresolvedNode)n;
    unr.add_fun(ptr);           // Checks all formals are unambiguous
    set_fld(fld,unr);
  }
  
  public void set_fld( TypeFld fld, Node n ) {
    assert !_closed;
    throw unimpl();
  }
  public void pop_fld() { throw unimpl(); }
  
  public void close() { assert !_closed; _closed=true; }

    // The current local scope ends, no more names will appear.  Forward refs
  // first found in this scope are assumed to be defined in some outer scope
  // and get promoted.  Other locals are no longer kept alive, but live or die
  // according to use.
  public void promote_forward( NewNode parent ) {
    assert parent != null;
    for( TypeFld fld : _ts ) {
      //Node n = in(fld._order);
      //if( n.is_forward_ref() ) {
      //  // Is this Unresolved defined in this scope, or some outer scope?
      //  if( ((UnresolvedNode)n).is_scoped() ) {
      //    // Definitely defined here, and all stores are complete; all fcns added
      //    ((UnresolvedNode)n).define();
      //    Env.GVN.add_unuse(n);
      //  } else {
      //    // Make field in the parent
      //    parent.create(fld._fld,n,fld._access,fld._t,null/*TODO: Copy forward the error*/);
      //    // Stomp field locally to ANY
      //    set_def(fld._order,Env.ANY);
      //    setsm(_ts.replace_fld(fld.make_from(Type.ANY,Access.Final)));
      //    Env.GVN.add_flow_uses(n);
      //  }
      //}
      throw unimpl();
    }
  }

  @Override public Node ideal_reduce() {
    //// If either the address or memory is not looked at then the memory
    //// contents are dead.  The object might remain as a 'gensym' or 'sentinel'
    //// for identity tests.
    //if( _defs._len > 1 && captured() ) { kill2(); return this; }
    //return null;
    // Simpler capture notion
    throw unimpl();
  }

  @Override public void add_flow_def_extra(Node chg) {
    if( chg instanceof MrgProjNode && chg._live.at(_alias)==TypeStruct.UNUSED )
      Env.GVN.add_reduce(chg);
  }


  @Override public Type value() {
    //return _tptr;
    // TODO: MrgProj has to compute struct type, has the neighbor problem.
    // TODO: dead NewNodes can kill all fields, have _tptr goto TMP of UNUSED
    throw unimpl();
  }

  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }

  // kept alive as prototype, until Combo resolves all Load-uses.
  @Override public TypeMem live() {
    if( Env.PROTOS.containsKey(_ts._name) )
      return TypeMem.ALLMEM;
    return super.live();
  }

  // Only alive fields in the MrgProj escape
  @Override public TypeMem live_use(Node def ) {
    //TypeObj to = _live.at(_alias);
    //if( !(to instanceof TypeStruct) ) return to.oob(TypeMem.ALIVE);
    //int idx=0;  while( in(idx)!=def ) idx++; // Index of node
    //TypeFld fld = ((TypeStruct)to).fld_idx(idx);
    //if( fld==null ) return TypeMem.DEAD; // No such field is alive
    //Type t = fld._t;
    //return t.oob(TypeMem.ALIVE);
    throw unimpl();
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
    //if( rec._args != null )
    //  for( String id : rec._args.keySet() ) {
    //    // Field is the class prototype name
    //    if( id.charAt(id.length()-1)==':' && Util.eq(id,_tptr._obj._name) )
    //      continue;             // This is fine
    //    // Field is missing and not in error
    //    if( _ts.get(id)==null && !rec.arg(id).is_err() )
    //      return false;
    //  }
    //return true;
    throw unimpl();
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
    nnn._init(BitsAlias.new_alias(_alias),_ts);      // Children alias classes, split from parent
    _init(BitsAlias.new_alias(_alias),_ts); // The original NewNode also splits from the parent alias
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
