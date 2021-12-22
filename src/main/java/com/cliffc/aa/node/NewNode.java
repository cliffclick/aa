package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;
import org.jetbrains.annotations.NotNull;

import static com.cliffc.aa.AA.MEM_IDX;
import static com.cliffc.aa.AA.unimpl;

// Allocates a TypeObj and produces a Tuple with the TypeObj and a TypeMemPtr.
//
// NewNodes have a unique alias class - they do not alias with any other
// NewNode, even if they have the same type.  Upon cloning both NewNodes get
// new aliases that inherit (tree-like) from the original alias.
//
// The inputs mirror the standard input pattern; CTL_IDX is null, MEM_IDX is
// null, DSP_IDX is the display, and the fields follow.

public abstract class NewNode<T extends TypeObj<T>> extends Node {
  // Unique alias class, one class per unique memory allocation site.
  // Only effectively-final, because the copy/clone sets a new alias value.
  public int _alias, _reset_alias; // Alias class

  // A list of field names and field-mods, folded into the initial state of
  // this NewObj.  These can come from initializers at parse-time, or stores
  // folded in.  There are no types stored here; types come from the inputs.
  public T _ts;             // Base object type, representing all possible future values

  // The memory state for Env.DEFMEM, the default memory.  All non-final fields
  // are ALL; final fields keep their value.  All field flags are moved to
  // bottom, e.g. as-if all fields are now final-stored.  Will be set to
  // TypeObj.UNUSED for never-allocated (e.g. dead allocations)
  TypeObj _crushed;

  // Just TMP.make(_alias,OBJ)
  public TypeMemPtr _tptr;

  // News do not really need a ctrl; useful to bind the upward motion of
  // closures so variable stores can more easily fold into them.

  // Takes a parent alias, and splits a child out from it.
  public NewNode( byte type, int par_alias, T to         ) { super(type,null,null); _init(BitsAlias.new_alias(par_alias),to); }
  // Takes a alias and a field and uses them directly
  public NewNode( byte type, int     alias, T to,Node fld) { super(type, null, null, fld); _init( alias, to); }
  private void _init(int alias, T ts) {
    if( _elock ) unelock();    // Unlock before changing hash
    _alias = alias;
    _tptr = TypeMemPtr.make(BitsAlias.make0(alias),TypeObj.ISUSED);
    sets(ts);
  }
  @Override public String xstr() { return "New"+"*"+_alias; } // Self short name
  String  str() { return "New"+_ts; } // Inline less-short name
  @Override void record_for_reset() { _reset_alias=_alias; }
  void reset() { assert is_prim(); _init(_reset_alias,_ts); }

  public MrgProjNode mem() {
    if( _uses._len < 1 ) return null;
    if( _uses.at(0) instanceof MrgProjNode ) return (MrgProjNode)_uses.at(0);
    if( _uses._len < 2 ) return null;
    if( _uses.at(1) instanceof MrgProjNode ) return (MrgProjNode)_uses.at(1);
    return null;
  }

  // Recompute default memory cache on a change.  Might not be monotonic,
  // e.g. during Node create, or folding a Store.
  public final void sets( T ts ) {
    _ts = ts;
    _crushed = ts.crush();
    _tptr = _tptr.make_from((TypeObj)TypeObj.ISUSED.set_name(ts._name));
  }
  // Recompute default memory, expecting it to monotonically lift.
  public final void setsm( T ts ) { assert ts.isa(_ts); sets(ts); }

  @Override public Node ideal_reduce() {
    // If either the address or memory is not looked at then the memory
    // contents are dead.  The object might remain as a 'gensym' or 'sentinel'
    // for identity tests.
    if( _defs._len > 1 && captured() ) { kill2(); return this; }
    return null;
  }

  @Override public void add_flow_def_extra(Node chg) {
    if( chg instanceof MrgProjNode && chg._live.at(_alias)==TypeObj.UNUSED )
      Env.GVN.add_reduce(chg);
  }

  @Override public Type value() {
    Type t0 = Type.CTRL;
    Type t1 = is_unused() ? TypeObj.UNUSED : valueobj();
    Type t2 = _tptr;
    // Look for a hit with the existing value, cheaper than making and discovering the dup
    TypeTuple tt;
    if( _val instanceof TypeTuple ) {
      Type[] ts = ((TypeTuple)_val)._ts;
      if( !((TypeTuple)_val).above_center() && ts[0]==t0 && ts[1]==t1 && ts[2]==t2 )
        return _val;
    }
    return TypeTuple.make(t0, t1, t2);   // Complex obj, simple ptr.
  }
  abstract TypeObj valueobj();

  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }

  // Only alive fields in the MrgProj escape
  @Override public TypeMem live_use(Node def ) {
    return _live.at(_alias).oob(TypeMem.ALIVE);
  }

  abstract public TV2 new_tvar(String alloc_site);

  @Override BitsAlias escapees() { return _tptr._aliases; }
  abstract T dead_type();
  boolean is_unused() { return _ts==dead_type(); }
  // Kill all inputs, inform all users
  void kill2() {
    unelock();
    while( !is_dead() && _defs._len > 1 )
      pop();                    // Kill all fields except memory
    _crushed = _ts = dead_type();
    _tptr = TypeMemPtr.make(BitsAlias.make0(_alias),TypeObj.UNUSED);
    Env.GVN.revalive(this,ProjNode.proj(this,0));
    if( is_dead() ) return;
    for( Node use : _uses )
      Env.GVN.add_flow_uses(Env.GVN.add_reduce(use)); // Get FPtrs from MrgProj, and dead Ptrs into New
  }

  // Basic escape analysis.  If no escapes and no loads this object is dead.
  private boolean captured( ) {
    if( _uses._len==0 ) return false; // Dead or being created
    Node mem = _uses.at(0);
    // If only either address or memory remains, then memory contents are dead
    if( _uses._len==1 )
      return mem instanceof MrgProjNode; // No pointer, just dead memory
    Node ptr = _uses.at(1);
    if( ptr instanceof MrgProjNode ) ptr = _uses.at(0); // Get ptr not mem

    // Scan for memory contents being unreachable.
    // Really stupid!
    for( Node use : ptr._uses )
      if( !(use instanceof IfNode) )
        return false;
    // Only used to nil-check (always not-nil) and equality (always unequal to
    // other aliases).
    return true;
  }

  // clones during inlining all become unique new sites
  @SuppressWarnings("unchecked")
  @Override @NotNull public NewNode copy( boolean copy_edges) {
    // Split the original '_alias' class into 2 sub-aliases
    NewNode<T> nnn = (NewNode<T>)super.copy(copy_edges);
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

  // --------------------------------------------------------------------------
  public static abstract class NewPrimNode<T extends TypeObj<T>> extends NewNode<T> {
    public final String _name;    // Unique library call name
    final TypeStruct _formals;    // Arguments
    final TypeFunPtr _tfp;        // Fidx, nargs, return
    final boolean _reads;         // Reads old memory (all of these ops *make* new memory, none *write* old memory)
    final int _op_prec;
    NewPrimNode(byte op, int parent_alias, T to, String name, boolean reads, Type ret, int op_prec, TypeFld... args) {
      super(op,parent_alias,to);
      _name = name;
      _reads = reads;
      _formals = TypeStruct.make(args);
      int fidx = BitsFun.new_fidx();
      _tfp=TypeFunPtr.make(BitsFun.make0(fidx),_formals.nargs(),TypeMemPtr.NO_DISP,ret);
      _op_prec = op_prec;
    }
    String bal_close() { return null; }

    // Wrap the PrimNode with a Fun/Epilog wrapper that includes memory effects.
    @Override public FunPtrNode clazz_node( ) {
      try(GVNGCM.Build<FunPtrNode> X = Env.GVN.new Build<>()) {
        assert in(0)==null && _uses._len==0;
        FunNode  fun = ( FunNode) X.xform(new  FunNode(_name,this));
        fun._java_fun = true;
        ParmNode rpc = (ParmNode) X.xform(new ParmNode(TypeRPC.ALL_CALL,null,fun,0,"rpc"));
        Node memp= X.xform(new ParmNode(TypeMem.MEM,null,fun,MEM_IDX," mem"));
        fun._bal_close = bal_close();

        // Add input edges to the intrinsic
        if( _reads ) set_def(MEM_IDX, memp); // Memory is already null by default
        while( len() < _formals.nargs() ) add_def(null);
        for( TypeFld arg : _formals.flds() ) {
          if( arg._order==MEM_IDX ) continue; // Already handled MEM_IDX
          set_def(arg._order,X.xform(new ParmNode(arg._t.simple_ptr(), null, fun, arg._order, arg._fld)));
        }
        //NewNode nnn = (NewNode)X.xform(this);
        //Node mem = Env.DEFMEM.make_mem_proj(nnn,memp);
        //Node ptr = X.xform(new ProjNode(nnn,REZ_IDX));
        //RetNode ret = (RetNode)X.xform(new RetNode(fun,mem,ptr,rpc,fun));
        //return (X._ret = (FunPtrNode)X.xform(new FunPtrNode(_name,ret)));
        throw unimpl();
      }
    }
  }
}
