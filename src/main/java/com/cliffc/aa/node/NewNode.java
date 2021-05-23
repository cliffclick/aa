package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import org.jetbrains.annotations.NotNull;

import static com.cliffc.aa.AA.*;

// Allocates a TypeObj and produces a Tuple with the TypeObj and a TypeMemPtr.
//
// NewNodes have a unique alias class - they do not alias with any other
// NewNode, even if they have the same type.  Upon cloning both NewNodes get
// new aliases that inherit (tree-like) from the original alias.

public abstract class NewNode<T extends TypeObj<T>> extends Node {
  // Unique alias class, one class per unique memory allocation site.
  // Only effectively-final, because the copy/clone sets a new alias value.
  public int _alias; // Alias class

  // A list of field names and field-mods, folded into the initial state of
  // this NewObj.  These can come from initializers at parse-time, or stores
  // folded in.  There are no types stored here; types come from the inputs.
  public T _ts;             // Base object type, representing all possible future values

  // The memory state for Env.DEFMEM, the default memory.  All non-final fields
  // are ALL; final fields keep their value.  All field flags are moved to
  // bottom, e.g. as-if all fields are now final-stored.  Will be set to
  // TypeObj.UNUSE for never-allocated (eg dead allocations)
  TypeObj _crushed;

  // Just TMP.make(_alias,OBJ)
  public TypeMemPtr _tptr;

  // News do not really need a ctrl; useful to bind the upward motion of
  // closures so variable stores can more easily fold into them.
  public NewNode( byte type, int parent_alias, T to         ) { super(type,(Node)null); _init(parent_alias,to); }
  public NewNode( byte type, int parent_alias, T to,Node fld) { super(type, null, fld); _init(parent_alias,to); }
  private void _init(int parent_alias, T ts) {
    if( _elock ) unelock();    // Unlock before changing hash
    _alias = BitsAlias.new_alias(parent_alias);
    _tptr = TypeMemPtr.make(BitsAlias.make0(_alias),TypeObj.ISUSED);
    sets(ts);
  }
  @Override public String xstr() { return "New"+"*"+_alias; } // Self short name
  String  str() { return "New"+_ts; } // Inline less-short name

  static int def_idx(int fld) { return fld+1; } // Skip ctl in slot 0
  Node fld(int fld) { return in(def_idx(fld)); } // Node for field#

  // Recompute default memory cache on a change.  Might not be monotonic,
  // e.g. during Node create, or folding a Store.
  public final void sets( T ts ) {
    _ts = ts;
    _crushed = ts.crush();
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
  // Reducing a NewNode to 'any' changes DEFMEM
  @Override public void add_reduce_extra() {
    Env.GVN.add_flow(Env.DEFMEM);
  }

  @Override public Type value(GVNGCM.Mode opt_mode) {
    return TypeTuple.make(Type.CTRL, is_unused() ? TypeObj.UNUSED : valueobj(),_tptr);   // Complex obj, simple ptr.
  }
  abstract TypeObj valueobj();

  @Override public TypeMem all_live() { return TypeMem.ALLMEM; }

  @Override public TypeMem live(GVNGCM.Mode opt_mode) {
    // Keep the MrgProj memory, filtered by alias and the pointer being alive.
    if( _keep>0 ) return TypeMem.make(_alias,_crushed);

    // If the MrgProj does not have this object alive, then we are not alive -
    // even if the pointer is alive.
    if( _uses._len<2 ) return _live;    // Dead, collapsing
    Node mem = _uses.at(0);
    if( !(mem instanceof MrgProjNode) ) mem = _uses.at(1);
    assert mem instanceof MrgProjNode;
    return mem._live;
  }

  // Only alive fields in the MrgProj escape
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) {
    TypeObj to = _live.at(_alias);
    return to.above_center() ? TypeMem.DEAD : TypeMem.ESCAPE;
  }

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
    Env.DEFMEM.set_def(_alias,Node.con(TypeObj.UNUSED));
    Env.GVN.revalive(this,ProjNode.proj(this,0),Env.DEFMEM);
    tvar().unify(TV2.DEAD,false);
    if( is_dead() ) return;
    for( Node use : _uses )
      Env.GVN.add_flow_uses(use); // Get FPtrs from MrgProj, and dead Ptrs into New
  }

  // Basic escape analysis.  If no escapes and no loads this object is dead.
  private boolean captured( ) {
    if( _keep > 0 ) return false;
    if( _uses._len==0 ) return false; // Dead or being created
    Node mem = _uses.at(0);
    // If only either address or memory remains, then memory contents are dead
    if( _uses._len==1 ) {
      if( mem instanceof MrgProjNode ) return true; // No pointer, just dead memory
      // Just a pointer; currently on Strings become memory constants and
      // constant-fold - leaving the allocation dead.
      return !(val(1) instanceof TypeStr);
    }
    Node ptr = _uses.at(1);
    if( ptr instanceof MrgProjNode ) ptr = _uses.at(0); // Get ptr not mem
    if( ptr._keep>0 ) return false;

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
    nnn._init(_alias,_ts);      // Children alias classes, split from parent
    _init(_alias,_ts); // The original NewNode also splits from the parent alias
    Env.GVN.add_flow(this);     // Alias changes flow
    return nnn;
  }

  @Override public int hashCode() { return super.hashCode()+ _alias; }
  // Only ever equal to self, because of unique _alias.  We can collapse equal
  // NewNodes and join alias classes, but this is not the normal CSE and so is
  // not done by default.
  // TODO: Allow CSE if all fields are final at construction.
  @Override public boolean equals(Object o) {  return this==o; }
  public MrgProjNode mrg() {
    Node ptr = _uses.at(0);
    if( !(ptr instanceof MrgProjNode) ) ptr = _uses.at(1);
    return (MrgProjNode)ptr;
  }
  ProjNode ptr() {
    Node ptr = _uses.at(0);
    if( ptr instanceof MrgProjNode ) ptr = _uses.at(1);
    return (ProjNode)ptr;
  }

  // --------------------------------------------------------------------------
  public static abstract class NewPrimNode<T extends TypeObj<T>> extends NewNode<T> {
    public final String _name;    // Unique library call name
    final TypeFunSig _sig;        // Arguments
    final boolean _reads;         // Reads old memory (all of these ops *make* new memory, none *write* old memory)
    final int _op_prec;
    NewPrimNode(byte op, int parent_alias, T to, String name, boolean reads, int op_prec, Type... args) {
      super(op,parent_alias,to);
      _name = name;
      _reads = reads;
      assert (reads == (args[MEM_IDX]!=TypeMem.ALLMEM)); // If reading, then memory has some requirements
      args[DSP_IDX] = Type.ALL; // No display
      _sig = TypeFunSig.make(TypeTuple.RET,TypeTuple.make_args(args));
      _op_prec = op_prec;
    }
    String bal_close() { return null; }

    private static final Ary<NewPrimNode> INTRINSICS = new Ary<>(NewPrimNode.class);
    static { reset(); }
    public static void reset() { INTRINSICS.clear(); }
    public static Ary<NewPrimNode> INTRINSICS() {
      if( INTRINSICS.isEmpty() ) {
        NewAryNode.add_libs(INTRINSICS);
        NewStrNode.add_libs(INTRINSICS);
      }
      return INTRINSICS;
    }

    // Wrap the PrimNode with a Fun/Epilog wrapper that includes memory effects.
    public FunPtrNode as_fun( GVNGCM gvn ) {
      try(GVNGCM.Build<FunPtrNode> X = gvn.new Build<>()) {
        assert in(0)==null && _uses._len==0;
        FunNode  fun = ( FunNode) X.xform(new  FunNode(this).add_def(Env.ALL_CTRL));
        ParmNode rpc = (ParmNode) X.xform(new ParmNode(0,"rpc",fun,Node.con(TypeRPC.ALL_CALL),null));
        Node memp= X.xform(new ParmNode(MEM_IDX,_sig._args[MEM_IDX],fun, TypeMem.MEM, Env.DEFMEM,null));
        fun._bal_close = bal_close();

        // Add input edges to the intrinsic
        add_def(_reads ? memp : null); // Memory  for the primitive in slot MEM_IDX
        add_def(null);                 // Closure for the primitive in slot DSP_IDX
        for( int i=ARG_IDX; i<_sig.nargs(); i++ ) // Args follow
          add_def( X.xform(new ParmNode(i,_sig._args[i],fun, Node.con(_sig.arg(i).simple_ptr()),null)));
        NewNode nnn = (NewNode)X.xform(this);
        Node mem = Env.DEFMEM.make_mem_proj(nnn,memp);
        Node ptr = X.xform(new ProjNode(nnn,REZ_IDX));
        RetNode ret = (RetNode)X.xform(new RetNode(fun,mem,ptr,rpc,fun));
        return (X._ret = new FunPtrNode(_name,ret,null));
      }
    }
  }
}
