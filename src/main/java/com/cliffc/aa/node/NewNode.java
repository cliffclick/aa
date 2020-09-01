package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import org.jetbrains.annotations.NotNull;

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

  // NewNodes do not really need a ctrl; useful to bind the upward motion of
  // closures so variable stores can more easily fold into them.
  public NewNode( byte type, int parent_alias, T to         ) { super(type,(Node)null); _init(parent_alias,to); }
  public NewNode( byte type, int parent_alias, T to,Node fld) { super(type,  null,fld); _init(parent_alias,to); }
  private void _init(int parent_alias, T ts) {
    _alias = BitsAlias.new_alias(parent_alias);
    _tptr = TypeMemPtr.make(BitsAlias.make0(_alias),TypeObj.ISUSED);
    _ts = ts;
    _crushed = ts.crush();
  }
  String xstr() { return "New"+"*"+_alias; } // Self short name
  String  str() { return "New"+_ts; } // Inline less-short name

  static int def_idx(int fld) { return fld+1; } // Skip ctl in slot 0
  Node fld(int fld) { return in(def_idx(fld)); } // Node for field#

  // Recompute default memory cache on a change
  public final void sets_out( T ts ) {
    assert !touched();
    _ts = ts;
    _crushed = ts.crush();
  }
  protected final void sets_in( T ts ) {
    assert touched();
    _ts = ts;
    _crushed = ts.crush();
    Env.GVN.revalive(this,ProjNode.proj(this,0),Env.DEFMEM);
  }

  @Override public Node ideal(GVNGCM gvn, int level) {
    // If either the address or memory is not looked at then the memory
    // contents are dead.  The object might remain as a 'gensym' or 'sentinel'
    // for identity tests.
    if( _defs._len > 1 && captured(gvn) ) return kill(gvn);
    return null;
  }

  @Override public Type value(GVNGCM.Mode opt_mode) {
    return TypeTuple.make(is_unused() ? TypeObj.UNUSED : valueobj(),_tptr);   // Complex obj, simple ptr.
  }
  abstract TypeObj valueobj();

  @Override BitsAlias escapees() { return _tptr._aliases; }
  abstract T dead_type();
  boolean is_unused() { return _ts==dead_type(); }
  // Kill all inputs, inform all users
  NewNode kill(GVNGCM gvn) {
    while( !is_dead() && _defs._len > 1 )
      pop(gvn);               // Kill all fields except memory
    if( is_dead() ) return this;
    _crushed = _ts = dead_type();
    Env.GVN.revalive(this,ProjNode.proj(this,0),Env.DEFMEM);
    gvn.set_def_reg(Env.DEFMEM,_alias,gvn.add_work(gvn.con(TypeObj.UNUSED)));
    if( is_dead() ) return this;
    for( Node use : _uses )
      gvn.add_work_uses(use); // Get FPtrs from MrgProj, and dead Ptrs into New
    return this;
  }

  // Basic escape analysis.  If no escapes and no loads this object is dead.
  private boolean captured( GVNGCM gvn ) {
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

    // Scan for memory contents being unreachable.
    // Really stupid!
    for( Node use : ptr._uses )
      if( !(use instanceof IfNode) )
        return false;
    // Only used to nil-check (always not-nil) and equality (always unequal to
    // other aliases).
    return true;
  }

  boolean escaped(GVNGCM gvn) {
    if( gvn._opt_mode==GVNGCM.Mode.Parse ) return true; // Assume escaped in parser
    if( _uses._len!=2 ) return false; // Dying/dead, not escaped
    Node ptr = _uses.at(0);
    if( ptr instanceof MrgProjNode ) ptr = _uses.at(1); // Get ptr not mem
    return ptr._live==TypeMem.ESCAPE || ptr._live==TypeMem.LIVE_BOT;
  }

  // clones during inlining all become unique new sites
  @SuppressWarnings("unchecked")
  @Override @NotNull public NewNode copy( boolean copy_edges, GVNGCM gvn) {
    // Split the original '_alias' class into 2 sub-aliases
    NewNode<T> nnn = (NewNode<T>)super.copy(copy_edges, gvn);
    nnn._init(_alias,_ts);      // Children alias classes, split from parent
    // The original NewNode also splits from the parent alias
    assert touched();
    Type oldt = gvn.unreg(this);
    _init(_alias,_ts);
    gvn.rereg(this,oldt);
    return nnn;
  }

  @Override public int hashCode() { return super.hashCode()+ _alias; }
  // Only ever equal to self, because of unique _alias.  We can collapse equal
  // NewNodes and join alias classes, but this is not the normal CSE and so is
  // not done by default.
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
    NewPrimNode(byte op, int parent_alias, T to, String name, boolean reads, Type... args) {
      super(op,parent_alias,to);
      _name = name;
      _reads = reads;
      args[0] = TypeFunPtr.NO_DISP; // No display
      String[] flds = args.length==1 ? TypeStruct.ARGS_ :  (args.length==2 ? TypeStruct.ARGS_X : TypeStruct.ARGS_XY);
      _sig = TypeFunSig.make(TypeStruct.make_args(flds,args),Type.SCALAR);
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
      FunNode  fun = ( FunNode) gvn.xform(new  FunNode(this).add_def(Env.ALL_CTRL));
      ParmNode rpc = (ParmNode) gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL),null));
      Node memp= gvn.xform(new ParmNode(-2,"mem",fun,TypeMem.MEM,Env.DEFMEM,null));
      gvn.add_work(memp);         // This may refine more later
      fun._bal_close = bal_close();

      // Add input edges to the intrinsic
      add_def(_reads ? memp : null); // Memory  for the primitive in slot 1
      add_def(null);                 // Closure for the primitive in slot 2
      for( int i=1; i<_sig.nargs(); i++ ) // Args follow, closure in formal 0
        add_def( gvn.xform(new ParmNode(i,_sig.fld(i),fun, gvn.con(_sig.arg(i).simple_ptr()),null)));
      NewNode nnn = (NewNode)gvn.xform(this);
      Node mem = Env.DEFMEM.make_mem_proj(gvn,nnn,memp);
      Node ptr = gvn.xform(new ProjNode(1, nnn));
      RetNode ret = (RetNode)gvn.xform(new RetNode(fun,mem,ptr,rpc,fun));
      mem.xliv(gvn._opt_mode); // Refine initial memory
      return new FunPtrNode(ret,gvn.con(TypeFunPtr.NO_DISP));
    }
  }
}
