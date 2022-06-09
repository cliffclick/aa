package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.type.*;
import com.cliffc.aa.tvar.TV2;

import static com.cliffc.aa.AA.*;

// Allocates memory for the input
//
// NewNodes have a unique alias class - they do not alias with any other
// NewNode, even if they have the same type.  Upon cloning both NewNodes get
// new aliases that inherit (tree-like) from the original alias.
//
// Takes in a Control (often null), a Memory, and a TypeStruct producer (ala StructNode).
// Produces a Tuple of (TypeMem,TypeMemPtr).
public class NewNode extends Node {
  // Unique alias class, one class per unique memory allocation site.
  // Only effectively-final, because the copy/clone sets a new alias value.
  public int _alias; // Alias class
  public final int _reset_alias;

  // Just TMP.make(_alias,ISUSED)
  public TypeMemPtr _tptr;

  public NewNode( int alias, Node mem, Node ts ) {
    super(OP_NEW, null, mem, ts);
    _reset_alias = alias;       // Allow a reset, if this alias splits and then we want to run a new test
    set_alias( alias);
  }
  public NewNode( Node mem, Node ts ) { this(BitsAlias.new_alias(),mem,ts); }

  private void set_alias(int alias) {
    if( _elock ) unelock();    // Unlock before changing hash
    _alias = alias;
    _tptr = TypeMemPtr.make(alias,TypeStruct.ISUSED);
  }
  @Override public String xstr() { return "New"+"*"+_alias; } // Self short name
  @Override void walk_reset0() { assert is_prim(); set_alias(_reset_alias); }

  public Node ctl() { return in(CTL_IDX); }
  public Node mem() { return in(MEM_IDX); }
  public StructNode rec() { return (StructNode)in(REZ_IDX); }
  
  @Override public Type value() { return TypeTuple.make(Type.CTRL,memval(),_tptr); }
  // Construct the memory value
  private TypeMem memval() {
    Type tm = mem()._val;
    Type t  = rec()._val;
    if( !(tm instanceof TypeMem tmem ) ) return tm.oob(TypeMem.ALLMEM);
    if( !(t  instanceof TypeStruct ts) ) return t .oob(TypeMem.ALLMEM);
    return tmem.make_from(_alias,ts);
  }

 
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

  // The MProj liveness is always passed along, if it exists.  The self alias
  // is not excluded, because if recursion then the self alias can be alive
  // recursively.
  @Override public Type live() {
    ProjNode mem = ProjNode.proj(this,MEM_IDX);
    return mem==null ? Type.ANY : mem._live;
  }

  // Memory is full alive, include this alias in case of recursion.
  @Override public Type live_use( Node def ) {
    if( def==ctl() ) return Type.ALL;
    if( def==mem() ) return _live; // All memory, including self alias
    if( !(_live instanceof TypeMem tmem) ) return _live.oob();
    // Struct-aliveness
    return tmem.at(_alias);
  }

//  @Override public void add_flow_def_extra(Node chg) {
//    if( chg instanceof MrgProjNode && chg._live.at(_alias)==TypeStruct.UNUSED )
//      Env.GVN.add_reduce(chg);
//  }

  @Override public boolean has_tvar() { return false; }

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


  // ProjNode after New produces a pointer TV2 from whole cloth
  @Override public boolean unify_proj( ProjNode proj, boolean test ) {
    assert proj._idx == REZ_IDX;
    return false;
  }
  
 
  // clones during inlining all become unique new sites
  @Override public NewNode copy( boolean copy_edges) {
    // Split the original '_alias' class into 2 sub-aliases
    NewNode nnn = (NewNode)super.copy(copy_edges);
    nnn.set_alias(BitsAlias.new_alias(_alias)); // Children alias classes, split from parent
        set_alias(BitsAlias.new_alias(_alias)); // The original NewNode also splits from the parent alias
    Env.GVN.add_flow(this);     // Alias changes flow
    return nnn;
  }

  @Override public int hashCode() { return super.hashCode()+ _alias; }
  // Only ever equal to self, because of unique _alias.  We can collapse equal
  // NewNodes and join alias classes, but this is not the normal CSE and so is
  // not done by default.
  @Override public boolean equals(Object o) {  return this==o; }
}
