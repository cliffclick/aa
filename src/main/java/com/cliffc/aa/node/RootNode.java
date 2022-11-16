package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.VBitSet;

import java.util.function.Predicate;

import static com.cliffc.aa.AA.*;


// Program execution start
public class RootNode extends Node {
  // Inputs are:
  // [program exit control, program exit memory, program exit value, escaping RetNodes... ]
  public RootNode() { super(OP_ROOT, null, null, null); _def_mem = TypeMem.ALLMEM; }

  private TypeMem _def_mem;
  private Type _cache_key;
  private TypeTuple _cache_val;

  @Override boolean is_CFG() { return true; }

  // Output value is:
  // [Ctrl,All_Mem_Minus_Dead,TypeRPC.ALL_CALL,escaped_fidxs, escaped_aliases,]
  @Override public TypeTuple value() {
    Node rez = in(REZ_IDX);
    if( in(MEM_IDX) == null || rez == null )
      // No top-level return yet, so return most conservative answer
      rez = Env.ALL;
    // Check the cache
    if( rez._val==_cache_key && _def_mem == _cache_val.at(MEM_IDX) )
      return _cache_val;

    // Reset for walking
    ESCF.clear();
    EXT_ALIASES = BitsAlias.EMPTY;
    EXT_FIDXS = BitsFun.EMPTY;
    // Walk
    _escapes(rez._val);
    // Fill cache after walking
    _cache_key = rez._val;
    return (_cache_val = TypeTuple.make(Type.CTRL,
                                        _def_mem,
                                        TypeRPC.ALL_CALL,
                                        TypeFunPtr.make(EXT_FIDXS,1),
                                        TypeMemPtr.make(false,false,EXT_ALIASES,TypeStruct.ISUSED)));
  }

  public void kill_alias( int alias ) {
    _def_mem = _def_mem.make_from_unused(alias,TypeStruct.UNUSED);
    Env.GVN.add_flow(this);
  }

  // Escape all Root results.  Escaping functions are called with the most
  // conservative HM-compatible arguments.  Escaping Structs are recursively
  // escaped, and can appear as input arguments.
  private static final VBitSet ESCF = new VBitSet();
  private static BitsAlias EXT_ALIASES;
  private static BitsFun EXT_FIDXS;

  private static void _escapes(Type t) {
    if( t == Type.ALL ) {
      EXT_ALIASES = BitsAlias.NALL;
      EXT_FIDXS = BitsFun.NALL;
    }
    if( t instanceof TypeMemPtr tmp ) {
      // Add to the set of escaped structures
      for( int alias : tmp._aliases ) {
        if( alias==0 ) continue;
        if( !EXT_ALIASES.test(alias) ) continue;
        EXT_ALIASES = EXT_ALIASES.set(alias);
        //Alloc a = ALIASES.at(alias);
        //TypeMemPtr atmp = a.tmp();
        //for( TypeFld fld : atmp._obj )
        //  if( !Util.eq(fld._fld,"^") )
        //    _escapes(fld._t,work);
        throw unimpl();
      }
    }
    if( t instanceof TypeFunPtr tfp && !ESCF.tset(tfp._uid) ) {
      // Walk all escaped function args, and call them (like an external
      // Apply might) with the most conservative flow arguments possible.
      for( int fidx : tfp.fidxs() ) {
        if( fidx==0 ) continue;
        RetNode ret = RetNode.FUNS.at(fidx);
        if( ret!=null && !EXT_FIDXS.test(fidx) ) {
          FunPtrNode fptr = ret.funptr();
          if( fptr !=null && fptr.has_tvar() ) {
            TV3 tfun = ret.funptr().tvar();
            tfun.add_deps_work();
            //tfun.arg(" ret").clr_cp();
            throw unimpl();
          }
        }
        EXT_FIDXS = EXT_FIDXS.set(fidx);
        //for( int i=0; i<fun.nargs(); i++ ) {
        //  // One-time make compatible external func/struct for this argument
        //  Type cflow;
        //  if( fun instanceof Lambda lam ) {
        //    Ident[] ids = lam._refs[i];
        //    if( ids!=null ) {
        //      EXT_DEPS.add(ids); // Add to external deps; when HM_FREEZE flips these all need to be visited
        //      for( Ident id : lam._refs[i] ) EXT_DEPS.add(id._par);
        //    }
        //    T2 t2 = lam.targ(i); // Get HM constraints on the arg
        //    if( t2.is_fun() && !lam.extsetf(i) ) new EXTLambda(t2); // Make a canonical external function to call
        //    if( t2.is_ptr() && !lam.extsetp(i) ) new EXTStruct(t2); // Make a canonical external struct for args
        //    cflow = t2.as_flow(false);
        //  } else {
        //    cflow = TypeNil.SCALAR; // Most conservative args
        //  }
        //  fun.arg_meet(i,cflow,work); // Root / external-world calls this function with this arg
        //}
      }
      // The flow return also escapes
      _escapes(tfp._ret);
    }
  }


  @Override public Type live() { return Type.ALL; }
  @Override public int hashCode() { return 123456789+1; }
  @Override public boolean equals(Object o) { return this==o; }
  @Override Node walk_dom_last( Predicate<Node> P) { return null; }
  @Override public boolean has_tvar() { return false; }

  // Unify trailing result ProjNode with RootNode results; but no unification
  // with anything from Root, all results are independent.
  @Override public boolean unify_proj( ProjNode proj, boolean test ) {
    return false;
  }

  @Override public Node ideal_reduce() {
    Node rez = in(REZ_IDX);
    if( rez!=null && in(MEM_IDX) != Env.XMEM && !(rez._val instanceof TypeMemPtr) && !(rez._val instanceof TypeFunPtr) )
      return set_def(MEM_IDX,Env.XMEM);
    return null;
  }

  // Reset for next test
  public void reset() {
    set_def(CTL_IDX,null);
    set_def(MEM_IDX,null);
    set_def(REZ_IDX,null);
    while( len() > REZ_IDX+1 )
      pop();
    _def_mem = TypeMem.ALLMEM;
  }
}
