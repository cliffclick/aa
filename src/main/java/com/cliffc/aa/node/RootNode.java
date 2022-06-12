package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.type.*;

import java.util.function.Predicate;

import static com.cliffc.aa.AA.unimpl;
import static com.cliffc.aa.AA.CTL_IDX;
import static com.cliffc.aa.AA.MEM_IDX;
import static com.cliffc.aa.AA.REZ_IDX;


// Program execution start
public class RootNode extends Node {
  // Inputs are:
  // [program exit control, program exit memory, program exit value, escaping RetNodes... ]
  public RootNode() { super(OP_ROOT, null, null, null); }

  // Output value is:
  // [escaped_fidxs, escaped_aliases, TypeRPC.ALL_CALL]
  @Override public Type value() {
    BitsFun fidxs = BitsFun.NALL;
    BitsAlias aliases = BitsAlias.NALL;
    Node rez = in(REZ_IDX);
    if( in(MEM_IDX) == null || rez == null )
      // No top-level return yet, so return most conservative answer
      return TypeTuple.make(TypeFunPtr.make(fidxs,1),
                            TypeMemPtr.ISUSED.make_from(aliases),
                            TypeRPC.ALL_CALL);

    if( rez._val instanceof TypeMemPtr )
      throw unimpl();
    if( rez._val instanceof TypeFunPtr )
      throw unimpl();
    // Return is some primitive answer; no escapes
    return TypeTuple.make(TypeFunPtr.EMPTY,
                          TypeMemPtr.EMTPTR,
                          TypeRPC.ALL_CALL);
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
  }
}
