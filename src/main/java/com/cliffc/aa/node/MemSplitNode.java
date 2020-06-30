package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;

// Split a set of aliases into a SESE region, to be joined by a later MemJoin.
// This allows more precision in the SESE that may otherwise merge many paths
// in and out, and is especially targeting non-inlined calls.
public class MemSplitNode extends Node {
  final int _cuid;
  public MemSplitNode( CallNode call ) {
    super(OP_SPLIT,call.mem());
    _cuid = call._uid;
    copy_call_args(call,null);
    // CNC 6/29/2020 - not using
    throw com.cliffc.aa.AA.unimpl();
  }
  String xstr() { return ((is_dead() || is_copy(null,1)!=null) ? "x" : "S")+"plit"; } // Self short name
  String  str() { return xstr(); }       // Inline short name
  Node mem() { return in(0); }
  @Override public Node ideal(GVNGCM gvn, int level) {
    // Match call args.  Call args change for a bunch of reasons (constants,
    // dead) and instead of directly using them (and having the non-local
    // curse), nor being "inside" a Call/CEPI pair and depending on a Call (and
    // thus the Join has to do the CEPIs job of merging returns), just replicate
    // the Call args here.
    CallNode call = call();
    if( call != null )
      for( int i=0; i<call.nargs(); i++ )
        if( in(i+1)!=call.arg(i) )
          return copy_call_args(call,gvn);

    return null;
  }


  // Look at the arguments and find the transitive closure of escaped pointers.
  // These must go to the Right Hand Side (RHS), and the non-escaped pointers
  // can go on the LHS.  LHS is a pass-around a call, while the RHS merges in
  // the called functions and may be conservatively approximated.
  @Override public Type value(GVNGCM gvn) {
    // Check memory
    Type t0 = gvn.type(in(0));
    if( !(t0 instanceof TypeMem) ) return t0.oob();
    // Default for early fail-out.  All to the RHS, none to the LHS.
    TypeMem mem = (TypeMem)t0;    // Lowest, lifting to something is the RHS type; lifting to ~use moves things to LHS.
    // Gather all aliases from all args
    BitsAlias as = BitsAlias.EMPTY;
    for( int i=1; i<_defs._len; i++ ) {
      Type t = gvn.type(in(i));
      as = as.meet(get_alias(t));
      if( as==BitsAlias.FULL ) break;
    }
    // Recursively search memory for aliases
    BitsAlias as2 = mem.all_reaching_aliases(as);
    // Slice the memory
    TypeMem rhs = mem;
    // pre-call memory, RHS memory, escaping aliases
    return TypeTuple.make( mem, rhs, TypeMemPtr.make(as2,TypeObj.UNUSED) );
  }
  @Override public boolean basic_liveness() { return false; }
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) { return def==mem() ? _live : TypeMem.ALIVE; }

  CallNode call() {
    ProjNode p1 = ProjNode.proj(this,1);
    if( p1==null ) return null;
    int idx = p1._uses.find(e->e instanceof CallNode);
    if( idx==-1 ) return null;
    CallNode call = (CallNode)(p1._uses.at(idx));
    if( call._uid == _cuid ) return call; // Fixed to a particular call.  Means if Call goes dead, the Split & args are orphaned
    return null;
  }
  private Node copy_call_args(CallNode call, GVNGCM gvn) {
    while( _defs._len > 1 )
      pop(gvn);
    // Add all call args, needed to split escaping aliases
    for( int i=0; i<call.nargs(); i++ )
      add_def(call.arg(i));
    return this;
  }
  // Get (shallow) aliases from the type
  private static BitsAlias get_alias(Type t) {
    if( t instanceof TypeMemPtr ) return ((TypeMemPtr)t)._aliases;
    if( t instanceof TypeFunPtr ) return ((TypeFunPtr)t)._disp._aliases;
    if( TypeMemPtr.OOP.isa(t)   ) return BitsAlias.FULL;
    return BitsAlias.EMPTY;
  }

  @Override public Node is_copy(GVNGCM gvn, int idx) {
    if( _keep>0 || _uses._len>1 ) return null;
    MProjNode pj = (MProjNode)_uses.at(0);
    if( pj._idx!=idx ) return null; // Wrong projection
    Type t = gvn.self_type(this);
    if( !(t instanceof TypeTuple) ) return null;
    TypeTuple tt = (TypeTuple)t;
    BitsAlias as = ((TypeMemPtr)tt.at(2))._aliases;
    if( idx==0 && as==BitsAlias.EMPTY )  return mem();
    if( idx==0 && as==BitsAlias.NIL   )  throw com.cliffc.aa.AA.unimpl();
    if( idx==1 && as==BitsAlias.FULL  )  return mem();
    if( idx==1 && as==BitsAlias.NZERO )  throw com.cliffc.aa.AA.unimpl();
    return null;
  }
}
