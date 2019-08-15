package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeTuple;

/** TODO CNC NOTES

CallEpi - merges call-graph edges, but the call-graph is not discovered prior
to GCP.  If any call wires up pre-GCP it must be exact.  So: "if(!opto||wired)"
then optimistic MEET of all incoming Returns.  Otherwise, must be pre-opto and
pessimal: all calls are possible so the result is TypeTuple.CALL.  Move
Unresolved handling into CallEpi from Call, since it will not wire but the
result type is more precise.

Call - convenient if its type is just a gather of inputs and does no
processing.  When the type changes, it propagates to CallEpi to recompute.
Mostly need Control and the FunPtr types.  No need for arg or memory types.

Return: revert to integrated Epilog and Type is the standard run-together of
{Ctrl,Mem,Val}.  Changes if any exit value changes.  Point to FunNode as last
edge same as old Epilog, for fast SESE access.

Epilog: Drop.

FunPtrNode: Add: just points to the Return to keep it alive, and keeps the
matching FIDX.  Type is a BitsFun.  Used by static calls, Unresolved, Stores,
Phis, etc.  After GCP these should be let-go and dead functions dropped.



 */

// See CallNode
public final class CallEpiNode extends Node {
  public CallEpiNode( Node... rets ) { super(OP_CALLEPI,rets); }
  @Override public Node ideal(GVNGCM gvn) {
    // If is_copy is true, CallEpiNodes uses need to fold away as well
    if( is_copy(gvn,0) != null )
      for( Node use : _uses ) gvn.add_work(use);
    return null;
  }
  @Override public Type value(GVNGCM gvn) {
    Type t = TypeTuple.XCALL;
    for( Node n : _defs )
      t = t.meet(gvn.type(n));
    return t;
  }

  void rewire( GVNGCM gvn, EpilogNode oldepi, EpilogNode newepi ) {
    unwire(gvn,oldepi);
    gvn.add_def(this,newepi.ret());
  }
  void unwire( GVNGCM gvn, EpilogNode epi ) {
    int idx = _defs.find(epi.ret());
    if( idx != -1 ) gvn.remove(this,idx);
  }
  @Override public Node is_copy(GVNGCM gvn, int idx) { return in(0).is_copy(gvn,idx); }
  @Override public Type all_type() { return TypeTuple.CALL; }
}
