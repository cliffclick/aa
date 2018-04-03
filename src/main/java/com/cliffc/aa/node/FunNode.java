package com.cliffc.aa.node;

import com.cliffc.aa.*;

// Function node; after construction will have one def pointing to the return
// results and all the ParmNodes will point to it.

// CNC: Thinking about solve 1st-class function typing issues
//
// FunNode is a RegionNode; args point to all the known callers.  Zero slot is
// empty, same as C2.  Arg1 points to the generic unknown worse-case caller;
// maybe local control at assignment time.  This can be removed once no more
// callers can appear.  Carries a Type which is a FunType, and has embedded
// TypeVars where structural sharing may occur.
//   
// Pointing to the FunNode are ParmNodes which are also PhiNodes; one input
// path for each known caller.  Zero slot points to the FunNode.  Arg1 points
// to the generic unknown worse-case caller (a type-specific ConNode with
// worse-case legit bottom type).  The collection of these ConNodes can share
// TypeVars to structurally type the inputs.  Alternative: the FunNode carries
// the type structure.
//
// The function body points to the FunNode and ParmNodes like C2.
//
// The ReturnNode points to the computed return control in slot 0, the FunNode
// in slot 1 (UNLIKE C2) and the return value in slot 2 (again UNLIKE C2).
// This gives constant-time access to the FunNode from the return.
//
// There is a JoinNode which points to the ReturnNode for actual value.  The
// JoinNode is specific to each caller, and carries the return value for each
// caller (ReturnNodes are only used by JoinNodes).  The JoinNode joins() its
// input with the callers' known type, lifting the result per-call-site.  This
// sharpens the type analysis per-call-site, which I think is required for H-M
// style typing, and leads to a O(n^2) graph (maybe?)
//
// The Parser will use the Env to point to the worse-case JoinNode to allow (or
// create) more callers as parsing continues.  The JoinNode is what is passed
// about for a "function pointer".  The graph walk is: Join->Return->Fun
//
// ---
//
// ApplyNodes do not need a zero arg (can freely float).  The arg1 is typed as
// a collection-of-possible-functions (an ALL-UnionType of functions).  Args2+
// are for parms.  Inlining can happen when the input arg1 becomes a constant
// function.



public class FunNode extends Node {
  @Override String str() { return "{...}"; }
  @Override public Node ideal(GVNGCP gvn) { return null; }
  @Override public Type value(GVNGCP gvn) { return Type.SCALAR; }
  @Override public Type all_type() { return Type.SCALAR; } // TODO: Function call any arg count
}
