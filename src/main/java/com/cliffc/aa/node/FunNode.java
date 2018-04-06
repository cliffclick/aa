package com.cliffc.aa.node;

import com.cliffc.aa.*;

// FunNode is a RegionNode; args point to all the known callers.  Zero slot is
// empty, same as C2.  Arg1 points to the generic unknown worse-case caller;
// maybe local control at assignment time.  This can be removed once no more
// callers can appear.  Carries a Type which is a FunType, and has embedded
// TypeVars where structural sharing may occur.
//
// FunNodes are finite in count and unique densely numbered, and a FunType
// contains a bitset listing the set of possible functions allowed there.
// Could also contain an actual list of FunNode ptrs - not as program
// semantics, but as another variant of a list-of-FunNodes.
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
// RetNode is different from C2, to support precise function type inference.
// Rets point to the return control and value, like C2, but also the original
// FunNode with an index indicating which call.  There is a unique RetNode for
// every call-site, and its type is joined with the types used at the call.
// Example: FunNode "map" is called with type args A[] and A->B and returns
// type B[]; at one site its "[int]" and "int->str", so the RetNode for this
// site joins its result with "[str]".  However at another site the same
// FunNode is called with "[flt]" and "flt->int" so the Ret for that site
// joins its result with "[int]".
//
// Need a single Node for a function-pointer, obvious choice is FunNode.  Need
// some worse-case return Node to point call-sites at, and want to find that
// from the FunNode... which implies FunNodes point to their return value
// (not a RetNode, one of those per call-site).
//
// Something like a RetPC value, which is pass in from callers and used to find
// the call-site return.  The Type system needs to be able to pass around a
// simple/cheap value which contains e.g a bitset indicating which FunNodes
// might be in that function-ptr; this implies a finite set of FunNodes (and
// finite code).

// The Parser will use the Env to point to the worse-case JoinNode to allow (or
// create) more callers as parsing continues.  The RetNode is what is passed
// about for a "function pointer".
//
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
