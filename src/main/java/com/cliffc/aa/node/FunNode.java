package com.cliffc.aa.node;

import com.cliffc.aa.*;

// FunNode is a RegionNode; args point to all the known callers.  Zero slot is
// null, same as a C2 Region.  Args 1+ point to callers; Arg 1 points to Root
// as the generic unknown worse-case caller; This can be removed once no more
// callers can appear after parsing.  Carries a Type which is a FunType, and
// has embedded TypeVars where structural sharing may occur.
//
// FunNodes are finite in count and can be unique densely numbered.
//   
// Pointing to the FunNode are ParmNodes which are also PhiNodes; one input
// path for each known caller.  Zero slot points to the FunNode.  Arg1 points
// to the generic unknown worse-case caller (a type-specific ConNode with
// worse-case legit bottom type).  The collection of these ConNodes can share
// TypeVars to structurally type the inputs.  Alternative: the FunNode carries
// the type structure.
//
// There is an extra hidden argument/ParmNode - the return PC, or RPC.  This is
// a unique dense numbering of potential call-sites.
//
// The function body points to the FunNode and ParmNodes like C2.
//
// RetNode is different from C2, to support precise function type inference.
// Rets point to the return control and value, like C2, and also the original
// RPC parm.  Root points to the Ret, as the worse-case unknown caller.  Other
// Applys point to the the Ret have a constant RPC, and the RPC is used to
// select which return path is taken.  While there is a single Ret for all
// call-sites, the Applys can "peek through" to see the function body knowning
// the incoming args come from a known input path.
// 
// Example: FunNode "map" is called with type args A[] and A->B and returns
// type B[]; at one site its "int[]" and "int->str" and at another site its
// "flt[]" and "flt->int" args.  The RetNode merges results to be "SCALAR[]".
// The Apply#1 upcasts its value to "str[]", and Apply#2 upcasts its value to
// "int[]".
//
// The Parser will use the Env to point to the worse-case RetNode to allow (or
// create) more callers as parsing continues.  The RetNode is what is passed
// about for a "function pointer".
//
public class FunNode extends Node {
  public final TypeFun _tf;     // Worse-case correct type
  public FunNode(TypeFun tf) { super(OP_FUN,Env.top_root()); _tf = tf; }
  @Override String str() { return _tf.toString(); }
  @Override public Node ideal(GVNGCP gvn) { return null; }
  @Override public Type value(GVNGCP gvn) { return _tf; }
  @Override public Type all_type() { return _tf; }
}
