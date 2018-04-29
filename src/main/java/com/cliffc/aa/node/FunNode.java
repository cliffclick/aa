package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.util.Ary;

import java.util.HashMap;

// FunNode is a RegionNode; args point to all the known callers.  Zero slot is
// null, same as a C2 Region.  Args 1+ point to callers; Arg 1 points to Scope
// as the generic unknown worse-case caller; This can be removed once no more
// callers can appear after parsing.  Each unique call-site to a function gets
// a new path to the FunNode.
//
// FunNodes are finite in count and can be unique densely numbered.
// TODO: Use this numbering in TypeFun, to allow function constants.
//   
// Pointing to the FunNode are ParmNodes which are also PhiNodes; one input
// path for each known caller.  Zero slot points to the FunNode.  Arg1 points
// to the generic unknown worse-case caller (a type-specific ConNode with
// worse-case legit bottom type).  The collection of these ConNodes can share
// TypeVars to structurally type the inputs.  ParmNodes merge all input path
// types (since they are a Phi), and the call "loses precision" for type
// inference there.
//
// The function body points to the FunNode and ParmNodes like C2.
//
// RetNode is different from C2, to support precise function type inference.
// Rets point to the return control and the original FunNode; its type is a
// control Tuple, similar to IfNodes.  Pointing to the RetNode are Projs with
// call-site indices; they carry the control-out of the function for their
// call-site.  While there is a single Ret for all call-sites, Calls can "peek
// through" to see the function body learning the incoming args come from a
// known input path.
// 
// Results come from CastNodes, which up-cast the merged function results back
// to the call-site specific type - this is where the precision loss are
// ParmNodes is regained.  CastNodes point to the original call-site control
// path and the function result.

// Example: FunNode "map" is called with type args A[] and A->B and returns
// type B[]; at one site its "int[]" and "int->str" and at another site its
// "flt[]" and "flt->int" args.  The RetNode merges results to be "SCALAR[]".
// The Cast#1 upcasts its value to "str[]", and Cast#2 upcasts its value to
// "int[]".
// 
//  0 Scope...               -- Call site#1 control
//  1 Con_TV#C (really A[] ) -- Call site#1 arg#1
//  2 Con_TV#D (really A->B) -- Call site#1 arg#2
//  3 Ctrl callsite 2        -- Call site#2 control
//  4 arg#int[]              -- Call site#2 arg#1  
//  5 arg#int->str           -- Call site#2 arg#2  
//  6 Ctrl callsite 3        -- Call site#3 control
//  7 arg#flt[]              -- Call site#3 arg#1  
//  8 arg#flt->int           -- Call site#3 arg#2  
//  9 Fun _ 0 3 6
// 10 ParmX 9 1 4 7  -- meet of A[] , int[]   , flt[]
// 11 ParmX 9 2 5 8  -- meet of A->B, int->str, flt->int
// -- function body, uses 9 10 11
// 12 function body control
// 13 function body return value
// -- function ends
// 14 Ret 12 13 9 {A[] {A -> B} -> B[]}
// 15 Proj#1 14            -- Return path  for unknown caller in slot 1
// 16 Cast#1 0 13#SCALAR[] -- Return value for unknown caller in slot 1
// 16 Proj#2 14            -- Return path  for caller {int[] {int -> str} -> str[]}
// 17 Cast#2 3 13#flt[]    -- Return value for caller {int[] {int -> str} -> str[]}
// 18 Proj#3 14            -- Return path  for caller {flt[] {flt -> int} -> int[]}
// 19 Cast#3 6 13#int[]    -- Return value for caller {flt[] {flt -> int} -> int[]}
//
// The Parser will use the Env to point to the RetNode to create more callers
// as parsing continues.  The RetNode is what is passed about for a "function
// pointer".
//
public class FunNode extends RegionNode {
  static private int CNT=2; // Function index; 1 is reserved for unknown functions
  private final int _fidx;  // Function index; 1 is reserved for unknown functions
  final byte _op_prec;      // Operator precedence; only set top-level primitive wrappers
  public final TypeFun _tf; // Worse-case correct type
  public FunNode(TypeFun tf, Node sc) { this(tf,sc,-1); }
  public FunNode(TypeFun tf, Node sc, int op_prec) { super(OP_FUN,sc); _tf = tf; _fidx = CNT++; _op_prec = (byte)op_prec; }
  @Override String str() { return "fun#"+_fidx+":"+_tf.toString(); }

  @Override public Node ideal(GVNGCM gvn) {
    // Clone function for type-specialization
    Node n = type_special(gvn);
    if( n != null ) return n;
    // Else generic Region ideal
    return ideal(gvn,gvn.type(at(1))==TypeErr.ANY?1:2);
  }

  // Look for type-specialization inlining.  If any ParmNode has an Unresolved
  // Call, then we'd like to make a clone of the function body (at least up to
  // getting all the UnresolvedNodes to clear out).  The specialized code uses
  // generalized versions of the arguments, where we only specialize on
  // arguments that help immediately.
  private Node type_special( GVNGCM gvn ) {
    // Bail if there are any dead pathes; RegionNode ideal will clean out
    for( int i=1; i<_defs._len; i++ ) if( gvn.type(at(i))==TypeErr.ANY ) return null;
    if( _defs._len <= 2 ) return null; // No need to specialize if only 1 caller
    if( !(at(1) instanceof ScopeNode) ) throw AA.unimpl();
    
    // Gather the ParmNodes and the RetNode.  Ignore other (control) uses
    int nargs = _tf._ts._ts.length+1;
    ParmNode[] parms = new ParmNode[nargs];
    RetNode ret = null;
    for( Node use : _uses )
      if( use instanceof ParmNode ) parms[((ParmNode)use)._idx] = (ParmNode)use;
      else if( use instanceof RetNode ) { assert ret==null || ret==use; ret = (RetNode)use; }
    
    // Visit all ParmNodes, looking for unresolved call uses
    boolean any_unr=false;
    boolean[] has_unrs = new boolean[nargs];
    for( int i=1; i<nargs; i++ )
      for( Node use : parms[i]._uses )
        if( use instanceof CallNode && use.at(1) instanceof UnresolvedNode ) {
          has_unrs[i] = any_unr = true; break;
        }
    if( !any_unr ) return null; // No unresolved calls; no point in type-specialization

    // Find the Proj matching the call to-be-cloned
    ProjNode prj2 = null;
    for( Node use : ret._uses )
      if( use instanceof ProjNode && ((ProjNode)use)._idx == 2 )
        { assert prj2==null; prj2 = (ProjNode)use; }
    if( prj2 == null )          // Not found?  This path is dead
      throw AA.unimpl();        // TODO: Should be eliminated by e.g. RetNode
    
    // Make a more-specific clone of the original function, and direct calls
    // with the matching arguments to it.
    
    // If Parm has unresolved calls, we want to type-specialize on its
    // arguments.  Call-site #1 is the most generic call site for the parser
    // (all Scalar args).  Peel out 2nd call-site args and generalize them.
    Type[] sig = new Type[nargs-1];
    for( int i=1; i<nargs; i++ )
      sig[i-1] = gvn.type(parms[i].at(2)).widen();
    // Make a new function header with new signature
    TypeFun tf = TypeFun.make(TypeTuple.make(sig),_tf._ret);
    assert tf.isa(_tf);
    if( tf == _tf ) return null; // No improvement for further splitting
    FunNode fun2 = new FunNode(tf,at(1));
    fun2.add_def(at(2));

    // Clone the function body
    HashMap<Node,Node> map = new HashMap<>();
    Ary<Node> work = new Ary<>(new Node[1],0);
    map.put(this,fun2);
    work.addAll(_uses);         // Prime worklist
    while( work._len > 0 ) {    // While have work
      Node n = work.pop();      // Get work
      if( map.get(n) != null ) continue; // Already visited?
      if( n instanceof CastNode && n.at(0).at(0)==ret )
        continue;              // Do not clone function data-exit 
      if( n != ret )           // Except for the Ret, control-exit for function
        work.addAll(n._uses);  // Visit all uses also
      map.put(n,n.copy()); // Make a blank copy with no edges and map from old to new
    }

    // Fill in edges.  New Nodes point to New instead of Old; everybody
    // shares old nodes not in the function (and not cloned).  The
    // FunNode & Parms only get the matching slice of args.
    for( Node n : map.keySet() ) {
      Node c = map.get(n);
      if( n instanceof ParmNode ) {  // Leading edge ParmNodes
        c.add_def(map.get(n.at(0))); // Control
        c.add_def(gvn.con(sig[((ParmNode)n)._idx-1])); // Generic arg#1
        // Only keep defs matching signature, not all of them.
        if( _defs._len != 3 ) throw AA.unimpl(); // TODO: Actually doing signature-splitting...
        c.add_def(n.at(2));     // Specific arg#2
      } else if( !(n instanceof FunNode)) { // Interior nodes
        for( Node def : n._defs ) {
          Node newdef = map.get(def);
          c.add_def(newdef==null ? def : newdef);
        }
      }
    }
    if( prj2._uses._len != 1 )
      throw AA.unimpl(); // Should be a control-use and a data/Cast use
    Node data = (CastNode)prj2._uses.at(0);
    gvn.unreg(prj2);
    gvn.unreg(data);
    prj2.set_def(0,map.get(ret),gvn); // Repoint proj as well
    data.set_def(1,map.get(ret.at(1)),gvn);
    // TODO: CAST repointed to new call as well
    set_def(2,gvn.con(TypeErr.ANY),gvn); // Kill incoming path on old FunNode

    // Put all new nodes into the GVN tables and worklists
    for( Node c : map.values() ) gvn.rereg(c);
    gvn.rereg(prj2);
    gvn.rereg(data);
    // TODO: Hook with proper signature into ScopeNode under an Unresolved.
    // Future calls may resolve to either the old version or the new.
    return this;
  }
  
  @Override public int hashCode() { return OP_FUN+_fidx; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof FunNode) ) return false;
    FunNode fun = (FunNode)o;
    return _fidx==fun._fidx;
  }
  @Override public byte op_prec() { return _op_prec; }
}
