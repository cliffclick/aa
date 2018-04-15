package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;

// This is a place-holder choice-of-functions for Apply.  The choice is limited
// to those with a auto-convert option (e.g. int->flt) or (anything->str).
// flt->int is NOT allowed except losslessly (e.g. 0.0 -> 0).  The semantics
// are that of join (since this is a choice) of functions.
//
// Since this is a place-holder, value() and ideal() do almost nothing.
// value() returns the join of its functions, after they are passed SCALAR args
// - typically the function does not handle all SCALAR values on all args, and
// so fails with an ALL.  ideal() can replace a choice-of-1 with the choice,
// and has support to toss out choices with incorrect args (known from the
// parser).  The goal is to collapse the Unresolved away.
//
// Apply carries the actuals args, and unless inlined, is typically very
// conservative args.  If some arg is not isa a formal, that function is not
// used (reports ALL to the JOIN); if no function is used the Apply returns
// ALL.  This is common for non-inlined calls where the args are only known as
// SCALAR.
//
// After Apply inlines a call-site and the args lift to e.g. int or flt, can
// some kind of real resolution take place.  The resolution logic is here, and
// returns a join-of-functions type result.  As soon as some function returns
// something other than ALL (because args apply), it supercedes other choices-
// which can be dropped.  

// If more than one choice applies, then the choice with fewest costly
// conversions are kept; if there is more than one then the join of them is
// kept - and the program is not-yet type correct (ambguious choices).
//
// "x=2; fun={y -> x+y}; fun(3)"
//
//            2(I) _Y(SCALAR)
//  I+I  F+F  /   /
//   UNR+    /   -
//     APPLY----/
//
// End up with 2/I + SCALAR/I  vs  2/F + SCALAR/F
//
// Since !SCALAR.isa(I), using I+I is not type-correct, cannot use I+I.
// Same for F+F, so type result is a join of two ALLs for an ALL result.
//
// Notion: if choice of no-conversions, this wins.
// Notion: if must convert, and any convert is i->f, this wins. (flts poison int math)
// Notion: if must convert f->i, only allowed if known lossless (user required for lossy conversions)
//
// Later pass; inline fun at the one call-site with 3.  End up with: "2/I + 3/I
// vs 2/F + 3/F".  Now we have type correct, and also int arg-only args, so
// preserve int-ness.  Choose I+I.  Could choose both is wanted to preserve
// choice for later.  If instead the unknown arg becomes a String, output
// remains ALL.
//


public class UnresolvedNode extends Node {
  public UnresolvedNode() { super(OP_UNR); }

  // JOIN of all incoming (function) types
  @Override public Type value(GVNGCP gvn) {
    Type t = Type.ALL;
    for( Node def : _defs )
      t = t.join(gvn.type(def));
    return t;
  }
  // Fold away a single choice
  @Override public Node ideal(GVNGCP gvn) {
    return _defs._len==1 ? _defs.at(0) : null;
  }
  
  // When a call-site and a function get together, we can filter out choices
  // based on argument count.
  public Node filter( int nargs ) {
    UnresolvedNode rez= new UnresolvedNode();
    for( Node n : _defs )       // For each choice function
      if( ((FunNode)n.at(2).at(0))._tf._ts._ts.length == nargs ) // Correct argument count
        rez.add_def(n);
    return Env._gvn.xform(rez); // Cleanup; could be a single choice or identical to input
  }

  // Given a list of actuals, apply them to each function choice.  If any
  // (!actual-isa-formal), then that function does not work and supplies an
  // ALL to the JOIN.  This is common for non-inlined calls where the unknown
  // arguments are approximated as SCALAR.  Lossless conversions are allowed as
  // part of a valid isa test.  As soon as some function returns something
  // other than ALL (because args apply), it supercedes other choices- which
  // can be dropped.

  // If more than one choice applies, then the choice with fewest costly
  // conversions are kept; if there is more than one then the join of them is
  // kept - and the program is not-yet type correct (ambiguous choices).
  Ary<Node> resolve( GVNGCP gvn, ApplyNode apply ) {
    // Set of possible choices with fewest conversions
    Ary<Node> ns = new Ary<>(new Node[1],0);
    int min_cvts = 999;         // Required conversions
    
    // for each function, see if the actual args isa the formal args.  If not, toss it out.
    outerloop:
    for( Node ret : _defs ) {
      // Peek Ret->RPC->Fun and get the function type
      TypeFun fun = (TypeFun)gvn.type(ret.at(2).at(0));
      Type[] formals = fun._ts._ts;   // Type of each argument
      if( formals.length != apply.nargs() )
        continue; // Argument count mismatch
      // Now check if the arguments are compatible at all
      boolean scalar=false;
      for( int j=0; j<formals.length; j++ ) {
        Type tx = apply.actual(gvn,j).join(formals[j]);
        if( tx.above_center() ) // Actual and formal have values in common?
          continue outerloop;   // No, this function will never work
        if( apply.actual(gvn,j)==Type.SCALAR ) scalar=true;
      }
      if( scalar ) { // Some unknown args from unknow callers
        ns.add(ret); // Cannot insert conversions, nor toss out based on converts
        continue;    // Must keep this choice
      }
      int cvts=0;               // Count required conversions
      for( int j=0; j<formals.length; j++ )
        if( !apply.actual(gvn,j).isBitShape(formals[j]) ) cvts++;
      // Save only choices with minimal conversions
      if( cvts < min_cvts ) { min_cvts = cvts; ns.clear(); }
      if( cvts == min_cvts)
        ns.add(ret);            // This is an acceptable choice.
    }
    return ns;
  }

  // Function return type for resolved functions.  Crash/ALL for no functions
  // allowed, join of possible returns otherwise - we get to choose the best
  // choice here.
  Type retype( GVNGCP gvn, ApplyNode apply ) {
    Type t = Type.ALL;
    outerloop:
    for( Node ret : _defs ) {
      // Peek Ret->RPC->Fun and get the function type
      TypeFun fun = (TypeFun)gvn.type(ret.at(2).at(0));
      Type[] formals = fun._ts._ts;   // Type of each argument
      if( formals.length != apply.nargs() ) continue; // Argument count mismatch; join of ALL
      // Now check if the arguments are compatible at all
      for( int j=0; j<formals.length; j++ )
        if( !apply.actual(gvn,j).isa(formals[j]) )
          continue outerloop;   // Actual is not a formal; join of ALL
      t = t.join(fun.ret());
    }    
    return t;
  }
  

  @Override public String toString() {
    SB sb = new SB().p("ANY(");
    boolean first=true;
    for( Node n : _defs ) { sb.p(first?"":" ").p(n==null?"_":n.at(1).str()); first=false; }
    return sb.p(")").toString();
  }
  @Override String str() { return "ANY"; }
  // Return a sample op_prec, but really could assert all are the same
  @Override public int op_prec() { return _defs._len==0 ? -1 : _defs.at(0).op_prec(); }
}
