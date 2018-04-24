package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.util.Ary;

// This is a place-holder choice-of-functions for Call.  The choice is limited
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
// Call carries the actuals args, and unless inlined, is typically very
// conservative args.  If some arg is not isa a formal, that function is not
// used (reports ALL to the JOIN); if no function is used the Call returns
// ALL.  This is common for non-inlined calls where the args are only known as
// SCALAR.
//
// After Call inlines a call-site and the args lift to e.g. int or flt, can
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
//     CALL-----/
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
  private final String _name;
  UnresolvedNode(String name) { super(OP_UNR); _name=name; }

  // Fold away a single choice
  @Override public Node ideal(GVNGCM gvn) {
    return _defs._len==1 ? _defs.at(0) : null;
  }
  // JOIN of all incoming (function) types
  @Override public Type value(GVNGCM gvn) {
    Type t = TypeErr.ALL;
    for( Node def : _defs ) {
      FunNode fun = (FunNode) (def.at(0).at(2));
      t = t.join(fun._tf);
    }
    return t;
  }
  
  // When a call-site and a function get together, we can filter out choices
  // based on argument count.
  public Node filter( int nargs ) {
    UnresolvedNode rez= new UnresolvedNode(_name);
    for( Node n : _defs )       // For each choice function
      if( ((FunNode)n.at(0).at(2))._tf._ts._ts.length == nargs ) // Correct argument count
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
  Ary<Node> resolve( GVNGCM gvn, CallNode call ) {
    // Set of possible choices with fewest conversions
    Ary<Node> ns = new Ary<>(new Node[1],0);
    int min_cvts = 999;         // Required conversions
    int cvts[] = new int[_defs._len];

    // For each function, see if the actual args isa the formal args.  If not,
    // toss it out.  Also count conversions, and keep the minimal conversion
    // function with all arguments known.
    outerloop:
    for( Node proj : _defs ) {
      // Peek Proj->Ret->Fun and get the function type
      TypeFun fun = ((FunNode)(proj.at(0).at(2)))._tf;
      Type[] formals = fun._ts._ts;   // Type of each argument
      if( formals.length != call.nargs() )
        continue; // Argument count mismatch, toss out this choice
      // Now check if the arguments are compatible at all, keeping lowest cost
      int xcvts = 0;             // Count of conversions required
      boolean unk = false;       // Unknown arg might be incompatible or free to convert
      for( int j=0; j<formals.length; j++ ) {
        Type actual = gvn.type(call.actual(j));
        Type tx = actual.join(formals[j]);
        if( tx.above_center() ) // Actual and formal have values in common?
          continue outerloop;   // No, this function will never work; e.g. cannot cast 1.2 as any integer
        byte cvt = actual.isBitShape(formals[j]); // +1 needs convert, 0 no-cost convert, -1 unknown, 99 never
        if( cvt == 99 )         // Happens if actual is e.g. TypeErr
          continue outerloop;   // No, this function will never work
        if( cvt == -1 ) unk = true; // Unknown yet
        else xcvts += cvt;          // Count conversions
      }
      if( !unk && xcvts < min_cvts ) min_cvts = xcvts; // Keep minimal known conversion
      cvts[ns._len] = xcvts;    // Keep count of conversions
      ns.add(proj);             // This is an acceptable choice, so far (args can be made to work)
    }
    // Toss out choices with strictly more conversions than the minimal
    for( int i=0; i<ns._len; i++ )
      if( cvts[i] > min_cvts ) {
        cvts[i] = cvts[ns._len-1];
        ns.del(i--);
      }
    return ns;
  }

  // Function return type for resolved functions.  Crash/ALL for no functions
  // allowed, join of possible returns otherwise - we get to choose the best
  // choice here.
  Type retype( GVNGCM gvn, CallNode call ) {
    Type t = TypeErr.ALL;
    outerloop:
    for( Node proj : _defs ) {
      // Peek Proj->Ret->Fun and get the function type
      TypeFun fun = ((FunNode)proj.at(0).at(2))._tf;
      Type[] formals = fun._ts._ts;   // Type of each argument
      if( formals.length != call.nargs() ) continue; // Argument count mismatch; join of ALL
      // Now check if the arguments are compatible at all
      for( int j=0; j<formals.length; j++ )
        if( !gvn.type(call.actual(j)).isa(formals[j]) )
          continue outerloop;   // Actual is not a formal; join of ALL
      t = t.join(fun.ret());
    }    
    return t;
  }

  String errmsg() {
    String s = _name+":[ ";
    for( Node proj : _defs )
      s += ((FunNode)(proj.at(0).at(2)))._tf+" ";
    return s+"]";
  }
  @Override String str() { return "Unr"+_name; }
  // Return a sample op_prec, but really could assert all are the same
  @Override public byte op_prec() { return _defs._len==0 ? -1 : _defs.at(0).at(0).op_prec(); }
}
