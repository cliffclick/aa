package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.VBitSet;

import static com.cliffc.aa.AA.unimpl;

/** Combined Global Constant Propagation and Hindly-Milner with extensions.

See HM/HM.java for a complete stand-alone research version.

==============================================================================

Treats Hindly-Milner as a Monotone Analysis Framework; converted to a worklist
style.  The type variables are monotonically unified, gradually growing over
time - and this is treated as the MAF lattice.  Some normal Algo-W work has
already been done; e.g. discovering identifier sources (SSA form), and building
the non-generative set.  Because of the non-local unification behavior type
variables include a "dependent" set; a set of Nodes put back on the worklist if
this type unifies, beyond the expected Node graph neighbors.

The normal HM unification steps are treated as the MAF transfer functions,
taking type variables as inputs and producing new, unified, type variables.
Because unification happens in-place (normal disjoint-set union), the transfer
functions are executed for side effects only and return a progress flag.  The
transfer functions are virtual calls on Nodes, similar to the existing
Node.value() calls.

HM Bases include anything from the GCP lattice, but 'widened' to form borders
between e.g. ints and pointers.  Includes polymorphic structures and fields
(structural typing not duck typing), polymorphic nil-checking and an error type
variable.  Both HM and GCP types fully support recursive types.

Unification typically makes many temporary type variables and immediately
unifies them.  For efficiency, this algorithm checks to see if unification
requires an allocation first, instead of just "allocate and unify".  The major
place this happens is identifiers, which normally make a "fresh" copy of their
type-var, then unify.  I use a combined "make-fresh-and-unify" unification
algorithm there.  It is a structural clone of the normal unify, except that it
lazily makes a fresh-copy of the left-hand-side on demand only; typically
discovering that no fresh-copy is required.

To engineer and debug the algorithm, the unification step includes a flag to
mean "actually unify and report a progress flag" vs "report if progress".  The
report-only mode is aggressively asserted for; all Nodes that can make progress
are asserted as on the worklist.

==============================================================================

Global Optimistic Constant Propagation is treated as the usual Monotone
Analysis Framework.  Passed in the parsed program state (including any return
result, i/o and memory state).  Returns the most-precise types possible, and
replaces constants types with constants.

Besides the obvious GCP algorithm (and the type-precision that results from the
analysis), GCP does a few more things.

GCP builds an explicit Call-Graph.  Before GCP not all callers are known and
this is approximated by being called by ALL_CTRL, a ConNode of Type CTRL, as a
permanently available unknown caller.  If the whole program is available to us
then we can compute all callers conservatively and fairly precisely - we may
have extra never-taken caller/callee edges, but no missing caller/callee edges.
These edges are virtual (represented by ALL_CTRL) before GCP.  During GCP we
discover most ALL_CTRL paths are dead, and we add in physical CG edges as
possible calls are discovered.

GCP resolves all ambiguous (overloaded) calls, using the precise types first,
and then inserting conversions using a greedy decision.  If this is not
sufficient to resolve all calls, the program is ambiguous and wrong.

==============================================================================

The combined algorithm includes transfer functions taking facts from both MAF
lattices, producing results in the other lattice.

For the GCP->HM direction, the HM IfNode has a custom transfer function instead
of the usual one.  Unification looks at the GCP value, and unifies either the
true arm, or the false arm, or both or neither.  In this way GCP allows HM to
avoid picking up constraints from dead code.

Also for GCP->HM, the HM ground terms or base terms include anything from the
GCP lattice, instead of just the usual int/float/datum/string set.

For the HM->GCP direction, the GCP CallEpi has a customer transfer function
where the result from a call gets lifted (JOINed) based on the matching GCP
inputs - and the match comes from using the same HM type-var on both inputs and
outputs.  This allows e.g. "map" calls which typically merge many GCP values at
many call sites and thus end up typed as a Scalar to Scalar, to improve the GCP
type on a per-call-site basis.

 */
public abstract class Combo {
  public static final boolean DO_HM=true;

  public static void opto() {
    Env.GVN._opt_mode = GVNGCM.Mode.Opto;
    // General worklist algorithm
    Work work = new Work("Combo",false) { @Override public Node apply(Node n) { throw unimpl(); } };
    // Collect unresolved calls, and verify they get resolved.
    Work ambi = new Work("Ambi",false) { @Override public Node apply(Node n) { throw unimpl(); } };

    // Set all values to ANY and lives to DEAD, their most optimistic types.
    // Set all type-vars to Leafs.
    Env.START.walk_initype(work,true);
    assert Env.START.more_flow(work,false)==0; // Initial conditions are correct

    // Repeat; if we have any escaping calls, assume they are called with the
    // most pessimistic, but HM-type valid, arguments.  Otherwise, we must
    // assume they are called with Scalar which generally makes a type error.
    int cnt=0;                  // Debug counter
    while( !work.isEmpty() ) {

      // Repeat; if we remove some ambiguous choices, and keep falling until the
      // graph stabilizes without ambiguity.
      while( !work.isEmpty() ) {

        // Analysis phase.
        // Work down list until all reachable nodes types quit falling
        Node n;
        while( (n=work.pop()) != null ) {
          cnt++; assert cnt < 100000; // Infinite loop check
          if( n.is_dead() ) continue; // Can be dead functions after removing ambiguous calls

          // Forwards flow
          n.combo_forwards(work);

          // Backwards flow
          n.combo_backwards(work);

          // H-M unification
          if( DO_HM )
            n.combo_unify(work);

          // Check for resolving an unresolved call
          n.combo_resolve(ambi);

          // Very expensive assert: everything that can make progress is on worklist
          //assert Env.START.more_flow(work,false)==0;
        }

        // Remove CallNode ambiguity after worklist runs dry.  This makes a
        // 'least_cost' choice on unresolved Calls, and lowers them in the
        // lattice... allowing more GCP progress.
        remove_ambi(ambi,work);
        // If nothing resolved and there are still ambiguous calls, the program
        // is in error.  Force them to act as-if called by all choices and finish
        // off Opto.
        if( work.isEmpty() )
          for( Node call : ambi._work )
            if( !((CallNode)call)._not_resolved_by_gcp )
              ((CallNode)work.add(call))._not_resolved_by_gcp = true;
      }

      // The unknown caller flips to pessimistic defaults on HM types.
      lower_escaping_args(work);
    }

    assert Env.START.more_flow(work,false)==0; // Final conditions are correct
    Env.START.walk_opt(new VBitSet());
  }

  // Resolve ambiguous calls, and put on the worklist to make more progress.
  private static void remove_ambi(Work ambi, Work work) {
    assert work.isEmpty();
    for( int i=0; i<ambi.len(); i++ ) {
      CallNode call = (CallNode)ambi.at(i);
      if( call.remove_ambi() ) {
        ambi.del(i--);
        work.add(call);
      }
    }
  }

  // All functions called by the top exit scope escape - and thus may be called
  // by future callers.  These callers are assumed correct but conservative:
  // they are allowed to pass in the most conservative types consistent with
  // the H-M function type.
  private static void lower_escaping_args(Work work) {
    for( FunNode fun : FunNode.FUNS )
      if( fun!=null && !fun.is_dead() && fun.len()>= 2 && fun.in(1) instanceof CEProjNode && fun.in(1).in(0) instanceof ScopeNode && fun.in(1)._val == Type.CTRL ) {
        TV2 tfun = fun.ret().funptr().tvar();
        for( Node parm : fun._uses )
          if( parm instanceof ParmNode && parm.in(1)==Env.ALL_PARM ) {
            TV2 tparm = tfun.get((""+((ParmNode)parm)._idx).intern());
            if( tparm != null ) {
              Type t = tparm.as_flow();
              parm.set_def(1,Node.con(t));
              parm.in(1)._live = parm._live;
              work.add(parm);
            }
          }
      }
  }
}
