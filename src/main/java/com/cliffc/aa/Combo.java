package com.cliffc.aa;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.node.Work;
import com.cliffc.aa.util.VBitSet;

import static com.cliffc.aa.AA.unimpl;

/** Combined Global Constant Propagation and Hindly-Milner with extensions.

See HM/HM.java for a complete stand-alone research version.

==============================================================================
Treats Hindly-Milner as a Monotone Analysis Framework; converted to a worklist
style.  The type variables are monotonically unified, gradually growing over
time - and this is treated as the MAF lattice.  Some of the normal Algo-W work
has already been done; e.g. discovering identifier sources (SSA form), and
building the non-generative set.  Because of the non-local unification behavior
type variables include a "dependent" set; a set of Nodes put back on the
worklist if this type unifies, beyond the expected Node graph neighbors.

The normal HM unification steps are treated as the MAF transfer functions,
taking type variables as inputs and producing new, unified, type variables.
Because unification happens in-place (normal disjoint-set union), the transfer
functions are executed for side-effects only and return a progress flag.  The
transfer functions are virtual calls on Nodes, similar to the existing
Node.value() calls.

HM Bases include anything from the GCP lattice, but 'widened' to form borders
between e.g. ints and pointers.  Includes polymorphic structures and fields
(structural typing not duck typing), polymorphic nil-checking and an error type
variable.  Both HM and GCP types fully support recursive types.

Unification typically makes many many temporary type variables and immediately
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

Global Optimistic Constant Propagation treated as the usual Monotone Analysis
Framework.  Passed in the parsed program state (including any return result, i/o
and memory state).  Returns the most-precise types possible, and replaces
constants types with constants.

Besides the obvious GCP algorithm (and the type-precision that results
from the analysis), GCP does a few more things.

GCP builds an explicit Call-Graph.  Before GCP not all callers are known
and this is approximated by being called by ALL_CTRL, a ConNode of Type
CTRL, as a permanently available unknown caller.  If the whole program is
available to us then we can compute all callers conservatively and fairly
precisely - we may have extra never-taken caller/callee edges, but no
missing caller/callee edges.  These edges are virtual (represented by
ALL_CTRL) before GCP.  Just before GCP we remove the ALL_CTRL path, and
during GCP we add in physical CG edges as possible calls are discovered.

GCP resolves all ambiguous (overloaded) calls, using the precise types
first, and then inserting conversions using a greedy decision.  If this is
not sufficient to resolve all calls, the program is ambiguous and wrong.

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
  private static final boolean DO_HM=false;

  public static void opto() {
    Env.GVN._opt_mode = GVNGCM.Mode.Opto;
    // General worklist algorithm
    Work work = new Work("Combo",false) { @Override public Node apply(Node n) { throw unimpl(); } };
    // Collect unresolved calls, and verify they get resolved.
    Work ambi = new Work("Ambi",false) { @Override public Node apply(Node n) { throw unimpl(); } };

    // Set all values to ALL and lives to DEAD, their most optimistic types.
    // Set all type-vars to Leafs.
    Env.START.walk_initype(work);
    assert Env.START.more_flow(work,false)==0; // Initial conditions are correct

    // Repeat, if we remove some ambiguous choices, and keep falling until the
    // graph stabilizes without ambiguity.
    int cnt=0;                  // Debug counter
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
      while( !ambi.isEmpty() )
        ambi.pop().remove_ambi(work);
    }

    assert Env.START.more_flow(work,false)==0; // Final conditions are correct
    Env.START.walk_opt(new VBitSet());
  }
}
