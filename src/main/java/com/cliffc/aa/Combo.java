package com.cliffc.aa;

import com.cliffc.aa.node.*;
import com.cliffc.aa.tvar.Resolvable;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.NonBlockingHashMapLong;

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
functions can be executed for side effects only and return a progress flag.
The transfer functions are virtual calls on Nodes, similar to the existing
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
mean "actually unify and report a progress" vs "report if progress".  The
report-only mode is aggressively asserted for; all Nodes that can make progress
are asserted as on the worklist.

==============================================================================

Global Optimistic Constant Propagation is treated as the usual Monotone
Analysis Framework.  Passed in the parsed program state (including any return
result, i/o and memory state).  Returns the most-precise types possible, and
replaces computed constants with constant nodes.  GCP types are computed using
the virtual value() call, which computes a new type from the node neighbors
without reference to the old type.  value()has no side-effects.

Besides the obvious GCP algorithm (and the type-precision that results from the
analysis), GCP does a few more things:

GCP builds an explicit Call-Graph.  Before GCP not all callers are known and
this is approximated by being called by a ScopeNode as a permanently available
unknown caller.  If the whole program is available to us then we can compute
all callers conservatively and fairly precisely - we may have extra never-taken
caller/callee edges, but no missing caller/callee edges.  These edges are
virtual before GCP.  During GCP we discover most paths are dead, and we add in
physical CG edges as possible calls are discovered.

GCP discovers functions which escape at the top-most level, and wires the
RetNode to the top-most Scope to mimic future unknown callers.

==============================================================================

Global Optimistic Liveness is also computed.  This is the reverse version of
GCP, treated as the usual Monotone Analysis Framework.  Liveness is precise
through memory, tracking in-use aliases and fields of structures.  Similar to
GCP, liveness is computed using a virtual live() call - which typically uses
the default version.  Each live-use edge is checked with a virtual live_use
call, which is typically overloaded for every Node.

==============================================================================

The combined algorithm includes transfer functions taking facts from one MAF
lattice and produces results in some other MAF lattice.

For the GCP->HM direction, the HM IfNode has a custom transfer function instead
of the usual one.  Unification looks at the GCP predicate value, and unifies
either the true arm, or the false arm, or both or neither.  In this way GCP
allows HM to avoid picking up constraints from dead code.

Also for GCP->HM, the HM CallNode has a custom transfer function instead of the
usual one.  Unification looks at the GCP function type, and unifies against
reachable functions instead of all of them.  Similar to HM IfNode unification,
HM avoids picking up constraints from calls not in the Call Graph.

Also for GCP->HM, the HM ground terms or base terms include anything from the
GCP lattice, instead of just the usual int/float/datum/string set.

For the HM->GCP direction, the GCP CallEpi has a customer transfer function
where the result from a call gets lifted (JOINed) based on the matching GCP
inputs - and the match comes from using the same HM type-var on both inputs and
outputs.  This allows e.g. "map" calls which typically merge many GCP values at
many call sites and thus end up typed as a Scalar to Scalar, to improve the GCP
type on a per-call-site basis.

Also for the HM->GCP direction, HM is used to lift external calls to escaped
functions.  This probably needs more explanation: Functions which do not
escape the borders of the compilation unit are treated as private, and all
their callers are known (the Call Graph is found by GCP as explained above).
Functions which DO escape are treated "as-if" called by an unknown caller with
the most conservative possible arguments; e.g. exposed module entry points, or
functions defined in the REPL and yet to be called by a future REPL entry.
Without HM, GCP assumes an external caller calls with Scalar arguments (and
memory filled with Scalars); with HM the GCP inputs are lifted to the HM
structural types.

Also for the HM->GCP direction, loads from external pointers are lifted.  The
HM-required memory structure is not reflected in the external memory, nor does
GCP have the external alias numbers.

For the Live->HM direction, dead Nodes do not unify hence do not force structure
on the HM variables.

For the GCP->Live direction, Nodes which (may) compute a constant do not need
their inputs, and so their inputs are treated as dead.

==============================================================================

 */
public abstract class Combo {
  public static boolean HM_NEW_LEAF;   // After 1st pass, potential HM new leafs will no longer lift Apply results
  public static boolean HM_AMBI;       // After 2nd pass, unresolved Fields are ambiguous
  public static boolean HM_FREEZE;     // After 3rd pass, HM types are frozen but GCP types continue to fall
  // After Combo has run, the Call Graph is built.  All Calls are wired and all
  // Rets explicitly know their callers.  Several approximations are waiting
  // for Combo to start or finish.
  public static boolean pre   () { return  AA.LIFTING && !HM_FREEZE; }
  public static boolean during() { return !AA.LIFTING              ; }
  public static boolean post  () { return  AA.LIFTING &&  HM_FREEZE; }

  public static void opto() {
    assert !PrimNode.post_init() || Env.GVN.work_is_clear();
    // This pass LIFTS not FALLs
    AA.LIFTING = false;

    // Set all values to ANY and lives to DEAD, their most optimistic types.
    // Set all type-vars to Leafs.
    RootNode.combo_def_mem();
    Env.KEEP_ALIVE.walk( (n,ignore) -> {
        if( n.is_prim() ) return 0;
        n._val = n._live = Type.ANY;  // Highest value
        if( n.has_tvar() ) n.set_tvar();
        n.add_flow();
        if( n instanceof FunNode fun && !n.always_prim() )
          fun.set_unknown_callers();
        return 0;
      });
    assert Env.KEEP_ALIVE.more_work()==0; // Initial conditions are correct

    // Init
    HM_NEW_LEAF = false;
    HM_AMBI     = false;
    HM_FREEZE   = false;
    int work_cnt=0;

    // Pass 1: Everything starts high/top/leaf and falls; escaping function args are assumed high
    work_cnt += main_work_loop(1);

    // Pass 2: Potential new Leafs quit lifting GCP in Apply
    add_new_leaf_work();
    assert Env.KEEP_ALIVE.more_work()==0;
    work_cnt += main_work_loop(2);

    // Pass 3: Unresolved Fields are ambiguous; propagate errors
    HM_AMBI = true;
    add_ambi_work();
    assert Env.KEEP_ALIVE.more_work()==0;
    work_cnt += main_work_loop(3);

    // Pass 4: H-M types freeze, escaping function args are assumed called with lowest H-M compatible
    // GCP types continue to run downhill.
    HM_FREEZE = true;
    add_freeze_work();
    assert Env.KEEP_ALIVE.more_work()==0;
    work_cnt += main_work_loop(4);

    // Take advantage of results
    Env.KEEP_ALIVE.walk( (n,ignore) -> {
        Env.GVN.add_work_new(n);
        return 0;
      });
  }

  static int main_work_loop( int pass ) {

    int cnt=0;                  // Debug counter

    // Analysis phase.
    // Work down list until all reachable nodes types quit falling
    Node n;
    while( (n=Env.GVN.pop_flow()) != null ) {
      cnt++; assert cnt < 20000; // Infinite loop check
      Type told = n._val;

      // Forwards flow
      n.combo_forwards();

      // Backwards flow
      n.combo_backwards();

      // H-M unification
      n.combo_unify();

      // During Combo value flow, the exact fcn pointers appear,
      // and we require wiring to make these edges explicit.
      if( told != n._val ) {
        if( n instanceof CallNode call ) call.cepi().CG_wire();
        if( n instanceof RootNode root ) root.CG_wire();
      }

      if( Env.GVN.flow_len()==0 && !Resolvable.RESOLVINGS.isEmpty() )
        for( Resolvable r : Resolvable.RESOLVINGS.values() )
          r.trial_resolve(false); // Do delayed resolve

      // Very expensive assert: everything that can make progress is on worklist
      assert Env.KEEP_ALIVE.more_work()==0;
    }
    return cnt;
  }

  private static void add_new_leaf_work() { }
  private static void add_ambi_work() {
    //for( Resolvable r : Resolvable.RESOLVINGS.values() )
    //  throw AA.unimpl();
  }

  private static final NonBlockingHashMapLong<Node> FREEZE_WORK = new NonBlockingHashMapLong<>();
  public static void add_freeze_dep( Node dep ) {
    FREEZE_WORK.put(dep._uid,dep);
  }
  private static void add_freeze_work()   {
    for( Node dep : FREEZE_WORK.values() )
      dep.add_flow();
    FREEZE_WORK.clear();
  }

  static void reset() { HM_NEW_LEAF = HM_AMBI = HM_FREEZE=false; FREEZE_WORK.clear(); }
}
