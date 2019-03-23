package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

// CNC notes-

// Tuples are not memory, just a collection.

// TypeMem has an Alias and a Named Struct (name is optional).  Structs ARE
// memory and list the known fields and contents.

// NewNode produces both a memory and a pointer.

// Example:  x = @{ a:=1, b:='abc'};
// 'x' is a pointer-to-mem-alias-X.
// Mem-alias X is exactly @{ a:=1, b:='abc' };
// Example: x.a
//   Load(X,x,.a) -- Mem-alias X, ptr 'x', field '.a'.  This is c-fold to a '1'.
// Example: foo(); x.a;
//   Here memory is merged & aliased, so the mem-alias from foo() is wide.
//   Load(WIDE,x,.a) -- wide-alias can split out a 'widened' version of mem-alias-X
//   This has value type of 'real' (since '1' can widen to either int or float).
// NO - use the value of mem-alias-X from the Call return.  Calls merge memory at
//   function head, and produce it out.  Assume foo() updates mem-alias-X.
// Example: x.b:='def'
//   This updates mem-alias-X from @{a:=2,b:='abc'} to @{a:=2,b:='def'}

// Aliases have a heirarchy of at least 3- "all" of memory, "all" of a Named-
// Struct type, and a specific allocation site.  In the past, have looked at
// negative alias types (all minus X), and also complete splits.  Did complete
// splits with alias bits, and the infinite-bit set (see Bits.java).

// Look at: No merging of discrete bits into a "fat" memory and then splitting
// it apart - because the merge into "fat" will lose precision.  Just keep it
// split always? - except at program entry/exit?  Whole-program issues: need to
// look at approximations to keep size in check.  Maybe: unrelated fcns keep
// unrelated memory fat - which means split-around a Call site (same as Cntrl)
// many-skinny flow around a Call - and the call contents are not messing with
// the external memory.
//
// Gets into Call signatures for memory - untouched memory, read-only memory,
// r/w memory, freed vs borrowed memory, etc.

// Types: TypeMem has sub-types for every alias, and generically TypeMem for
// bulk (non-aliased).  Not allowed to Load/Store from Bulk memory (approx
// issues).  So TypeMem e.g. an array indexed by Alias#, or a HashTable indexed
// by Alias# for very sparse.  Use an accessor and change impl as needed.  So
// has a list of specific Alias#s.  Also needs a list of "fat" alias#s, which
// can be the inverted bitvector.  Again, use accessor and change impl.  Will
// need to support a Merge operation (allowed on a 2 mid-tier or a mid-tier and
// a NewNode alias).
//
// Need a TypePtr which has a mid-tier and a new-node specific alias.  There
// can be a "allptr" pointing to "all", but maybe there's only 1 (like type
// Scalar it has no shape or content).
//
// Can be many "tiers" in the heirarchy, as there are Names in the Types.
// NewNode is basically a named subtype of its result type.
//
// Action items:
//
// - An assert that walks the entire graph, and ensures no duplicate memory
//   aliases in any program slice.
//-  NewNode tracks unique memory aliases, same as CallNode for RPCs.
// - A TypePtr has a Bits of memory aliases
// - A TypeMem has a mapping from every alias to a Type
// - NewNode produces a TypeMem with 1 alias to a e.g. Struct and a TypePtr.
// - StartNode produces a empty TypeMem.
// - TypeMem supports merging TypeMems with unrelated aliases.  Error to merge
//   same alias.
// - Load & Store take in a TypeMem & a TypePtr.  TypeMem can be "fat" with many
//   aliases but the TypePtr can only be mid-tier "fat".
// - Calls take in a TypeMem and can update all Aliases in the TypeMem's
//   subtypes.  Calls can be more strongly user-typed to limit r/w aliases -
//   but in any case the gvn.opto will discover the minimal update set.
// - Phi keeps mem types fully alias precise unless TypePtrs are also becoming
//   imprecise?  No need to ever get approx?
//-----
// More thinking:
//
// Keep OOP as parent of Str,Struct,Array.  These are memory-content values.
// TypeMem is a collection of OOPs, indexed into Alias sets.
// TypeMemPtr is a collection of Alias#s.





// Merging 'wide' memory (memory from all prior state) and a new 'skinny'
// memory from a NewNode.
public class MergeMemNode extends Node {
  public MergeMemNode( Node wide, Node skinny ) { super(OP_MERGE,wide,skinny); }
  
  @Override public Node ideal(GVNGCM gvn) {
    // If the skinny memory is from a MProj from a NewNode, and the only proj
    // is the MProj, then there is no *address* user, and the New object must
    // be dead.  Remove the New.
    if( in(1) instanceof MProjNode &&
        in(1).in(0) instanceof NewNode &&
        in(1).in(0)._uses._len==1 )
      return in(0);             // Skinny memory is dead, nothing to merge
    return null;
  }

  @Override public Type value(GVNGCM gvn) { return TypeMem.MEM; }
  @Override public Type all_type() { return TypeMem.MEM; }
}

