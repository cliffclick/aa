package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.*;

// Load a struct from memory.  Does its own nil-check testing.  Display/Frames
// are normal structs, so local vars are ALSO normal struct loads.

//"x.y"
// Op     Adr   Value
// Load.y ptr   field
// Bind   ptr   bound lambda, or original field
//
//"1._+_._"
// Op       Adr   Value
// Load._+.  1    (unbound function choices from INT CLZ)
// Bind      1    (  bound function choices)
// Load._   ts       bound function
// Bind     ts       bound function --since ptr is TypeStruct, no-op

//"1+2"
// Load._+_  1    (unbound function choices)
// Bind      1       bound function

/*
#- Kill dead code, remove RESOLVING, RESOLVABLE
#- No need for Fresh on pending resolves
#- DynLoad gets pattern -> label mappings
#- - mappings will start null/missing
#- - mappings are added over time (monotonic)
#- - patterns are added over time
#- - patterns can unify with each other, or some other pattern
#- - mappings can go to 2+ labels; this is a ambiguous error
#- - As labels appear on mapping RHS, value call starts MEET over those fields

Took a walk, need to go back & keep much of this infra:
- TVStruct needs a resolving/resolved list (or at least resolving).
- - This is so we keep picking up constraints on Dyn/Fresh pairs.
- Resolvable has Dyn/Fresh/Pat/Label
- Unify merges based on (Dyn/Fresh); merged labels can get more than 1, this is
  an error.  Merged pats just unify also; this is just merging many uses of the
  same field (which isn't known yet).
- Fresh copies the (Dyn/Fresh) with a Fresh Pat & same labels.
- Keep a global list of Resolving/Resolveds as before.
- Incremental: could track all Pat & Struct children & re-resolve.  Or keep my
  current stupid global state.

- More thots: why only 1 Fresh?
- Indeed my latest big test case has 2 Freshes on purpose.
- I think I need a DynLoad plus a *lexical path* of Freshes.  A dynamic path is
  death.  A lexical path gives an exponential set of chocies, which jives with
  my vague notion that worse-case HM types go exponential.
- Or maybe its just a Pattern (unique along a path anyways) maps to an offset.

- So at the DynLoad itself, it does a runtime dynamic mapping from the dict
  that comes with the TVStruct.  That is, every TVStruct producer also
  produces a dictionary mapping Dyn->label.
- Every TVStruct has a Dyn->label mapping.  The mapping starts unknown
  but includes a pattern.
- Unify two TVStructs unifies their Dyn mappings.
- Updating a TVStruct fields (via unify) can re-check the dyn mappings?
- No error if we can force a Dyn into a single label - all TVStructs
  seeing the same Dyn->Label mapping.
- Where we cannot, the Dyn is *dynamic* and needs another input - the mapping from dyn to label.
- - This Dyn is not broken, just *dynamic*
- Fresh just clones the TVStruct including Dyn labels.
- At some outer levels, the TVStruct dyn mappings do get mapped to a label.
- Multiple YES mappings are errors.
- Multiple maybes just delay.
- During Unify (and Fresh-Unify), if progress comes from a TVStruct innards, we can re-check its Dyn mappings
- Still open Q: when is ambiguous error?

Brings me to a TVDyn -> TVStruct, TVDyn has the field type, and "resolves" when it can.
Every function takes as hidden extra args, all the TVDyn ever mentioned.  This is similar to a typeclass dictionary?
Callers unify with a hidden extra arg dyn->struct.

In my stacked TestParse case, mapping lookups are stacked
foo = { x y ->
        ( { x y -> !x * !y },
          { x y -> !x *  y.sin(3.14) },
          { x y -> x.sin(3.14) * !y },
          { x y -> x.sin(3.14) *  y.sin(3.14) }
  )._(x,y)
};
baz = { x -> math.rand(2) ? foo(x,2) : foo(x,2.2) };
bar = {   -> math.rand(2) ? baz(  3) : baz  (3.3) };
bar()

Foo returns a [dyn -> (0:,1:,2:,3:)] mapping
So foo gets type { x y [dyn -> (0:,1:,2:,3:)] -> dyn } // where the dyn-> TVDyn type becomes the final result once resolved
So for `baz = { x -> math.rand(2) ? foo(x,2) : foo(x,2.2) };`
each of the foo calls passes in a different table:
  foo(x,2  ,A:[dyn -> (0:,2:)]) with a fresh dyn result
  foo(x,2.2,B:[dyn -> (1:,3:)]) with a fresh dyn result
So baz type { x [A,B] -> dyn }
And finally bar


Another thought: any given Fresh uniquely identifies a unique lexical path, but
this isn't neccesarily how the code execution arrives at the Dyn.

So theory:
TVStruct carries Dyn->pattern mapping, with the label if resolved.
Unify TVStruct unified patterns for same Dyn.  This can pats go to multi-Yes (ambiguous).
Fresh adds a Fresh in front of the existing mappings; can nest Freshes then?
Or the pattern is [Dyn,Fresh... in any order, no dups] -> Pat/Label.
So map TVStruct carries { UQNodes -> Pattern }.

 */


public class DynLoadNode extends Node {

  // Where to report errors
  private final Parse _bad;

  // Mapping from [dynload,fresh(s)] to a field pattern.
  private final Ary<Resolvable> _resolves;
  
  public DynLoadNode( Node mem, Node adr, Parse bad ) {
    super(null,mem,adr);
    _bad = bad;
    _resolves = new Ary<>(Resolvable.class);
  }

  @Override public String label() { return "._"; }   // Self short name
  
  public Node mem() { return in(MEM_IDX); }
  public Node adr() { return in(DSP_IDX); }
  
  @Override public Type value() {
    Type tadr = adr()._val;
    Type tmem = mem()._val;

    if( !(tadr instanceof TypeNil ta) || (tadr instanceof TypeFunPtr) )
      return tadr.oob(); // Not an address
    if( !(tmem instanceof TypeMem tm) )
      return tmem.oob(); // Not a memory

    if( ta==TypeNil.NIL || ta==TypeNil.XNIL )
      ta = (TypeNil)ta.meet(PrimNode.PINT._val);
    if( !(ta instanceof TypeMemPtr tmp) )
      return TypeNil.SCALAR.oob(ta);

    // Set of fields being picked over
    TypeStruct ts = tmp.is_simple_ptr() ? tm.ld(ta) : tmp._obj;

    // Still resolving, dunno which field yet
    if( Combo.pre() ) {
      Type t = ts._def;
      for( TypeFld tf : ts ) {
        Type q = tf._t;
        if( tf._t instanceof TypeMemPtr tmp2 && tmp2.is_simple_ptr() )
          q = tmp2.make_from(tm.ld(tmp2));
        t = t.meet(q);
      }
      return t;
    }
    
    // Meet over all possible choices.  This DynLoad might have resolved
    // differently with different TV3s from different paths, so meet over all
    // possible choices.
    Type t = TypeNil.XSCALAR;
    for( Resolvable r : _resolves )
      if( r._label != null )
        t = t.meet(LoadNode.lookup(ts,tmp,tm,r._label));
    return t;
  }

  
  // The only memory required here is what is needed to support the Load.
  // If the Load is alive, so is the address.
  @Override public Type live_use( int i ) {
    //assert _live==Type.ALL;
    Type adr = adr()._val;
    // Since the Load is alive, the address is alive
    if( i!=MEM_IDX ) return Type.ALL;
    // Memory demands
    Node def = mem();
    if( adr.above_center() ) return Type.ANY; // Nothing is demanded
    if( !(adr instanceof TypeNil ptr) )  // Demand everything not killed at this field
      return RootNode.defMem(def);
  
    if( ptr._aliases.is_empty() )  return Type.ANY; // Nothing is demanded still

    // Demand memory produce the desired field from a struct
    if( ptr._aliases==BitsAlias.NALL )
      return RootNode.defMem(def);
    // All fields are live
    return TypeMem.make(ptr._aliases,TypeStruct.ISUSED);
  }

  @Override public Node ideal_reduce() {
    for( Resolvable r : _resolves ) {
      assert r._dyn==this;
      if( r._path.size()==1 ) {
        assert _resolves._len==1;
        if( r._label!=null )
          return new LoadNode(mem(),adr(),r._label,_bad).peep().setLive(_live);
      }
    }
    return null;
  }

  // No matches to pattern (no YESes, no MAYBEs).  Empty patterns might have no NOs.
  public boolean resolve_failed_no_match( TV3 pattern, TVStruct rhs, boolean test ) {
    throw TODO();
  }
  
  @Override public boolean has_tvar() { return true; }
  @Override public TV3 _set_tvar() {
    // Load takes a pointer
    TV3 ptr0 = adr().set_tvar();
    TVPtr ptr;
    if( ptr0 instanceof TVPtr ptr1 ) ptr = ptr1;
    else ptr0.unify(ptr = new TVPtr(BitsAlias.EMPTY, new TVStruct(true) ),false);
    _tvar = new TVLeaf();
    Resolvable r = new Resolvable(this,UQNodes.make(this),ptr.load(),_tvar);
    assert _resolves.isEmpty();
    _resolves.push(r);
    return _tvar;
  }

  @Override public boolean unify( boolean test ) {
    boolean progress = false;
    for( Resolvable r : _resolves ) {
      progress |= r.trial_resolve(test);
      if( progress && test ) return true;
    }
    return progress;
  }
  
}
