package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.Util;

import java.util.HashMap;
import java.util.Iterator;

import static com.cliffc.aa.AA.unimpl;

/**
   A sub-set of the powerset of all bits.  
   This is a lattice using trivial set inclusion.

   This is a sum-of-products form.  Each term is a product, and the collection
   of terms are summed.  Example terms:
     {ABc} === (A *  B * !C)
     {Abc} === (A * !B * !C)
   And the sum-of-products:
     {ABc,Abc} == (A *  B * !C) + (A * !B * !C)
   Here 'A' is in both terms, so 'A' is present.
   Here both 'B' and 'b' appear, so B is a Don't-Care term.
   Here 'c' is in both terms, so 'C' is absent.
   Adding terms increases the set of choices, and removing lowers.  Hence
   MEET is intersection (fewer terms) and JOIN is union.

   All-bits-set is a single term, {ABC...Z...}.
   All-bits-clr is a single term, {abc...z...}.
   No terms is some kind of error situation.
   A constant 'A' term will have all other bits be Don't-Care - which means
   they appear in all combinations:
       {Abc,ABc,AbC,ABC}  // the constant 'A', b and c in all 4 combos
       {aBc,ABc,aBC,ABC}  // the constant 'B', a and c in all 4 combos
   A MEET of constants A and B would be:
       {    ABc,    ABC}  // always 'A' and 'B', c in both combos
   A JOIN of constants A and B would be:
       {Abc,ABc,AbC,ABC,aBc,aBC} // 6 terms
   Suppose the above JOIN comes from an Overload/Unresolved, and this is then
   mixed in a Phi with a constant 'C'.  The end result is:
       {        AbC,ABC,    aBC} // 3 terms

   Only certain subsets are efficiently represented, although all subsets can
   be represented in some way.  See 
     https://en.wikipedia.org/wiki/Espresso_heuristic_logic_minimizer
   for a well understood and reasonably efficient way to represent subsets.

   Supports printing, union, intersection, creation from simple bit sets.
   All instances are interned, and pointer-equality is equality.

 */
public class PowerSet<B extends PowerSet<B>> implements Iterable<Integer> {

  static final byte OFF=1,ON=2,DC=3; // On,off, and Dont'-Care
  byte _etc;                         // All the other bits
  // All bits are renamed to a dense set, in numeric order. '0' is allowed for nil.
  short[] _bits;                // Rename the bits to dense 0,1,2,...

  // Dense bitset for the PowerSet.  Support for _bits of length 6 in a single
  // long.  Number of explicit bits is 2^_bits.length; the remaining (infinite)
  // bits come from _etc.
  long _pset;                   // Dense bitset for the PowerSet
  
  
  // Intern: lookup and return an existing Bits or install in hashmap and
  // return a new Bits.  Overridden in subclasses to make type-specific Bits.
  private static final HashMap<PowerSet,PowerSet> INTERN = new HashMap<>();
  private static PowerSet FREE=null;
  private static PowerSet malloc(byte etc, short[] bits, long pset ) {
    PowerSet b1 = FREE;
    if( b1 == null ) b1 = new PowerSet();
    else FREE = null;
    return b1.init(etc,bits,pset);
  }
  private PowerSet hash_cons_free() {
    assert check();
    PowerSet ps = INTERN.get(this);
    if( ps != null ) {
      assert FREE==null; // time for a linked list
      FREE = this;
      return ps;
    }
    INTERN.put(this,this);
    return this;
  }

  // Common init
  PowerSet init(byte etc, short[] bits, long pset ) {
    _etc =etc;
    _bits=bits;
    _pset=pset;
    Util.add_hash(etc);
    Util.add_hash(pset);
    for( int i : _bits ) Util.add_hash(i);
    long hash = Util.get_hash();
    _hash = (int)((hash>>32)+hash);
    return this;
  }

  // Check invariants
  private boolean check() {
    if( _bits.length>6 ) return false; // Requires pset be an array of longs
    // Check cannot move any bits into etc
    if( _bits.length!=1 ) return false; // Requires a better check
    
    if( _etc==ON  && _pset==0b01 ) return false; // Single bit is always ON , which matches etc
    if( _etc==OFF && _pset==0b10 ) return false; // Single bit is always OFF, which matches etc
    if( _etc==DC  && _pset==0b11 ) return false; // Single bit is DC, which matches etc
    
    return true;
  }


  // Make a PowerSet with a single bit
  static public PowerSet make(int bit) { return malloc(DC,new short[]{(short)bit},0b01).hash_cons_free(); }

  // Internal: make a new PowerSet with merged _bits; it may not be canonical
  // and is not interned, and can be directly edited.
  private PowerSet make_from_bits( PowerSet ps ) {
    PowerSet xps = malloc(_etc,_bits,_pset);
    xps._bits = Util.merge_sort(_bits,ps._bits);
    // rename 


    
    throw unimpl();
    // xps._etc = _etc | ps._etc; // TODO: NOPE.... an ALL plus a NONE is not a DONT-CARE
  }

  
  // Union/OR
  public PowerSet OR( PowerSet ps ) {
    // Make a not-interned editable PS from 'this' with a merged set of '_bits'.
    PowerSet xps = make_from_bits(ps);
      
    throw unimpl();
  }

  // Intersection/AND
  public PowerSet AND(PowerSet ps) {
    throw unimpl();
  }

  @Override public Iterator<Integer> iterator() {
    throw unimpl();
  }

  // Pre-computed hashcode
  int _hash;
  @Override public int hashCode( ) { return _hash; }
  // Hard equality, used for interning
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof PowerSet ps) ) return false;
    if( _hash != ps._hash ) return false;
    throw unimpl();
  }

  // toString for default debug printing
  @Override public String toString() { return str(new SB()).toString(); }
  public SB str(SB sb) {

    if( _bits.length!=1 ) throw unimpl(); // Needs a better str

    if( _etc==DC ) {
      if( _pset==0b01 ) return sb.p("[" ).p(_bits[0]).p("]");
      if( _pset==0b10 ) return sb.p("[~").p(_bits[0]).p("]");
      throw unimpl();
    }
    
    
    throw unimpl();
  }
  
}
