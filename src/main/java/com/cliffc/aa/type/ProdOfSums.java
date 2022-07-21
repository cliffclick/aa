package com.cliffc.aa.type;

import com.cliffc.aa.util.*;

import java.util.*;

import static com.cliffc.aa.AA.unimpl;

// Product of Sums of BitsFun.

// Sum     == choice/OR/JOIN
// Product == must/AND/MEET

// Goal: support function overloads.
// Normal, non-overload example: [14,15] === One of functions 14,15, can't tell which one.
// Overload example: [20+21] == Choice/overload of functions 20,21.  H-M must resolve or ambiguous.

// Example: "(pred ? _+_ : _*_)(X,Y)".  Depending on predicate either choice of
// ADD or choice of MUL.  Choice is resolved by X,Y being INT or FLT.
// ADD: [20+21].  MUL: [18+19].  Product of sums: [20+21],[18+19]
//
// Normal case, with no overloads and low/meet FIDXs is a single low BitsFun.
// Overload case includes more BitsFun which are HIGH.

public class ProdOfSums {

  private static final HashMap<ProdOfSums,ProdOfSums> INTERN = new HashMap<>();
  private static ProdOfSums FREE=null;
  public static final ProdOfSums EMPTY = make(BitsFun.EMPTY);
  public static final ProdOfSums NALL = make(BitsFun.NALL);

  public BitsFun _fidxs;   // Normal, low fidxs only (or dual)
  public BitsFun[] _overs; // Overloads, high fidxs only (or dual).  Typically zero-length.
  int _hash;               // Pre-computed hash
  private ProdOfSums() {}

  // Initialize a free one
  private ProdOfSums init(BitsFun fidxs, BitsFun[] overs) {
    assert check(fidxs,overs);
    _fidxs = fidxs;
    _overs = overs;
    _hash = compute_hash();
    return this;
  }
  private static boolean check(BitsFun fidxs, BitsFun[] overs) {
    assert !fidxs.test(0);      // Nil handling elsewhere
    assert fidxs!=BitsFun.NALL || overs.length==0; // Full means no choices
    // overloads are already interned
    assert BitsFuns.interned(overs);
    // overloads are opposite parity from normals
    for( BitsFun over : overs )
      assert (fidxs.is_empty() || (over.above_center() != fidxs.above_center())) && !over.is_empty();
    // No overlaps on overloads
    for( BitsFun over : overs ) {
      assert !over.overlaps(fidxs);
      for( BitsFun over2 : overs )
        assert over2==over || !over.overlaps(over2);
    }
    // Overloads are sorted
    BitsFun prior=null;
    for( BitsFun over : overs )
      if( prior==null ) prior=over;
      else { assert prior.compareTo(over) <0; prior=over; }
    return true;
  }
  int compute_hash() { return _fidxs._hash^BitsFuns.compute_hash(_overs); }
  @Override public int hashCode( ) { return _hash; }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof ProdOfSums ps) ) return false;
    return _fidxs==ps._fidxs && _overs==ps._overs;
  }    
 
  // Make with full arguments, including hash-cons intern step
  public static ProdOfSums make(BitsFun fidxs, BitsFun[] overs) {
    ProdOfSums ps = FREE;
    if( ps == null ) ps = new ProdOfSums();
    else FREE = null;
    ProdOfSums ps2 = INTERN.get(ps.init(fidxs,overs));
    if( ps2 != null ) { FREE = ps; return ps2; }
    else { INTERN.put(ps,ps); return ps; }
  }
  public static ProdOfSums make(BitsFun fidxs) { return make(fidxs,BitsFuns.EMPTY); }
  public static ProdOfSums make(int fidx) { return make(BitsFun.make0(fidx),BitsFuns.EMPTY); }

  @Override public String toString() { return str(new SB()).toString(); }
  public SB str(SB sb) {
    _fidxs.str(sb);
    for( BitsFun over : _overs )
      over.str(sb.p(_fidxs.above_center()?'+':'&'));
    return sb;
  }  
  
  public ProdOfSums dual() { return make(_fidxs.dual(),BitsFuns.dual(_overs)); }

  public ProdOfSums meet( ProdOfSums pos ) {
    if( this==pos ) return this; // Shortcut
    BitsFun fidxs = _fidxs.meet(pos._fidxs);
    BitsFun[] iovers = _overs, jovers = pos._overs;
    int ilen = iovers.length, jlen = jovers.length;
    if( ilen>0 || jlen>0 ) {
      BitsFun[] kovers = BitsFuns.get(ilen + jlen);
      int i=0, j=0, k=0;
      while( i<ilen || j<jlen ) {
        int cmp = i==ilen ? 1
          : (j==jlen ? -1
             : (iovers[i].compareTo(jovers[j])));
        kovers[k++] = cmp<=0 ? iovers[i++] : jovers[j++];
        if( cmp==0 ) j++;
        if( fidxs.overlaps(kovers[k-1]) )
          k--;          // No real choices; must pick the low value in any case
      }
      if( k!=kovers.length )
        { iovers = BitsFuns.copyOf(kovers,k); BitsFuns.free(kovers); kovers=iovers; }
      iovers = BitsFuns.hash_cons(kovers);
    }
    return make(fidxs,iovers);
  }

  public BitsFun overload( ) {
    BitsFun fidxs = _fidxs;
    assert !fidxs.above_center();
    fidxs = fidxs.dual();
    for( BitsFun overs : _overs ) {
      assert overs.above_center();
      fidxs = (BitsFun)fidxs.join(overs);
    }
    return fidxs;
  }
  
  public boolean overlaps( ProdOfSums pos ) {
    if( this==pos && !is_empty() ) return true;
    assert _overs.length==0;    // TODO: what does this mean
    return _fidxs.overlaps(pos._fidxs);
  }
  
  public boolean above_center( ) {
    return (_fidxs.is_empty() && _overs.length>0 && _overs[0].above_center() ) || _fidxs.above_center();
  }

  public boolean test(int fidx) { return _fidxs.test_recur(fidx); }
  public ProdOfSums clear(int fidx) {
    if( !_fidxs.test(fidx) ) return this;
    throw unimpl();
  }

  public boolean is_fidx() { return _fidxs.abit() > 1; } // Single-bit
  public int fidx() { return _fidxs.getbit(); } // Single-bit
  public boolean is_empty() { return _fidxs.is_empty() && _overs.length==0; }
  public boolean is_full() { return _fidxs==BitsFun.NALL; }
}
