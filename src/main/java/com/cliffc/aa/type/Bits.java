package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;
import org.jetbrains.annotations.NotNull;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;

// Bits supporting a lattice; immutable; hash-cons'd.  Bits can be *split* in
// twain, are everywhere immediately updated (ala Smalltalk "becomes") to the
// pair.  To keep the hash-cons working, the hash code of the original and the
// pair are kept the same, but the "equals" call works as normal.
//
// Splitting is useful during e.g. inlining, where a single Call is duplicated
// and RPCs to the original one might return to either of of the inlines.  Same
// for internal functions and allocation sites - after the inline, pointers &
// references to the original might now refer to either copy.  Each copy only
// refers to itself, so after some optimizations the ambiguious bits can be
// optimized away.  i.e., its useful to make the distinction between the cloned
// instances, just might be some confusion at first.
//
// Bit 0 - is always the 'null' or 'empty' instance.
// Bit 1 - is the first "real" bit, and represents all-of-a-class.
// Other bits always split from bit 1, and can split in any pattern.
//
// Individual bits can be considered either constants (on the centerline) or a
// class of things that are either meet'd or join'd (above or below the
// centerline).  Aliases are usually classes because a single NewNode can be
// executed in a loop, producing many objects with the same alias#.  FIDXs and
// RPCs are always constants, as there is a single instance of a function or a
// return-point.  Code-cloning (i.e. inlining) splits the constant instantly
// into 2 new values which are both constants; i.e. single FIDX#s and RPC#s are
// never *classes*.
//
// Constant-or-class is on a per-bit basis, as some NewNodes are known to
// execute once (hence produce a constant alias class or a Singleton) and
// others execute many times.  This is handled by the subclasses; BitsAlias may
// track singletons at some future date.

public abstract class Bits<B extends Bits<B>> implements Iterable<Integer> {
  // Holds a set of bits meet'd together, or join'd together, along
  // with a single bit choice as a constant.
  // If _bits is NULL and _con is 0, this is nil and a constant.
  // If _bits is NULL, then _con is a single class bit and is +/- for
  // meet/join, OR "is_class()" is false and _con is a single constant.
  // If _bits is not-null, then _con is +1 for meet, and -1 for join.
  long[] _bits;   // Bits set or null for a single bit
  int _con;       // value of single bit
  int _hash;      // Pre-computed hashcode
  long[] _reset_bits;
  int _reset_con = -999999;
  // Intern: lookup and return an existing Bits or install in hashmap and
  // return a new Bits.  Overridden in subclasses to make type-specific Bits.
  abstract B make_impl(int con, long[] bits );
  abstract boolean is_class();    // All bits are constants or classes
  abstract HashMaker hashmaker(); // Hashcode maker, that handles split bits
  public abstract B ALL();
  public abstract B ANY();

  // Common init
  void init(int con, long[] bits ) {
    _con = con;
    _bits=bits;
    _hash=hashmaker().compute_hash(this);
    assert check();
  }
  private boolean check() {
    if( _bits==null ) return is_class() || _con >= 0; // Must be a single constant bit#
    if( _con != 1 && _con != -1 ) return false;
    if( _bits.length==0 ) return false;  // Empty bits replaced by a con
    if( _bits.length==1 && _bits[0]== 0) return true; // NO bits is OK
    if( _bits[_bits.length-1]==0 ) return false; // Array is "tight"
    // For efficiency, 1 bit set uses 'con' instead of 'bits'
    return check_multi_bits(_bits); // Found multiple bits
  }
  private static boolean check_multi_bits( long[] bits) {
    int len = bits.length;
    long b = bits[len-1];              // Last word
    if( (b & (b-1))!=0 ) return true; // Last word has multiple bits
    // Check multiple bits spread over multiple words
    for( int i=0; i<len-1; i++ ) if( bits[i] != 0 ) return true;
    return false;                // Found a single bit in last word
  }
  @Override public int hashCode( ) { return _hash; }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof Bits) ) return false;
    Bits bs = (Bits)o;
    if( _con != bs._con || _hash != bs._hash ) return false;
    if( _bits == bs._bits ) return true;
    if( _bits ==null || bs._bits==null ) return false;
    if( _bits.length != bs._bits.length ) return false;
    for( int i=0; i<_bits.length; i++ )
      if( _bits[i]!=bs._bits[i] ) return false;
    return true;
  }
  @Override public String toString() { return toString(new SB()).toString(); }
  public SB toString(SB sb) {
    if( this==ALL() ) return sb.p("[ALL]");
    if( this==ANY() ) return sb.p("[~ALL]");
    sb.p('[');
    if( above_center() ) sb.p('~');
    if( _bits==null ) sb.p(Math.abs(_con));
    else {
      for( Integer idx : this ) sb.p(idx).p(above_center()?'+':',');
    }
    return sb.p(']');
  }

  // Constructor taking an array of bits, and allowing join/meet selection.
  // Canonicalizes the bits.  The 'this' pointer is only used to clone the class.
  final B make( boolean any, long[] bits ) {
    // Remove any trailing empty words
    int len = bits.length;
    while( len > 1 && bits[len-1]==0 ) len--;
    if( bits.length != len ) bits = Arrays.copyOf(bits,len);
    
    // Check for a single bit or NO bits
    if( check_multi_bits(bits) || (len==1 && bits[0]==0) ) return make_impl(any ? -1 : 1,bits);
    int bnum0 = 63 - Long.numberOfLeadingZeros(bits[len-1]);
    int bnum = bnum0 + ((len-1)<<6);
    if( any && is_class() ) bnum = -bnum;
    return make_impl(bnum,null);
  }
  // Constructor taking a single bit
  final B make( int bit ) { return make_impl(bit,null); }
  // Constructor taking an array of bits
  public final B make( int... bits ) {
    int max= -1;                // Find max bit
    for( int bit : bits ) max=Math.max(max,bit);
    long[] ls = bits(0,max);  // Big enuf bits
    for( int bit : bits ) or(ls,bit);
    return make(false,ls);
  }

  private static int  idx (long i) { return (int)(i>>6); }
  private static long mask(long i) { return 1L<<(i&63); }
  
  int getbit() { assert _bits==null; return _con; }
  public int abit() { return _bits==null ? _con : -1; }
  public boolean above_center() { return _con<0; }
  boolean may_nil() { return _con==0 || (_con==-1 && ((_bits[0]&1) == 1)); }
  // Add a nil
  @SuppressWarnings("unchecked")
  B meet_nil() {
    if( _con==0 ) return (B)this;// Already a nil constant
    long[] bs = _bits;
    if( bs==null )              // Is a single compressed bit
      or(bs = bits(0,Math.abs(_con)),Math.abs(_con)); // Decompress single bit into array
    else bs = _bits.clone();    // Make a private set
    bs[0] |= 1;                 // Set nil
    return make(false,bs);
  }

  // Test a specific bit is set or clear on a given bits
  private static boolean test(long[] bits, int i) { return (bits[idx(i)]&mask(i))!=0; }
  // Test a specific bit is set or clear on this Bits
  public boolean test(int i) {
    if( _bits==null ) return i==Math.abs(_con);
    int idx = idx(i);
    return idx < _bits.length && test(_bits, i);
  }

  // Return the type without a nil-choice.  Only applies to above_center types,
  // as these are the only types with a nil-choice.  Only called during meets
  // with above-center types.  If called with below-center, there is no
  // nil-choice (might be a must-nil but not a choice-nil), so can return this.
  @SuppressWarnings("unchecked")
  B not_nil() {
    assert _con != 0; // cannot remove nil from nil?
    if( _con != -1 || _bits == null ) return (B)this; // Below or at center
    if( !test(_bits,0) ) return (B)this; // No nil choice
    long[] bs = _bits.clone();           // Keep all other bits
    and(bs,0);                           // remove nil choice
    return make(true,bs);                // Choices without nil
  }
  
  private static int max( long[] bits ) { return (bits.length<<6)-1; }
  private static void or ( long[] bits, long con ) { bits[idx(con)] |=  mask(con); }
  private static void and( long[] bits, long con ) { bits[idx(con)] &= ~mask(con); }
  private static long[] bits( int a, int b ) { return new long[idx(Math.max(a,b))+1]; }
  int max( ) {
    return _bits==null ? _con : (63 - Long.numberOfLeadingZeros(_bits[_bits.length-1]))+((_bits.length-1)<<6);
  }

  @SuppressWarnings("unchecked")
  public B meet( B bs ) {
    if( this==bs ) return (B)this;
    B full = ALL();             // Subclass-specific version of full
    if( this==full || bs==full ) return full;
    B any  = ANY();             // Subclass-specific version of any
    if( this==any ) return bs;
    if( bs  ==any ) return (B)this;
    long[] bits0 = _bits, bits1 = bs._bits;
    int con0 = Math.abs(_con), con1 = Math.abs(bs._con);
    if( bits0==null && con0==0 ) return bs.meet_nil();
    if( bits1==null && con1==0 ) return    meet_nil();

    // Expand any single bits
    if( bits0==null ) or(bits0=bits(0,con0), con0);
    if( bits1==null ) or(bits1=bits(0,con1), con1);
    con0 =    _con < 0 ? -1 : 1; 
    con1 = bs._con < 0 ? -1 : 1; 
    
    // Bigger in bits0
    if( bits0.length < bits1.length ) { long[] tmp=bits0; bits0=bits1; bits1=tmp; int t=con0; con0=con1; con1=t; }
    // Both meets?  Set-union
    if( con0 == 1 && con1 == 1 ) {
      long[] bits = bits0.clone();        // Clone larger
      for( int i=0; i<bits1.length; i++ ) // OR in smaller bits
        bits[i] |= bits1[i];
      return make(false,bits);
    }
    // Both joins?  Set-intersection
    if( con0 == -1 && con1 == -1 ) {
      long[] bits = bits1.clone();        // Clone smaller
      for( int i=0; i<bits1.length; i++ ) // AND in smaller bits
        bits[i] &= bits0[i];
      return make(true,bits);
    }

    // Mixed meet/join.  Find any bit in the join that is also in the meet.  If
    // found, we do not need to expand the meet - return it as-is.
    for( int i=0; i<Math.min(bits0.length,bits1.length); i++ )
      if( (bits0[i]&bits1[i]) != 0 )
        return make(false,con0== 1 ? bits0 : bits1);

    // Mixed meet/join.  Need to expand the meet with the smallest bit from the join.
    int bnum = find_smallest_bit(con0==-1 ? bits0 : bits1);
    long[] mbits = con0==1 ? bits0 : bits1; // Meet bits
    mbits = Arrays.copyOfRange(mbits,0,Math.max(mbits.length,idx(bnum)+1));
    or(mbits,bnum);
    return make(false,mbits);
  }
  
  private static int find_smallest_bit(long[] bits) {
    for( long bit : bits )
      if( bit != 0 )
        return Long.numberOfTrailingZeros(bit);
    throw AA.unimpl();
  }

  // Constants are self-dual; classes just flip the meet/join bit.  
  @SuppressWarnings("unchecked")
  public B dual() { return _bits==null && !is_class() ? (B)this : make_impl(-_con,_bits); }
  // join is defined in terms of meet and dual
  public Bits<B> join(Bits<B> bs) { return dual().meet(bs.dual()).dual(); }

  // Make a deep copy, for reseting INTERN to the starting state between tests
  static <T extends Bits> void init0(HashMap<T,T> INTERN) {
    for( T b : INTERN.keySet() ) {
      b._reset_con  = b._con;   // Saves con, and also removes -999999 sentinal
      b._reset_bits = b._bits == null ? null : b._bits.clone();
    }
  }
  // Make a deep copy, for reseting INTERN to the starting state between tests
  static <T extends Bits> void reset_to_init0(HashMap<T,T> INTERN) {
    Iterator<T> it = INTERN.keySet().iterator();
    while( it.hasNext() ) {
      T b = it.next();
      if( b._reset_con == -999999 ) { // If never called by init0, not part of the starting types
        it.remove();                  // So remove it
      } else {
        b._con  = b._reset_con;
        b._bits = b._reset_bits==null ? null : b._reset_bits.clone();
      }
    }
  }
 
  // Instances are unique-per-subclass of Bits, i.e., one for each of
  // BitsAlias, BitsFun, BitsRPC.  These record the split history, to let us
  // compute hashes that do not move after a split.
  static class HashMaker<B extends Bits<B>> {
    static class Q { Q(int a,int s) { _alias=a; _split=s; } final int _alias, _split; }
    int _init;             // One-time set at init, used to reset between tests
    Ary<Q> _splits = new Ary<>(new Q[1],0); //

    @Override public String toString() {
      SB sb = new SB().p("HashMaker[");
      for( Q q : _splits )
        sb.p(q._alias).p("->").p(q._split).p(',');
      return sb.p("]").toString();
    }
    
    // Split out a bit to form a new constant, from a prior a bit
    int split(int par, HashMap<B,B> INTERN) {
      if( par==0 ) return 1;    // Ignore init
      // Split the parent bit in twain.  Instances of the parent are everywhere
      // updated to have both bits, but hash to the same value as the parent.
      int new_split = _splits._len+2;

      // Walk and update
      for( B bits : INTERN.keySet() ) {
        if( bits.test(par) ) {
          int con = bits._con;
          assert con!=0;        // nil is never split
          if( bits._bits==null ) {
            bits._con = con < 0 ? -1 : 1;
            or(bits._bits = bits(con,new_split),Math.abs(con));
          } else if( new_split > max(bits._bits) ) bits._bits = bits(0,new_split);
          or(bits._bits,new_split);
        }
      }

      // Also, for BitsAlias, have to expand TypeMems to match
      if( this==BitsAlias.HASHMAKER )
        for( Type t : Type.INTERN.keySet() )
          if( t instanceof TypeMem )
            ((TypeMem)t).split(par,new_split);
      
      _splits.push(new Q(par,new_split)); // Record the split

      // Assert hash not changed
      for( B bits : INTERN.keySet() )
        assert bits._hash == compute_hash(bits);
      
      return new_split;
    }
    int compute_hash(Bits bits) {
      // Sum of bits, minus exceptions
      long sum=0;
      if( bits._bits==null ) sum = mask(Math.abs(bits._con));
      else for( long b : bits._bits ) sum += b;
      // Minus the exceptions
      for( Q q : _splits )
        if( q != null && bits.test(q._alias) && bits.test(q._split) )
          sum -= mask(q._split);
      // Fold to an int
      return (int)((sum>>32)|sum);
    }
    int compute_hash(TypeObj[] as) {
      // Sum of hashes, minus exceptions
      int sum=0, len=as.length;
      for( TypeObj obj : as ) if( obj != null ) sum+=obj._hash;
      // Minus the exceptions
      for( Q q : _splits )
        if( q != null && q._alias < len && q._split < len &&
            as[q._alias]!=null && as[q._split]!=null )
          sum -= as[q._split]._hash;
      return sum;
    }
    void init0() { _init = _splits._len; }
    void reset_to_init0() { _splits.set_len(_init); }
    boolean has_bits(B b) { return b.max() >= _init+2; }
  }
  
  /** @return an iterator */
  @NotNull @Override public Iterator<Integer> iterator() { return new Iter(); }
  private class Iter implements Iterator<Integer> {
    int _i=-1;
    @Override public boolean hasNext() {
      if( _bits==null )
        if( _i==-1 ) { _i=0; return true; } else return false;
      int idx;
      while( (idx=idx(++_i)) < _bits.length )
        if( (_bits[idx]&mask(_i)) != 0 )
          return true;
      return false;
    }
    @Override public Integer next() {
      if( _bits==null ) return Math.abs(_con);
      if( idx(_i) < _bits.length ) return _i;
      throw new java.util.NoSuchElementException();
    }
  }
}
