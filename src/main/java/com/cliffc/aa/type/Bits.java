package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import org.jetbrains.annotations.NotNull;

import java.util.Arrays;
import java.util.BitSet;
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
// Splitting induces a tree-structure to the bits; there is a parent / child
// relationship defined in the inner Tree class, and used in meet calls.
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
//
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
  // Intern: lookup and return an existing Bits or install in hashmap and
  // return a new Bits.  Overridden in subclasses to make type-specific Bits.
  abstract B make_impl(int con, long[] bits );
  abstract boolean is_class(int idx); // This bit is a class all by itself
  abstract Tree<B> tree();
  public abstract B ALL();
  public abstract B ANY();

  // Common init
  void init(int con, long[] bits ) {
    _con = con;
    _bits=bits;
    long sum=_con;
    if( _bits != null ) for( long l : _bits ) sum += l;
    _hash = (int)((sum>>32)+sum);
    if( _hash==0 ) _hash=1;
    assert check();
  }
  private boolean check() {
    if( _bits==null ) return _con >= 0 || is_class(-_con); // Must be a single constant bit#
    if( _con != 1 && _con != -1 ) return false;
    if( _bits.length==0 ) return false;  // Empty bits replaced by a con
    if( _bits.length==1 && _bits[0]== 0 && _con==1 ) return true; // NO bits is OK
    if( _bits[_bits.length-1]==0 ) return false; // Array is "tight"
    // No set bit has a parent bit set
    Tree<B> tree = tree();
    for( int i : this )
      while( (i = tree.parent(i)) != 0 )
        if( test(i) )
          return false;
    // For efficiency, 1 bit set uses 'con' instead of 'bits'
    return check_multi_bits(_bits); // Found multiple bits
  }
  private static boolean check_multi_bits( long[] bits) {
    int len = bits.length;
    long b = bits[len-1];             // Last word
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
  // This bit set contains more than 1 concrete element type
  public boolean is_class() {
    return
      _bits!=null ||            // many bits are set
      _con<0 ||                 // or JOIN of set of bits
      is_class(_con);           // or single bit is a class not a constant
  }

  // Constructor taking an array of bits, and allowing join/meet selection.
  // Canonicalizes the bits.  The 'this' pointer is only used to clone the class.
  private B make( boolean any, long[] bits ) {
    // If a 'parent' bit is set, then no need to have any child bits set.
    Tree<B> tree = tree();
    // TODO: Run this loop backwards, avoids most tree-walks; lowers O(n log n)
    // to O(n).
    for( int i=0; i<bits.length; i++ ) { // For all words
      long l = bits[i];
      if( l!=0 ) {
        for( int j=0; j<64; j++ ) // For all bits in word
          if( (mask(j)&l) != 0 ) {
            int par = (i<<6)+j; // Kid index
            while( (par = tree.parent(par)) != 0 ) // Walk parent chain
              if( test(bits,par) )                 // If parent set
                { bits[i]&=~mask(j); break; }      // then clear kid
          }
      }
    }

    // Remove any trailing empty words
    int len = bits.length;
    while( len > 1 && bits[len-1]==0 ) len--;
    if( bits.length != len ) bits = Arrays.copyOf(bits,len);

    // Check for a single bit or NO bits
    if( check_multi_bits(bits) ) return make_impl(any ? -1 : 1,bits);
    // Empty is self-dual, ignores 'any'
    if( len==1 && bits[0]==0 ) return make_impl(1,bits);
    // Single bit
    int bnum0 = 63 - Long.numberOfLeadingZeros(bits[len-1]);
    int bnum = bnum0 + ((len-1)<<6);
    if( any && is_class(bnum) ) bnum = -bnum;
    return make_impl(bnum,null);
  }
  // Constructor taking a single bit
  final B make( int bit ) { return make_impl(bit,null); }
  // Constructor taking an array of bits
  public final B make( int... bits ) {
    int max= 0;                // Find max bit
    for( int bit : bits ) max=Math.max(max,bit);
    long[] ls = bits(max);  // Big enuf bits
    for( int bit : bits ) or(ls,bit);
    return make(false,ls);
  }

  private static int  idx (long i) { return (int)(i>>6); }
  private static long mask(long i) { return 1L<<(i&63); }

  int getbit() { assert _bits==null; return _con; }
  public int abit() { return _bits==null ? _con : -1; }
  public boolean above_center() { return _con<0; }
  public boolean is_con() {
    return _bits==null || (_bits.length==1 && _bits[0]==0);
  }
  public boolean is_empty() { return _bits!=null && _bits.length==1 && _bits[0]==0; }
  boolean may_nil() { return _con==0 || (_con==-1 && _bits != null && ((_bits[0]&1) == 1)); }
  // Add a nil
  @SuppressWarnings("unchecked")
  B meet_nil() {
    if( _con==0 ) return (B)this;// Already a nil constant
    long[] bs = _bits;
    if( _con == -1 && bs!=null && (bs[0]&1)==1 ) // JOIN includes nil?
      return make(0);                // Return just NIL
    if( bs==null )              // Is a single compressed bit
      or(bs = bits(Math.abs(_con)),Math.abs(_con)); // Decompress single bit into array
    else bs = _bits.clone();    // Make a private set
    bs[0] |= 1;                 // Set nil
    return make(false,bs);      // Its below center now, even if the original was above
  }

  // Test a specific bit is set or clear on a given bits
  private static boolean test(long[] bits, int i) { return idx(i) < bits.length && (bits[idx(i)]&mask(i))!=0; }
  // Test a specific bit is set or clear on this Bits
  public boolean test(int i) {
    if( _bits==null ) return i==Math.abs(_con);
    int idx = idx(i);
    return idx < _bits.length && test(_bits, i);
  }
  // Test if this bit, or any parent of this bit, is set
  boolean test_recur( int i ) {
    if( test(i) ) return true;
    Tree<B> tree = tree();
    while( (i = tree.parent(i)) != 0 )
      if( test(i) )
        return true;
    return false;
  }

  // Return the type without a nil-choice.  Only applies to above_center types,
  // as these are the only types with a nil-choice.  Only called during meets
  // with above-center types.  If called with below-center, there is no
  // nil-choice (might be a must-nil but not a choice-nil), so can return this.
  @SuppressWarnings("unchecked")
  B not_nil() {
    if( _con != -1 || _bits == null ) return (B)this; // Below or at center
    if( !test(_bits,0) ) return (B)this; // No nil choice
    long[] bs = _bits.clone();           // Keep all other bits
    and(bs,0);                           // remove nil choice
    return make(true,bs);                // Choices without nil
  }
  // Remove the nil bit, but otherwise preserve the type
  @SuppressWarnings("unchecked")
  public B strip_nil() {
    if( _bits == null ) return (B)this; // Should not be a nil to remove
    if( (_bits[0] &1)==0 ) return (B) this; // No nil
    long[] bs = _bits.clone();
    bs[0] &= ~1;                // Strip nil
    return make(_con==-1,bs);
  }
  // Ignore nil in 'this', and make both Bits below center, and check 'isa'
  boolean is_contained(B bs1) {
    B bs0 = strip_nil();
    if( bs0.above_center() ) bs0 = bs0.dual();
    if( bs1.above_center() ) bs1 = bs1.dual();
    return bs0.isa(bs1);
  }

  private static void or ( long[] bits, long con ) { bits[idx(con)] |=  mask(con); }
  private static void and( long[] bits, long con ) { bits[idx(con)] &= ~mask(con); }
  private static long[] bits( int b ) { return new long[idx(b)+1]; }
  int max( ) {
    return _bits==null ? _con : (63 - Long.numberOfLeadingZeros(_bits[_bits.length-1]))+((_bits.length-1)<<6);
  }

  // Meet is more complex than the obvious AND/OR over bits.  There's a bit of
  // prefix logic to remove common cases (meet with ANY/ALL/NIL), and a final
  // expanding into a large bit array.  After that we need to honor the tree
  // semantics; any set bits automatically include all their children as well.
  //
  // AS-IF: For any given set-bit, we "unpack" it setting every child bit.  We
  // then do the proper AND/OR operation on the bits, followed by a repack.
  //

  @SuppressWarnings("unchecked")
  public B meet( B bs ) {
    if( this==bs ) return (B)this;
    B full = ALL();             // Subclass-specific version of full
    if( this==full || bs==full ) return full;
    B any  = ANY();             // Subclass-specific version of any
    if( this==any ) return bs;
    if( bs  ==any ) return (B)this;
    // Empty is a little odd; similar to meeting two JOIN sets with nothing in
    // common - it is on the center, and forces above values to fall, and
    // itself falls to below values.
    if( is_empty() ) return bs.above_center() ? (B)this : bs;
    if( bs.is_empty() ) return above_center() ? bs : (B)this;

    long[] bits0 = _bits, bits1 = bs._bits;
    int con0 = Math.abs(_con), con1 = Math.abs(bs._con);
    if( bits0==null && con0==0 ) return bs.meet_nil();
    if( bits1==null && con1==0 ) return    meet_nil();

    // Expand any single bits
    if( bits0==null ) or(bits0=bits(con0), con0);
    if( bits1==null ) or(bits1=bits(con1), con1);
    con0 =    _con < 0 ? -1 : 1;
    con1 = bs._con < 0 ? -1 : 1;

    // Bigger in bits0
    if( bits0.length < bits1.length ) { long[] tmp=bits0; bits0=bits1; bits1=tmp; int t=con0; con0=con1; con1=t; }
    // Both meets?  Set-union
    if( con0 == 1 && con1 == 1 ) {
      long[] bits = bits0.clone();        // Clone larger
      for( int i=0; i<bits1.length; i++ ) // OR in smaller bits
        bits[i] |= bits1[i];
      return make(false,bits);  // This will remove parent/child dups
    }
    // Both joins?  Set-intersection
    Tree<B> tree = tree();
    if( con0 == -1 && con1 == -1 ) {
      long[] bits = new long[bits0.length];// Result array
      join(tree,bits0,bits1,bits);         // Merge left into right
      join(tree,bits1,bits0,bits);         // Merge right into left
      // Nil is not part of the parent tree, so needs to be set explicitly
      if( (bits0[0]&1)==1 && (bits1[0]&1)==1 )  bits[0]|=1;
      return make(true,bits);
    }

    // Mixed meet/join.  Find any bit in the join that is also in the meet.  If
    // found, we do not need to expand the meet - return it as-is.
    for( int i=0; i<Math.min(bits0.length,bits1.length); i++ )
      if( (bits0[i]&bits1[i]) != 0 )
        return make(false,con0== 1 ? bits0 : bits1);

    // Walk all the meet bits; if any are in the join we're done.  This is a
    // more exact version of the above any-bits-in-common test.
    if( (con0==1 ? test(tree,bits0,bits1) : test(tree,bits1,bits0)) )
      return make(false,con0== 1 ? bits0 : bits1);

    // Mixed meet/join.  Need to expand the meet with the smallest bit from the join.
    int bnum = find_smallest_bit(con0==-1 ? bits0 : bits1);
    long[] mbits = con0==1 ? bits0 : bits1; // Meet bits
    mbits = Arrays.copyOfRange(mbits,0,Math.max(mbits.length,idx(bnum)+1));
    if( bnum != -1) or(mbits,bnum); // Add a bit in.  Could make a dup bit
    return make(false,mbits);   // This will remove parent/child dups
  }

  private static int find_smallest_bit(long[] bits) {
    for( long bit : bits )
      if( bit != 0 )
        return Long.numberOfTrailingZeros(bit);
    return -1;
  }

  // Virtually expand all bits in both arrays to cover all children,
  // then AND the bits, then re-pack.  However, we do it tree-by-tree
  // keep from doing the full expansion costs.
  private static void join( Tree tree, long[] bits0, long[] bits1, long[] bits2 ) {
    // If a 'parent' bit is set, then no need to have any child bits set.
    for( int i=0; i<bits0.length; i++ ) { // For all words
      long l = bits0[i];
      if( l!=0 ) {
        // TODO: Use Long.numberOfTrailingZeros (or LeadingZeros probably) to
        // do this only once-per-set-bit.
        for( int j=0; j<64; j++ ) // For all bits in word
          if( (mask(j)&l) != 0 ) {
            for( int par = (i<<6)+j; par!=0; par = tree.parent(par) ) // Walk parent chain
              if( test(bits1,par) )                // If parent set
                { bits2[i]|=mask(j); break; }      // then set kid
          }
      }
    }
  }

  // Walk all the meet bits; if any are in the join return true.
  private static boolean test( Tree tree, long[] meets, long[] joins ) {
    for( int i=0; i<meets.length; i++ ) { // For all words
      long l = meets[i];
      if( l!=0 ) {
        // TODO: Use Long.numberOfTrailingZeros (or LeadingZeros probably) to
        // do this only once-per-set-bit.
        for( int j=0; j<64; j++ ) // For all bits in word
          if( (mask(j)&l) != 0 ) {
            for( int par = (i<<6)+j; par!=0; par = tree.parent(par) ) // Walk parent chain
              if( test(joins,par) )                // If parent set in join
                return true;
          }
      }
    }
    return false;
  }

  // Constants are self-dual; classes just flip the meet/join bit.
  @SuppressWarnings("unchecked")
  public B dual() {
    if( _bits!=null && _bits.length==1 && _bits[0]==0 ) return (B)this; // Empty is self-dual
    return _bits==null && !is_class(Math.abs(_con)) ? (B)this : make_impl(-_con,_bits);
  }
  // join is defined in terms of meet and dual
  public Bits<B> join(Bits<B> bs) { return dual().meet(bs.dual()).dual(); }
  // Note no special nil handling; both sides need to either handle nil or not
  public boolean isa(B bs) { return meet(bs) == bs; }

  // Bits are split in a tree like pattern, recorded here.  To avoid rehashing,
  // the exact same tree-split is handed out between tests.  Basically there is
  // only 1 tree shape, lazily discovered, for all tests.
  public static class Tree<B extends Bits<B>> {
    int _cnt = 1; // Next available bit number
    // Invariants: _pars[kid]==parent && _kids[parent].contains(kid)
    int[]   _pars = new int[2];  // Parent bit from child bit; _cnt is the in-use part
    int[][] _kids = new int[2][];// List of kids from a parent; 1st element is in-use length
    int[] _init;                 // Used to reset _kids[X][0] for all X

    int parent( int kid ) { return _pars[kid]; }
    public boolean is_parent( int idx ) { return idx<_kids.length && _kids[idx]!=null &&_kids[idx][0]>1; }
    @Override public String toString() { return toString(new SB(),1).toString(); }
    private SB toString(SB sb,int i) {
      sb.i().p(i).nl();
      if( is_parent(i) ) {
        sb.ii(1);
        for( int j=1; j<_kids[i][0]; j++ )
          toString(sb,_kids[i][j]);
        sb.di(1);
      }
      return sb;
    }

    // Split out a bit to form a new constant, from a prior a bit
    int split(int par) {
      // See if we have an existing bit
      if( par < _kids.length ) { // This parent has kids already
        int[] kids = _kids[par]; //
        if( kids != null ) {
          int klen = kids[0];        // Number of kids already, 1-based
          if( klen < kids.length ) { // Room for more in array?
            int bit = kids[klen];
            if( bit != 0 ) {            // Pre-allocated kid from prior test?
              assert _pars[bit] == par; // Then parent must already be preallocated
              kids[0] = klen+1;
              return bit;
            }
          }
        }
      }
      // Need a new bit
      int bit = _cnt++; // Next available bit number

      // Make space in the parents array to hold the parent of 'bit'
      while( bit >= _pars.length ) _pars = Arrays.copyOf(_pars,_pars.length<<1);
      assert _pars[bit]==0;
      _pars[bit] = par;
      // Make space in the kids array to hold the children of 'par'
      while( par >= _kids.length ) _kids = Arrays.copyOf(_kids,_kids.length<<1);
      int[] kids = _kids[par];  // All the children of 'par'
      if( kids==null ) _kids[par] = kids = new int[]{1};
      int klen = kids[0];       // 1-based number of children.  '1' means 'no children'
      if( klen == kids.length ) // Make space as needed
        _kids[par] = kids = Arrays.copyOf(kids,klen<<1);
      kids[klen] = bit;         // Insert new child of parent
      kids[0] = klen+1;         // Bump count of children
      return bit;
    }

    // Record all starting types tree relationships.
    void init0() {
      _init = new int[_kids.length];
      for( int i=0; i<_kids.length; i++ )
        _init[i] = _kids[i]==null ? 0 : _kids[i][0];
    }
    // Chop back alias tree to only those types recorded during 'init0'
    void reset_to_init0() {
      for( int i=0; i<_kids.length; i++ )
        if( _kids[i] != null )
          _kids[i][0] = i<_init.length ? _init[i] : 1;
    }
    int peek() { return _kids[1][_kids[1][0]]; } // for testing
    // Smear out the kids in a non-canonical representation, to allow the caller
    // to iterate more easily.
    public BitSet plus_kids(Bits<B> bits) {
      BitSet bs = new BitSet();
      for( int i : bits )
        if( i != 0 )
          _plus_kids(bs,i);
      return bs;
    }
    void _plus_kids(BitSet bs, int i) {
      bs.set(i);
      int nkids = i >= _kids.length || _kids[i]==null ? 0 : _kids[i][0];
      for( int kid=1; kid<nkids; kid++ )
        _plus_kids(bs,_kids[i][kid]);
    }
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
