package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import com.cliffc.aa.util.IBitSet;
import com.cliffc.aa.util.VBitSet;
import org.jetbrains.annotations.NotNull;

import java.util.Arrays;
import java.util.Iterator;

// Bits supporting a lattice; immutable; hash-cons'd.  Bits can be *split* in
// twain, basically a single Bit is really set of all possible future splits.
//
// Splitting is useful during inlining, where a single Call is duplicated and
// RPCs to the original one might return to either of of the inlines.  Same for
// internal functions and allocation sites - after the inline, pointers and
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
// Individual bits are never constants (due to possible future splits), and
// instead are a class of things that are either meet'd or join'd (above or
// below the centerline).  Aliases are usually classes because a single NewNode
// can be executed in a loop, producing many objects with the same alias#.
// FIDXs and RPCs would be constants, as there is a single instance of a
// function or a return-point, except for code-cloning (i.e. inlining).
//
// The tree-structure really defines a basic set-inclusion property which is
// trivially a lattice; see https://en.wikipedia.org/wiki/Lattice_(order) pic#1.
// However to get a lattice AND a dual we MUST have the empty element in the
// middle.  The meet of +2 and +5 is... [], the empty set, and NOT [2&5].

public abstract class Bits<B extends Bits<B>> implements Iterable<Integer> {
  // Holds a set of bits meet'd together, or join'd together, along
  // with a single bit choice.
  // If _bits is NULL and _con is 0, this is the EMPTY state.
  // If _bits is NULL, then _con is a single bit and is +/- for meet/join.
  // If _bits is not-null, then _con is +1 for meet, and -1 for join.
  // The NIL bit has both meet & join flavors, required for a lattice.
  long[] _bits;   // Bits set or null for a single bit
  int _con;       // value of single bit
  int _hash;      // Pre-computed hashcode
  // Intern: lookup and return an existing Bits or install in hashmap and
  // return a new Bits.  Overridden in subclasses to make type-specific Bits.
  abstract B make_impl(int con, long[] bits );
  abstract Tree<B> tree();
  public abstract B ALL();
  public abstract B ANY();
  public abstract B EMPTY();

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
    if( _bits==null ) return true;  // Must be a single bit#
    if( _con != 1 && _con != -1 ) return false;
    if( _bits.length==0 ) return false;  // Empty bits replaced by a con
    if( _bits.length==1 && _bits[0]== 0 ) return false; // NO bits is bad, use EMPTY instead
    if( _bits[_bits.length-1]==0 ) return false; // Array is "tight"
    if( _bits.length==1 && _bits[0]==1 ) return true; // NIL
    // No set bit has a parent bit set, because the parent overrides
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
  public int bitCount() {
    if( _bits==null ) return _con==0 ? 0 : 1;
    int sum=0;
    for( long b : _bits )
      sum += Long.bitCount(b);
    return sum;
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
  @Override public String toString() { return str(new SB()).toString(); }
  public SB str(SB sb) {
    if( _bits==null ) {
      if( _con==0 ) return sb.p("[]"); // EMPTY
      return sb.p('[').p(_con).p(']');
    }
    sb.p('[');
    if( above_center() ) sb.p('~');
    char sep = above_center()?'+':',';
    if( test(_bits,1) ) {
      if( test(_bits,0) ) sb.p('0').p(sep);
      return sb.p(above_center() ? "ANY]" : "ALL]");
    }
    for( Integer idx : this ) sb.p(idx).p(sep);
    return sb.unchar().p(']');
  }

  // Constructor taking an array of bits, and allowing join/meet selection.
  // Canonicalizes the bits.  The 'this' pointer is only used to clone the class.
  private B make( boolean any, long[] bits ) {
    // If a 'parent' bit is set, then no need to have any child bits set.
    Tree<B> tree = tree();
    // TODO: Run this loop backwards, avoids most tree-walks; lowers O(n log n) to O(n).
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
    // Special check for +/-0
    if( len==1 && bits[0]==1 ) return make_impl(any ? -1 : 1,bits);
    // Empty is self-dual, ignores 'any'
    if( len==1 && bits[0]==0 ) return make_impl(0,null);
    // Single bit
    int bnum0 = 63 - Long.numberOfLeadingZeros(bits[len-1]);
    int bnum = bnum0 + ((len-1)<<6);
    if( any ) bnum = -bnum;
    return make_impl(bnum,null);
  }
  // Constructor taking a single bit
  final B make( int bit ) { return bit==0 ? make_impl(1,new long[]{1}) : make_impl(bit,null); }
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

  public int getbit() { assert _bits==null && _con!=0; return _con; }
  public int abit() { return _bits==null&&_con!=0 ? _con : -1; }
  public boolean above_center() { return _con<0; }
  // Only empty and nil.  Other bits represent sets (possibly unsplit).
  public boolean is_con() { return is_nil() || is_empty(); }
  public boolean is_empty() { return _bits==null && _con==0; }
  public boolean is_nil() { return _bits!=null && _bits.length==1 && _bits[0]==1; }
  boolean may_nil() { return _con==-1 && _bits != null && ((_bits[0]&1) == 1); }
  // Add a low nil.
  @SuppressWarnings("unchecked")
  B meet_nil() {
    if( above_center() ) return make(0); // Crossing centerline, drop all above bits, just [0]
    if( test(0) ) return (B)this;// Already has nil
    long[] bs = _bits;
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
    if( _bits==null ) return i!=0 && i==Math.abs(_con);
    int idx = idx(i);
    return idx < _bits.length && test(_bits, i);
  }
  // Test if this bit, or any parent of this bit, is set
  public boolean test_recur( int i ) {
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
    if( !above_center() || _bits == null ) return (B)this;  // Some constant not-nil
    if( !test(_bits,0) ) return (B)this; // No nil choice
    long[] bs = _bits.clone();           // Keep all other bits
    and(bs,0);                           // remove nil choice
    return make(true,bs);                // Choices without nil
  }
  // Remove the named bit, but otherwise preserve the type
  @SuppressWarnings("unchecked")
  public B clear(int bit) {
    if( !test(bit) ) return (B)this;
    if( _bits == null ) return EMPTY();
    long[] bs = _bits.clone();
    and(bs,bit);
    return make(_con==-1,bs);
  }
  // Add the named bit, but otherwise preserve the type
  @SuppressWarnings("unchecked")
  public B set(int bit) {
    if( test(bit) ) return (B)this;
    B b = make(bit);
    if( this == EMPTY() ) return b;
    return meet(b);
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

  private static void or ( long[] bits, long con ) { bits[idx(con)] |=  mask(con); }
  private static void and( long[] bits, long con ) { bits[idx(con)] &= ~mask(con); }
  private static long[] bits( int b ) { return new long[idx(b)+1]; }
  public int max( ) {
    return _bits==null ? Math.abs(_con) : (63 - Long.numberOfLeadingZeros(_bits[_bits.length-1]))+((_bits.length-1)<<6);
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
  public B meet( final B bs ) {
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
      // Just the intersection, which may be empty.
      return make(true,bits);
    }

    // Mixed meet/join.  Toss away the join, keep only the meet bits.
    return above_center() ? bs : (B)this;
  }

  // Virtually expand all bits in both arrays to cover all children,
  // then AND the bits, then re-pack.  However, we do it tree-by-tree
  // to keep from doing the full expansion costs.
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

  // Constants are self-dual; classes just flip the meet/join bit.
  @SuppressWarnings("unchecked")
  public B dual() { return make_impl(-_con,_bits); }
  // join is defined in terms of meet and dual
  public Bits<B> join(Bits<B> bs) { return dual().meet(bs.dual()).dual(); }
  // Note no special nil handling; both sides need to either handle nil or not
  public boolean isa(B bs) { return meet(bs) == bs; }

  public Bits<B> subtract(Bits<B> bs) {
    Bits<B> bs0 = this;
    for( int alias : this )
      for( int kid=alias; kid!=0; kid = tree().next_kid(alias,kid) )
        if( bs.test_recur(kid) )
          bs0 = bs0.clear(kid);
    return bs0;
  }
  public boolean overlaps(Bits<B> bs) {
    for( int alias : this )
      for( int kid=alias; kid!=0; kid = tree().next_kid(alias,kid) )
        if( bs.test_recur(kid) )
          return true;
    return false;
  }

  // No kids
  public IBitSet bitset() {
    IBitSet bs = new IBitSet();
    for( int alias : this )
      bs.set(alias);
    return bs;
  }

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
    // Return two kids at slots ary[1] and ary[2].
    public int[] get_kids( int par ) { assert _kids[par][0]==3; return _kids[par]; }
    // True if kid is a child or equal to parent
    boolean is_parent( int par, int kid ) {
      for( ; par <= kid; kid = parent(kid) )
        if( par==kid ) return true;
      return false;             // Kid will be a larger number
    }

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
        _init[i] = _kids[i]==null ? 1 : _kids[i][0];
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
    public VBitSet plus_kids( Bits<B> bits) {
      VBitSet bs = new VBitSet();
      for( int i : bits )
        if( i != 0 )
          _plus_kids(bs,i);
      return bs;
    }
    void _plus_kids(VBitSet bs, int i) {
      bs.set(i);
      int nkids = i >= _kids.length || _kids[i]==null ? 0 : _kids[i][0];
      for( int kid=1; kid<nkids; kid++ )
        _plus_kids(bs,_kids[i][kid]);
    }

    // Return next child of alias; repeated calls iterate over all the children
    // of alias including itself.  When out of children returns 0.  Usage:
    // for( int kid=alias; kid!=0; kid=BitsAlias.next_kid(alias,kid) ) {...kid... }
    public int next_kid( int alias, int kid ) {
      if( kid==0 ) return 0;
      boolean is_par = is_parent(kid);
      if( kid==alias && !is_par ) return 0; // Singleton bit
      // Find kid in the alias-tree
      if( is_par ) {            // Go deeper
        return _kids[kid][1];   // First child one layer deeper
      } else {                  // Leaf, unwind & find sibling
        while(kid!=alias) {
          int par = _pars[kid];    // Parent
          int[] kids = _kids[par]; // All the parents' children
          for( int i=1; i<kids[0]-1; i++ )
            if( kids[i]==kid )
              return kids[i+1]; // Return sibling
          kid=par;              // Up-parent & go again
        }
        return 0;               // Last child visited
      }
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
