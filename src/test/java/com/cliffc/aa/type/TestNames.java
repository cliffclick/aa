package com.cliffc.aa.type;

import com.cliffc.aa.util.SB;
import org.junit.Test;

import java.util.Arrays;
import java.util.HashMap;

import static org.junit.Assert.*;

/** Test an implementation of named structs

Theory:

- Structs are neither up nor down, but they have a default which can be up or down
- Structs include all possible (infinite) fields, with the default for most
- Listed fields are as-is, neither up nor down, they are what they are
- Structs have a clazz name, which can be up or down
- The name up/down is separate from the default

 */
public class TestNames {

  // Testing Struct class
  static class S {
    String _clz;
    boolean _clzany;            // High/low on names, unrelated to def high/low
    Type _def;
    HashMap<String,Type> _flds;
    S _dual;
    S(String clz, boolean b, Type def, HashMap<String,Type> flds) { this(clz,b,def,flds,null); }
    S(String clz, boolean b, Type def, HashMap<String,Type> flds, S dual) {
      assert clz.isEmpty() || clz.endsWith(":");
      for( Type t : flds.values() )
        assert t!=def;
      _clz =clz ;
      _clzany= b;
      _def =def ;
      _flds=flds;
      if( dual==null ) {
        HashMap<String,Type> flds2 = new HashMap<>();
        for( String k : flds.keySet() )
          flds2.put(k,_flds.get(k).dual());
        _dual = new S(_clz,!b,_def.dual(),flds2, this);
      } else {
        _dual = dual;
      }
    }

    // Dual all the infinite fields
    S dual() { return _dual; }

    Type get(String clz, String key) {
      Type t = _flds.get(key);
      return t==null || !clz.startsWith(_clz) ? _def : t;
    }
    Type get(String key) {
      Type t = _flds.get(key);
      return t==null  ? _def : t;
    }

    // Compute 'isa' the hard way.
    // Check all fields in 'this' are 'isa' the matching field in 'that',
    // and vice-versa
    boolean x_isa( S s ) {
      for( String k : _flds.keySet() )
        if( !_flds.get(k).isa(s.get(_clz,k)) )
          return false;         // This field is not isa
      for( String k : s._flds.keySet() )
        if( !get(s._clz,k).isa(s._flds.get(k)) )
          return false;         // This field is not isa
      return true;
    }

    // Print all fields in this, and their matching field in that
    SB meet0( S s ) {
      SB sb = new SB();
      Type sdef = s._flds.get("_");
      for( String k : _flds.keySet() ) {
        _flds.get(k).str(sb.p(_clz).p(k).p('='),true,false).p("  ");
        // Matching field: _clz has to be a prefix of s._clz and the field has to exist
        s.get(_clz,k).str(sb,true,false).nl();
      }
      return sb;
    }

    static String prefix( String s0, String s1 ) {
      int len = Math.min(s0.length(), s1.length());
      for( int i = 0; i < len; i++ )
        if( s0.charAt(i) != s1.charAt(i) )
          return s0.substring(0, i);
      return s0.substring(0, len);
    }

    // Stoopid meet idea
    // names take prefix, so expand to cover
    // default must meet directly
    // fields meet with match from other side
    S meet( S s ) {
      HashMap<String,Type> flds = new HashMap<>();
      // Meet common keys
      for( String k :   _flds.keySet() )
        flds.put(k,get(k).meet(s.get(k)));
      for( String k : s._flds.keySet() )
        flds.put(k,get(k).meet(s.get(k)));
      // Meet default
      Type def = _def.meet(s._def);
      // Remove values matching def
      flds.values().removeIf( t -> t==def );

      // If no common prefix, fall to low prefix.
      // Else if prefix is high, keep low else high
      String s0=_clz, s1=s._clz;
      String pre = prefix(s0,s1), clz;
      boolean b = _clzany & s._clzany;
      if(      pre.equals(  _clz) ) clz =   _clzany ? s1 : s0;
      else if( pre.equals(s._clz) ) clz = s._clzany ? s0 : s1;
      else { clz = pre; b=false; } // No common prefix, fall hard

      return new S(clz,b,def,flds);
    }

    // Scalar meet
    S meet( Type t ) {
      HashMap<String,Type> flds = new HashMap<>();
      for( String k : _flds.keySet() )
        flds.put(k, _flds.get(k).meet(t));
      Type def = _def.meet(t);
      flds.values().removeIf( v -> v==def );
      return new S(_clz,_clzany,def,flds);
    }

    // Pretty print
    @Override public String toString() { return str(new SB()).toString(); }
    private SB str(SB sb) {
      sb.p(_clzany?"~":"").p(_clz).p('{');
      _def.str(sb,true,false);
      for( String k : _flds.keySet() )
        _flds.get(k).str(sb.p(", ").p(k).p('='),true,false);
      return sb.p('}');
    }

    @Override public boolean equals( Object o ) {
      if( this==o ) return true;
      if( !(o instanceof S s) ) return false;
      if( !_clz.equals(s._clz) ) return false;
      if( _def!=s._def ) return false;
      return _flds.equals(s._flds);
    }
    @Override public int hashCode() {
      throw com.cliffc.aa.AA.unimpl();
    }


    // (A & B) == (B & A)
    // Return 0 if no error, +1 if error
    int commute(S that) {
      S mt0 = this.meet(that);
      S mt1 = that.meet(this);
      if( mt0.equals(mt1) ) return 0;
      System.out.println("Not commutative!");
      System.out.println(""+this+" & "+that+" = "+mt0);
      System.out.println(""+that+" & "+this+" = "+mt1);
      return 1;
    }

    // A & (B & C) == (A & B) & C
    // Return 0 if no error, +1 if error
    static int associative(S s0, S s1, S s2 ) {
      S mt01 = s0.meet(s1);
      S mt01_2 = mt01.meet(s2);
      S mt12 = s1.meet(s2);
      S mt0_12 = s0.meet(mt12);
      if( mt01_2.equals(mt0_12) ) return 0;
      System.out.println("Not associative!");
      System.out.println(" "+s0+" & ("+s1+"  & "+s2+") = "+mt01_2);
      System.out.println("("+s0+" &  "+s1+") & "+s2+"  = "+mt0_12);
      return 1;
    }

    // A is a normal scalar type, and meets "deep"
    // A & (B & C) == (A & B) & C
    // Return 0 if no error, +1 if error
    static int associative(Type s0, S s1, S s2 ) {
      S mt01 = s1.meet(s0);
      S mt01_2 = mt01.meet(s2);
      S mt12 = s1.meet(s2);
      S mt0_12 = mt12.meet(s0);
      if( mt01_2.equals(mt0_12) ) return 0;
      System.out.println("Not associative!");
      System.out.println(" "+s0+" & ("+s1+"  & "+s2+") = "+mt01_2);
      System.out.println("("+s0+" &  "+s1+") & "+s2+"  = "+mt0_12);
      return 1;
    }

    // if A & B == MT then ~MT & ~A == ~A and ~MT & ~B == ~B
    // Return 0 if no error, +1 if error
    int symmetric(S that) {
      S mt = this.meet(that);
      S x = that.dual().meet(mt.dual());
      S y = this.dual().meet(mt.dual());
      if( x.equals(that.dual()) && y.equals(this.dual()) ) return 0;
      System.out.println("Not symmetric!");
      System.out.println(""+this+" & "+that+" = "+mt+", BUT");
      S xmt = y.equals(dual()) ? x : y;
      S x2  = y.equals(dual()) ? that : this;
      System.out.println(""+x2.dual()+" & "+mt.dual()+" = "+xmt+", and not "+x2.dual());
      return 1;
    }
  }

  final static S scd = new S("",false,Type.ALL,new HashMap<>(){{
        put("c",TypeInt.TRUE);
        put("d",TypeFlt.PI);
      }});

  final static S i64 = new S("int:",false,Type.ALL,new HashMap<>(){{
        put("x",TypeInt.INT64);
      }});

  final static S point = new S("Point:",false,Type.ALL,new HashMap<>(){{
        put("x",TypeFlt.FLT64);
        put("y",TypeFlt.FLT64);
      }});

  final static S empty = new S("",false,Type.ALL,new HashMap<>());


  final static S[] ss0 = new S[]{scd,i64,point,empty};
  final static Type[] ts0 = new Type[]{Type.ALL,Type.SCALAR,Type.NSCALR,Type.NIL};

  @Test public void testType() {
    // Include the duals in everything
    S[] ss = Arrays.copyOf(ss0,ss0.length<<1);
    for( int i=0; i<ss0.length; i++ ) {
      assert !ss0[i]._def.above_center() && !ss0[i]._clzany;
      ss[i+ss0.length] = ss0[i].dual();
    }

    Type[] ts = Arrays.copyOf(ts0,ts0.length<<1);
    for( int i=0; i<ts0.length; i++ ) {
      assert !ts0[i].above_center();
      ts[i+ts0.length] = ts0[i].dual();
    }

    int err=0;
    for( S s0 : ss )
      for( S s1 : ss )
        err += s0.commute(s1);
    assertEquals(0,err);

    for( S s0 : ss )
      for( S s1 : ss )
        for( S s2 : ss )
          err += S.associative(s0,s1,s2);
    assertEquals(0,err);

    for( Type t0 : ts )
      for( S s1 : ss )
        for( S s2 : ss )
          err += S.associative(t0,s1,s2);
    assertEquals(0,err);

    for( S s0 : ss )
      for( S s1 : ss )
        err += s0.symmetric(s1);
    if( err!=0 ) System.exit(err);

    assertEquals(0,err);
  }
}
