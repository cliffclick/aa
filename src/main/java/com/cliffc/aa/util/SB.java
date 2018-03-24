package com.cliffc.aa.util;

import com.cliffc.aa.Type;

/** Tight/tiny StringBuilder wrapper.
 *  Short short names on purpose; so they don't obscure the printing.
 *  Can't believe this wasn't done long long ago. */
public final class SB {
  public final StringBuilder _sb;
  int _indent = 0;
  public SB(        ) { _sb = new StringBuilder( ); }
  public SB(String s) { _sb = new StringBuilder(s); }
  public SB p( String s ) { _sb.append(s); return this; }
  public SB p( Type t ) { _sb.append(t.toString()); return this; }
  public SB p( float  s ) {
    if( Float.isNaN(s) )
      _sb.append( "Float.NaN");
    else if( Float.isInfinite(s) ) {
      _sb.append(s > 0 ? "Float.POSITIVE_INFINITY" : "Float.NEGATIVE_INFINITY");
    } else _sb.append(s);
    return this;
  }
  public SB p( double s ) {
    if( Double.isNaN(s) )
      _sb.append("Double.NaN");
    else if( Double.isInfinite(s) ) {
      _sb.append(s > 0 ? "Double.POSITIVE_INFINITY" : "Double.NEGATIVE_INFINITY");
    } else _sb.append(s);
    return this;
  }
  public SB p( char   s ) { _sb.append(s); return this; }
  public SB p( int    s ) { _sb.append(s); return this; }
  public SB p( long   s ) { _sb.append(s); return this; }
  public SB p( boolean s) { _sb.append(s); return this; }
  // Not spelled "p" on purpose: too easy to accidentally say "p(1.0)" and
  // suddenly call the autoboxed version.
  public SB pobj( Object s ) { _sb.append(s.toString()); return this; }
  public SB i( int d ) { for( int i=0; i<d+_indent; i++ ) p("  "); return this; }
  public SB i( ) { return i(0); }
  public SB ip(String s) { return i().p(s); }
  public SB s() { _sb.append(' '); return this; }
  // Java specific append of double
  public SB pj( double  s ) {
    if (Double.isInfinite(s))
      _sb.append("Double.").append(s>0? "POSITIVE_INFINITY" : "NEGATIVE_INFINITY");
    else if (Double.isNaN(s))
      _sb.append("Double.NaN");
    else
      _sb.append(s);
    return this;
  }
  // Java specific append of float
  public SB pj( float  s ) {
    if (Float.isInfinite(s))
      _sb.append("Float.").append(s>0? "POSITIVE_INFINITY" : "NEGATIVE_INFINITY");
    else if (Float.isNaN(s))
      _sb.append("Float.NaN");
    else
      _sb.append(s).append('f');
    return this;
  }

  // Increase indentation
  public SB ii( int i) { _indent += i; return this; }
  // Decrease indentation
  public SB di( int i) { _indent -= i; return this; }

  // Copy indent from given string buffer
  public SB nl( ) { return p('\n'); }

  @Override public String toString() { return _sb.toString(); }
}
