package com.cliffc.aa;

import static com.cliffc.aa.AA.unimpl;

/** Operator parsing.

No leading expr, but required trailing expr e1:

  - Normal uni-op parse; limit of single character
  - Examples:  ~e1     ;  +3     ;  -2
    Called as:  e1.~_();   3.+_();   2.-_();

  - First char is "[" or 2nd or later is "{" or "<"; trailing op chars allowed.
    Requires a closing ">" or "}" or "]" op token, without an '='.
  - Examples:   [3]    ;  [% e1 %]
    Called as:  3.[_]();     e1.[%_%]()

Leading expr, required no trailing expr
  - Any normal op sequence, and is treated as a postfix call
  - Examples:   3++     ;  e0$$
  - Called as:  3._++() ;  e0._$$()

Leading expr, and trailing expr
  - Any normal op sequence, and is treated as an infix call.  Precedence from 1st char
  - Examples:   1+2*3          ;  e0+*e1
  - Called as:  1._+_(2._*_(3));  e0._+*_(e1)

Leading expr, and trailing expr
  - Op token with '[' (leading position ok) or '{' (2nd or later position)
  - Requires trailing op token with matching '}' or ']'.
  - No '=' in trailing op
  - Examples:   ary[idx]     ;  e0 %{ e1 }%  ;
  - Called as:  ary._[_](idx);  e0._%{_}%(e1);

Trinary, 3 exprs
  - Op token with '[' (leading position ok) or '{' '<'(2nd or later position)
  - Requires trailing op token with matching '>', '}' or ']'.
  - Yes '=' in trailing op
  - Examples:   ary[idx]=val      ;  dict["key"]=val      ;  e0 %{% e1 %}=% e2
    Called as:  ary._[_]=(idx,val);  dict._[_]=("key",val);  e0._%{%_%}=%_(e1,e2)

 */

// TODO: Mostly half-baked, and could have a lot of support from Env moved into here
public class Oper {
  public final String _name;    // Full name, with '_' where arguments go
  public final byte _prec;      // Precedence.  Not set for uniops and balanced ops.  Always > 0 for infix binary ops.
  public final int _nargs;

  private Oper(String name, int prec) {
    char c0 = name.charAt(0), c1 = name.charAt(0);
    assert c0!='{' &&  (c0!='_' || c1!='{'); // Too confusing
    // Count '_' for nargs
    int nargs=0;
    for( int i=0; (i = name.indexOf('_',i)+1)!=0; )
      nargs++;
    // Binary operators always have a precedence, other ops always have prec==0
    //assert (c0=='_' && name.charAt(name.length()-1)=='_' && nargs==2) == (prec>0);
    _name=name.intern();
    _prec=(byte)prec;
    _nargs=nargs;
  }

  @Override public String toString() { return _name; }

  // Build a unary oper.
  public static Oper make(String name) { return new Oper(name,0); }

  // Build a binary oper, compute precedence based on 1st not-underscore
  // character.  Means, e.g. "<" and "<=" are forced to the same precedence.
  public static Oper make(String name, int prec) {
    int oprec = prec(name.charAt(1));
    if( prec > oprec ) return null;
    return new Oper(name,oprec);
  }

  // Build a balanced open oper.
  public static Oper make_open(String name) { return is_open(name) ? new Oper(name,0) : null; }
  // True if op has balanced-op openers
  static boolean is_open( String name ) { return name.indexOf('[')>=0 || name.indexOf('{')>=2 || name.indexOf('<')>=2; }
  public boolean is_open() { return is_open(_name); }

  // Precedence is based on the single first non-'_' character
  public static final int MAX_PREC=6;
  private static int prec(char c) {
    return switch( c ) {
    case '*', '/', '%'      -> 5;
    case '+', '-'           -> 4;
    case '<', '>', '=', '!' -> 3; // includes <, <=, >, >=, ==, !=
    case '&'                -> 2;
    case '|'                -> 1;
    default -> throw unimpl();
    };
  }

  // Parse a postfix op; update P or return null.
  // If the required trailing expr is not found, caller must unwind P.
  public static Oper post(Parse P) { throw unimpl(); }

  // Parse a binary op, OR a leading balanced op.
  public static Oper binbal(Parse P) { throw unimpl(); }

}
