package com.cliffc.aa;

import com.cliffc.aa.util.NonBlockingHashMap;

import static com.cliffc.aa.AA.unimpl;

/** Operator parsing.

No leading expr, but required trailing expr e1:

  - Normal uni-op parse; no other uni-op chars allowed.  No trailing suffix can
    match another uniop.  Disallowed: "#!" as a uniop because suffix "!" is
    already a uniop.  Similarly disallowed: "++", "--", "!!", etc.
  - Examples:  ~e1     ;  +3     ;  -2     ;  !7    ;  ~##e1
    Called as:  e1.~_();   3.+_();   2.-_();  7.!_();  e1.~##_()

  - First char is "[" or 2nd or later is "{" or "<"; trailing op chars allowed.
    No other uni-op chars allowed.
    Requires a closing ">" or "}" or "]" op token, without an '='.
  - Examples:  [3]     ;  [% e1 %]
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

Lazy operands:
  - The 2nd or later operands (not the first) can be computed lazily.
  - Indicated when Oper is built.
  - Parser thunks the operand, and passes the thunk.
  - Example:    a && b
  - Called as:  a._&&_( { -> b } )  or a._&&_( {b} )

 */

// Opers are added to the oper table when I see a final field store with a
// valid oper name.
public class Oper {
  static final NonBlockingHashMap<String,Oper> OPERS = new NonBlockingHashMap<>();

  public final String _name;    // Full name, with '_' where arguments go
  public final byte _prec;      // Precedence.  Not set for uniops and balanced ops.  Always > 0 for infix binary ops.
  public final int _nargs;      // Count of '_' same as count of arguments, including any 'self'
  public final boolean _lazy;   // Bin op, with lazy 2nd arg

  static boolean isOp0(byte c) { return "!#$%*+-.=<>^[]~/&|".indexOf(c) != -1; }
  static boolean isOp1(byte c) { return isOp0(c) || ":?_{}".indexOf(c) != -1; }

  // Precedence is based on the single first non-'_' character
  public static final int MAX_PREC=7; // Max level is used by recursive-descent Parser
  private static int prec(char c) {
    return switch( c ) {
    case '*', '/', '%' -> 6; // includes //
    case '+', '-'      -> 5; // includes ++, --
    case '<', '>'      -> 4; // includes <, <=, >, >=, <<, >>, etc.
    case '=', '!'      -> 3; // includes ==, !=
    case '&'           -> 2; // includes &&
    case '|'           -> 1; // includes ||
    default -> throw unimpl();
    };
  }

  // True if op has balanced-op openers
  public static boolean is_open( String name ) { return name.indexOf('[')>=0 || name.indexOf('{')>=2 || name.indexOf('<')>=2; }
  public boolean is_open() { return is_open(_name); }

  private Oper(String name, int prec, boolean lazy ) {
    char c0 = name.charAt(0), c1 = name.charAt(1);
    assert c0!='{' &&  (c0!='_' || c1!='{'); // Too confusing
    // Count '_' for nargs
    int nargs=0;
    for( int i=0; (i = name.indexOf('_',i)+1)!=0; )
      nargs++;
    // Binary operators always have a precedence, other ops always have prec==0
    assert (c0=='_' && name.charAt(name.length()-1)=='_' && nargs==2) == (prec>0);
    assert !lazy || prec>0;     // Binary ops can have lazy 2nd arg
    _name=name.intern();
    _prec=(byte)prec;
    _nargs = nargs;
    _lazy = lazy;
  }

  @Override public String toString() { return _name; }

  // Opers added to the OPERS table when a final field store is made.
  // This filters the string for non-opers, and publishes Opers.
  public static boolean make(String tok, boolean lazy) {
    String[] ss = tok.split("_",-99);
    if( ss.length==1 ) return false; // Got to have an '_' to be an operator
    if( ss[0].length()>0 ) {    // Must be a uni-op or leading bal-op
      byte c = (byte)ss[0].charAt(0);
      if( !isOp0(c) ) return false;
      if( is_leading_ambiguous(ss[0]) ) return false;
      if( ss.length==2 && ss[1].length()==0 ) return install(tok,0,false); // Valid unary op
      if( is_bal_op(ss[0],ss[1]) ) return false; // Not a matching balanced pair
      if( ss.length==2 ||                        // E.g. [_] for array alloc
          (ss.length==3 && ss[2].length()==0) )  // %{ e0 }%= e1
        return install(tok,0,false);
      throw unimpl(); // return false; // Too many args? "[_]=_?_"
    }
    // Leading expr.
    if( ss.length==3 ) { // Includes "_+_" and "_[_]"
      byte c = (byte)ss[1].charAt(0);
      if( !isOp0(c) ) return false;
      if( ss[2].length()==0 ) // Standard binary op
        return install(tok,prec(ss[1].charAt(0)),lazy);
      throw unimpl();
    }
    // TODO: check for valid balanced unary, binary, trinary
    // TODO: balanced ops install twice; once for just the prefix, which might
    // be shared amongst several balanced ops.
    throw unimpl();
  }
  private static boolean install(String tok, int prec, boolean lazy) { OPERS.put(tok,new Oper(tok,prec,lazy)); return true; }

  // Require that the all trailing substrings of 's' do not exist as leading
  // Opers already.  i.e. for an oper token "abc_def", the leading part is
  // "abc" and it has trailing parts "bc" and "c" which cannot themselves lead
  // another oper.  Example: a balanced unary op: "[-_-]" fails because the
  // leading part "[-" has a trailing substring "-" which is already an oper.
  // I.e. "[-7-]" could parse as "[-" "7" "-]" OR as "[" "-" "7" "-]".
  private static boolean is_leading_ambiguous(String s) {
    // Check that the remaining chars in ss[0] are not a hit for the leading
    // char of any other leading op.
    for( int i=1; i<s.length(); i++ ) {
      String t = s.substring(i)+"_";
      if( OPERS.get(t)!=null )
        throw unimpl(); // return false; // Ambiguous
    }
    return false;
  }

  // Balanced op.  Some amount of "[{<" in s0, and the reverse ">}]" in s1.
  // "{<" cannot appear as 1st char in s0.
  private static boolean is_bal_op(String s0, String s1) {
    throw unimpl();
  }

  // Lookup the tok as a unary operator, or the first part of a balanced
  // operator.  Return NULL if no match, otherwise return the Oper with the
  // longest matching name.  Adds '_' as the last character.
  public static Oper pre_bal(String tok, boolean prims) {
    if( tok==null ) return null;
    byte c = (byte)tok.charAt(0);
    if( !isOp0(c) ) return null; // Must be an op character
    if( prims && c=='$' ) return null; // Disallow $$ operator during prim parsing; ambiguous with $$java_class_name
    for( int i=tok.length(); i>0; i-- ) {
      Oper op = OPERS.get(tok.substring(0,i)+"_");
      if( op!=null ) return op;
    }
    return null;                // No leading oper
  }

  // Lookup the tok as a unbalanced binary operator.  Return NULL if no match,
  // or the Oper with the longest matching name and prec.  Adds '_' as the
  // first and last characters.
  public static Oper bin_op( String tok, int prec ) {
    if( tok==null ) return null;
    for( int i=tok.length(); i>0; i-- ) {
      Oper binop = OPERS.get(("_"+tok.substring(0,i)+"_").intern());
      if( binop!=null && binop._prec==prec ) return binop;
    }
    return null;
  }
  // Lookup the tok as a unbalanced binary operator.  Return NULL if no match,
  // or the Oper with the longest matching name and any prec.  Adds '_' as the
  // first and last characters.
  public static Oper bin_op( String tok ) { return bin_op(tok,prec(tok.charAt(0))); }

  // Lookup a balanced operator, either binary or trinary.  Returns NULL if no
  // match, or the Oper with the longest matching name and prec.  Adds '_' as
  // needed.
  public static Oper balanced( String tok0, String tok1 ) {
    throw unimpl();
  }

  // Chosen op can be shorter than tok, adjust Parsers _x
  int adjustx(String tok) {
    return tok.length() - (_name.length()-_nargs);
  }
}
