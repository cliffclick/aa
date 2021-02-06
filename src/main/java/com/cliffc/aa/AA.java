package com.cliffc.aa;

import com.cliffc.aa.node.Node;

/** an implementation of language AA
 */

@SuppressWarnings("unchecked")
public abstract class AA {
  public static RuntimeException unimpl() { return unimpl("unimplemented"); }
  public static RuntimeException unimpl(String msg) { throw new RuntimeException(msg); }
  // Indices common between Nodes & Types & TVars.
  public static final int CTL_IDX=0; // Often 0 is just used directly
  public static final int MEM_IDX=1; // Memory index
  public static final int DSP_IDX=2; // Display index to calls
  public static final int REZ_IDX=2; // Result from returns, same as DSP_IDX
  public static final int ARG_IDX=3; // Start of user-visible args

  private static final AbstractBuildVersion ABV;
  static {
    AbstractBuildVersion abv = null;
    try {
      Class klass = Class.forName("com.cliffc.aa.BuildVersion");
      java.lang.reflect.Constructor constructor = klass.getConstructor();
      abv = (AbstractBuildVersion) constructor.newInstance();
    } catch (Exception ignore) { }
    ABV = abv;
  }
  public static void main( String[] args ) {
    System.out.println(ABV.toString());
    if( args.length > 0 ) System.out.println(Exec.go(Env.file_scope(Env.top_scope()),"args",String.join(" ",args))._t.toString());
    else REPL.go();
  }
  public static boolean DEBUG = true;
  public static <T> T p(T x, String s) {
    if( !AA.DEBUG ) return x;
    System.err.println(s);
    return x;
  }
  public static String p    () { return Env.START.dumprpo(false,false); }  // Debugging hook
  public static String plive() { return Env.START.dumprpo(false,true ); }  // Debugging hook
  public static Node f(int uid) { return Env.START.find(uid); }        // Debugging hook
  public static int UID=-1;  
}
