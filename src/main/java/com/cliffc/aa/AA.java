package com.cliffc.aa;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.Type;

/** an implementation of language AA
 */

@SuppressWarnings("unchecked")
public abstract class AA {
  public static RuntimeException unimpl() { return unimpl("unimplemented"); }
  public static RuntimeException unimpl(String msg) { throw new RuntimeException(msg); }
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
}
