package com.cliffc.aa;

/** an implementation of language AA
 */

public abstract class Exec {
  private static Parse P; // Debugging hook
  public static TypeEnv go( Env top, String src, String str ) { // Execute string
    try( TypeEnv te = open(top,src,str) ) { return te; }
  }
  // Caller must close TypeEnv
  static TypeEnv open( Env top, String src, String str ) { // Execute string
    return (P=new Parse(src,top,str)).go_whole();
  }

  public static String dump() { return Env.START.dumprpo(false); } // Debugging hook
}
