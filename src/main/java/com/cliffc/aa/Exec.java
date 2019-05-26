package com.cliffc.aa;

/** an implementation of language AA
 */

public abstract class Exec {
  public static TypeEnv go( Env top, String src, String str ) { // Execute string
    try( TypeEnv te = open(top,src,str) ) { return te; }
  }
  // Caller must close TypeEnv
  public static TypeEnv open( Env top, String src, String str ) { // Execute string
    return new Parse(src,top,str).go_whole();
  }
  
}
