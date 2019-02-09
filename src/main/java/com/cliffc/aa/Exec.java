package com.cliffc.aa;

/** an implementation of language AA
 */

public abstract class Exec {
  public static TypeEnv go( Env top, String src, String str ) { // Execute string
    try( TypeEnv te = new Parse(src,top,str).go_whole() ) { return te; }
  }
}
