package com.cliffc.aa;

/** an implementation of language AA
 */

public abstract class Exec {
  public static TypeEnv go( String src, String str ) { // Execute string
    try( TypeEnv te = new Parse(src,Env.top(),str).go_whole() ) { return te; }
  }
}
