package com.cliffc.aa;

/** an implementation of language AA
 */

public abstract class Exec {
  public static TypeEnv go( String src, String str ) { // Execute string
    TypeEnv te = new Parse(src,Env.top(),str).go();
    te._env.close();
    return te;
  }
}
