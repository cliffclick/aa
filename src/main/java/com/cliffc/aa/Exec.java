package com.cliffc.aa;

/** an implementation of language AA
 */

public abstract class Exec {
  public static TypeEnv go( String src, String str ) { // Execute string
    Env env = Env.top();
    Prog p = new Parse(src,env,str).go();
    p = p.resolve();
    return new TypeEnv(p.go(),env);
  }
}
