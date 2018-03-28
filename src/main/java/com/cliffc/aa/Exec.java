package com.cliffc.aa;

import com.cliffc.aa.node.Node;

/** an implementation of language AA
 */

public abstract class Exec {
  public static TypeEnv go( String src, String str ) { // Execute string
    Env env = Env.top();
    GVNGCP gvn = new GVNGCP(false);
    Parse p = new Parse(src,env,gvn,str);
    Node n = p.go();
    return new TypeEnv(p._gvn.type(n)/*pessimistic type*/,env);
  }
}
