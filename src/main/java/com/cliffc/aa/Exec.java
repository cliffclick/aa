package com.cliffc.aa;

import com.cliffc.aa.node.Node;

/** an implementation of language AA
 */

public abstract class Exec {
  public static TypeEnv go( String src, String str ) { // Execute string
    Type t;
    Env par;
    try( Env env = Env.top() ) {
      Parse p = new Parse(src,env,str);
      Node n = p.go();            // Evaluated expression logic
      t = Env._gvn.type(n);       // pessimistic type
      if( n._uses._len == 0 ) Env._gvn.kill(n); // Dead now
      par = env._par;
    } // Close/del env on both normal and exceptions (parse errors)
    return new TypeEnv(t,par);  // Return result type; pretty sure I should return the Env during eval, but then not sure when to pop/delete it
  }
}
