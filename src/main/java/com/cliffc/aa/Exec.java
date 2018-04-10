package com.cliffc.aa;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.node.TmpNode;

/** an implementation of language AA
 */

public abstract class Exec {
  public static TypeEnv go( String src, String str ) { // Execute string
    Type t;
    Env par;
    try( Env env = Env.top(); TmpNode tmp = new TmpNode() ) {
      Parse p = new Parse(src,env,str);
      Node n = p.go();            // Evaluated expression logic
      tmp.add_def(n);             // Hook, so not deleted
      //Env._gvn.iter();            // Pessimistic optimizations; might improve
      Node n2 = tmp.at(0);        // New and improved n
      t = Env._gvn.type(n2);      // pessimistic type
      par = env._par;             // Pop 
    } // Close/del env on both normal and exceptions (parse errors)
    return new TypeEnv(t,par);  // Return result type; pretty sure I should return the Env during eval, but then not sure when to pop/delete it
  }
}
