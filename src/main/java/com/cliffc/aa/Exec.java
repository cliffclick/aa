package com.cliffc.aa;

import com.cliffc.aa.node.Node;

/** an implementation of language AA
 */

// A basic implementation of 'eval'.
// TODO: rename class

public abstract class Exec {
  // Parse and type a file-level string.  Reset back to Env.<clinit> when done.
  // Suitable for repeated tests
  public static TypeEnv file( String src, String str, int rseed, boolean do_gcp, boolean do_hmt ) { // Execute string

    TypeEnv te = go(Env.TOP,src,str,rseed,do_gcp,do_hmt);

    // Kill, cleanup and reset for another parse
    Env.top_reset();                   // Hard reset

    return te;
  }

  // Parse and type a string.  Can be nested.  In theory, will be eval() someday.
  // In theory, can keep the result node and promote them for the REPL.
  public static TypeEnv go( Env top, String src, String str, int rseed, boolean do_gcp, boolean do_hmt ) { // Execute string
    AA.RSEED = rseed;
    AA.DO_GCP = do_gcp;
    AA.DO_HMT = do_hmt;
    Env e = Env.FILE = new Env(top,null,false,top._scope.ctrl(),top._scope.mem(),top._scope.stk(),null);

    // Parse a program
    ErrMsg err = new Parse(src,false,e,str).prog();

    // Close file scope; no program text in this file, so no more fields to add.
    e._scope.stk().close();
    int sidx = e._scope.push();// Hook result, not dead
    e.close();                // No more fields added to the parse scope; finish off Iter

    Combo.opto();      // Global Constant Propagation and Hindley-Milner Typing

    Env.GVN.iter(); // Re-check all ideal calls now that types have been maximally lifted

    Env.FILE=null;

    TypeEnv rez = e.gather_errors(err);  // Gather errors and/or program typing

    // Cleanup top (normal user) scope
    Node scope = Node.pop(sidx);
    assert scope==rez._scope;
    // All edges removed, otherwise a self-cycle keeps alive
    while( scope.len()>0 ) scope.pop();
    Env.GVN.add_dead(scope);

    return rez;
  }


  public static String dump() { return Env.START.dumprpo(false,false); } // Debugging hook
}
