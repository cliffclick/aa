package com.cliffc.aa;

import static com.cliffc.aa.AA.*;

/** an implementation of language AA
 */

// A basic implementation of 'eval'.

public abstract class Exec {
  // Parse and type a file-level string.  Reset back to Env.<clinit> when done.
  // Suitable for repeated tests
  public static TypeEnv file( String src, String str, int rseed, boolean do_gcp, boolean do_hmt ) { // Execute string

    TypeEnv te = go(Env.TOP,src,str,rseed,do_gcp,do_hmt);

    // Kill, cleanup and reset for another parse
    Env.top_reset();            // Hard reset

    return te;
  }

  // Parse and type a string.  Can be nested.  In theory, will be eval() someday.
  // In theory, can keep the result node and promote them for the REPL.
  public static TypeEnv go( Env top, String src, String str, int rseed, boolean do_gcp, boolean do_hmt ) { // Execute string
    AA.RSEED = rseed;
    AA.DO_GCP = do_gcp;
    AA.DO_HMT = do_hmt;
    AA.LIFTING = true;
    Env e = Env.FILE = new Env(top,null,0,top._scope.ctrl(),top._scope.mem(),top._scope.ptr(), null);
    // Parse a program
    ErrMsg err = new Parse(src,false,e,str).prog();

    // Move final results into Root; close out the top scope
    Env.ROOT.set_def(CTL_IDX,e._scope.ctrl());
    Env.ROOT.set_def(MEM_IDX,e._scope.mem ());
    Env.ROOT.set_def(REZ_IDX,e._scope.rez ());
    Env.GVN.add_flow(Env.ROOT);
    Env.GVN.add_flow_uses(Env.ROOT);
    e.close();      // No more fields added to the parse scope

    AA.LIFTING = false;
    Combo.opto(); // Global Constant Propagation and Hindley-Milner Typing

    AA.LIFTING = true;
    Env.GVN.iter(); // Re-check all ideal calls now that types have been maximally lifted

    Env.FILE=null;

    return e.gather_errors(err);  // Gather errors and/or program typing
  }


  public static String dump() { return Env.ROOT.dumprpo(false,false,false); } // Debugging hook
}
