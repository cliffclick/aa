package com.cliffc.aa;

import com.cliffc.aa.node.*;

import static com.cliffc.aa.AA.*;

/** an implementation of language AA
 */

// A basic implementation of 'eval'.

public abstract class Exec {
  // Parse and type a file-level string.  Reset back to Env.<clinit> when done.
  // Suitable for repeated tests
  public static TypeEnv test( String src, String str, int rseed, boolean do_gcp, boolean do_hmt ) { // Execute string
    AA.RSEED = rseed;
    AA.DO_GCP = do_gcp;
    AA.DO_HMT = do_hmt;
    AA.LIFTING = true;
    // Kill, cleanup and reset for another parse
    Env.top_reset();            // Hard reset

    //
    return go_one(src,str);
  }

  public static TypeEnv go_one( String src, String str ) { // Execute string from whole cloth
    return go(Env.PRIM,Env.CTL_0,Env.MEM_0,src,str);
  }

  // Parse and type a string.  Can be nested.  In theory, will be eval() someday.
  // In theory, can keep the result node and promote them for the REPL.
  public static TypeEnv go( Env top, Node ctrl, Node mem, String src, String str ) { // Execute string
    Env e = Env.FILE = new Env(top,null,1,ctrl,mem,top._scope.ptr(), null);
    // Parse a program
    ErrMsg err = new Parse(src,e,str).prog();

    // Move final results into Root; close out the top scope
    Env.ROOT.setDef(CTL_IDX,e._scope.ctrl());
    Env.ROOT.setDef(MEM_IDX,e._scope.mem ());
    Env.ROOT.setDef(REZ_IDX,e._scope.rez ());
    e.close();      // No more fields added to the parse scope

    Env.ROOT.walk( Env.GVN::add_work_new );
    
    // Post-parse pre-Combo iterative peepholes
    Env.GVN.iter();

    Combo.opto(); // Global Constant Propagation and Hindley-Milner Typing

    Env.GVN.iter(); // Re-check all ideal calls now that types have been maximally lifted

    Env.FILE=null;

    return e.gather_errors(err);  // Gather errors and/or program typing
  }

}
