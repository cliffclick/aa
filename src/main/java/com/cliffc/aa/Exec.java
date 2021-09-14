package com.cliffc.aa;

/** an implementation of language AA
 */


public abstract class Exec {
  public static TypeEnv go( Env top, String src, String str ) { // Execute string
    // Parse a program
    ErrMsg err = new Parse(src,false,top,str).prog();

    // Delete names at the top scope before starting typing/optimization
    top._scope.keep();
    Env.GVN.add_flow_uses(top._scope);// Post-parse, revisit top-level called functions
    top.close();                // No more fields added to the top parse scope

    // Type
    Env.GVN.iter(GVNGCM.Mode.PesiNoCG); // Pessimistic optimizations; might improve error situation
    Env.DEFMEM.unkeep(2);            // Memory not forced alive
    Combo.opto();                    // Global Constant Propagation and Hindley-Milner Typing
    Env.GVN.iter(GVNGCM.Mode.PesiCG);// Re-check all ideal calls now that types have been maximally lifted
    Combo.opto();                    // Global Constant Propagation and Hindley-Milner Typing
    Env.GVN.iter(GVNGCM.Mode.PesiCG);// Re-check all ideal calls now that types have been maximally lifted
    top._scope.unkeep();
    //assert Type.intern_check();
    return top.gather_errors(err);
  }

  
  public static String dump() { return Env.START.dumprpo(false,false); } // Debugging hook
}
