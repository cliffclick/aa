package com.cliffc.aa;

/** an implementation of language AA
 */

// A basic implementation of 'eval'.
// TODO: rename class

public abstract class Exec {
  // Parse and type a file-level string.  Reset back to Env.<clinit> when done.
  // Suitable for repeated tests
  public static TypeEnv file( String src, String str ) { // Execute string

    TypeEnv te = go(Env.TOP,src,str);

    te._scope.unhook();
    te._scope.kill();
    Env.GVN.iter(GVNGCM.Mode.PesiCG);
    Env.top_reset();

    return te;
  }

  // Parse and type a string.  Can be nested.  In theory, will be eval() someday.
  // In theory, can keep the result node and promote them for the REPL.
  public static TypeEnv go( Env top, String src, String str ) { // Execute string
    Env e = new Env(top,false,top._scope.ctrl(),top._scope.mem());

    // Parse a program
    ErrMsg err = new Parse(src,false,e,str).prog();

    // Delete names before starting typing/optimization
    e._scope.keep();
    Env.GVN.add_flow_uses(e._scope);// Post-parse, revisit top-level called functions
    e.close();                // No more fields added to the parse scope

    // Type
    Env.GVN.iter(GVNGCM.Mode.PesiNoCG); // Pessimistic optimizations; might improve error situation
    Combo.opto();                    // Global Constant Propagation and Hindley-Milner Typing
    Env.GVN.iter(GVNGCM.Mode.PesiCG);// Re-check all ideal calls now that types have been maximally lifted
    Combo.opto();                    // Global Constant Propagation and Hindley-Milner Typing
    Env.GVN.iter(GVNGCM.Mode.PesiCG);// Re-check all ideal calls now that types have been maximally lifted
    //assert Type.intern_check();
    
    return e.gather_errors(err);
  }


  public static String dump() { return Env.START.dumprpo(false,false); } // Debugging hook
}
