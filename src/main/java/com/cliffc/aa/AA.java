package com.cliffc.aa;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.node.NodePrinter;

/** an implementation of language AA
 */

public abstract class AA {
  public static RuntimeException TODO() { return TODO("unimplemented"); }
  public static RuntimeException TODO( String msg) { throw new RuntimeException(msg); }
  // Indices common between Nodes & Types & TVars.
  public static final int CTL_IDX=0; // Often 0 is just used directly
  public static final int MEM_IDX=1; // Memory index
  public static final int DSP_IDX=2; // Display index to calls
  public static final int REZ_IDX=2; // Result from returns, same as DSP_IDX
  public static final int ARG_IDX=3; // Start of user-visible args

  public static int RSEED=0;    // Global random seed for worklist draws
  public static boolean DO_GCP=true, DO_HMT = true; // Global type-precision controllers
  public static boolean LIFTING = true; // Global type-phase


  private static final AbstractBuildVersion ABV;
  static {
    AbstractBuildVersion abv = null;
    try {
      Class klass = Class.forName("com.cliffc.aa.BuildVersion");
      java.lang.reflect.Constructor constructor = klass.getConstructor();
      abv = (AbstractBuildVersion) constructor.newInstance();
    } catch (Exception ignore) { }
    ABV = abv;
  }
  public static void main( String[] args ) {
    System.out.println(ABV.toString());
    // Command line program
    if( args.length > 0 ) {
      TypeEnv te = Exec.go_one("args",String.join(" ",args));
      if( te._errs!=null ) System.out.println(te._errs);
      else {
        System.out.println(te._hmt.toString());
        System.out.println(te._t  .toString());
      }
    } else {
      REPL.go();
    }
  }

  // Debug printers and finders
  public static boolean DEBUG = true;
  public static <T> T p(T x, String s) {
    if( !AA.DEBUG ) return x;
    System.err.println(s);
    return x;
  }
  public static String p() { return NodePrinter.prettyPrint(Env.ROOT,99,false); }  // Debugging hook
  public static Node f(int uid) { return Env.ROOT.find(uid); } // Debugging hook
  public static int UID=-1;     // Used to breakpoint on a named Node creation

  // assert AA.once_per() || ...expensive;
  private static int ASSERT_CNT;
  public static boolean once_per() { return once_per(8); }
  public static boolean once_per(int log) {
    return (ASSERT_CNT++ & ((1L<<log)-1))!=0;
  }
  static void reset() { ASSERT_CNT=0; }
}
