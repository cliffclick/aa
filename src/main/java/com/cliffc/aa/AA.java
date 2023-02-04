package com.cliffc.aa;

import com.cliffc.aa.node.Node;

/** an implementation of language AA
 */

public abstract class AA {
  public static RuntimeException unimpl() { return unimpl("unimplemented"); }
  public static RuntimeException unimpl(String msg) { throw new RuntimeException(msg); }
  // Indices common between Nodes & Types & TVars.
  public static final int CTL_IDX=0; // Often 0 is just used directly
  public static final int MEM_IDX=1; // Memory index
  public static final int DSP_IDX=2; // Display index to calls
  public static final int REZ_IDX=2; // Result from returns, same as DSP_IDX
  public static final int ARG_IDX=3; // Start of user-visible args

  public static int RSEED;              // Global random seed for worklist draws
  public static boolean DO_GCP, DO_HMT; // Global type-precision controllers
  public static boolean LIFTING;        // Global type-phase


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
      TypeEnv te = Exec.go(Env.TOP,"args",String.join(" ",args),1,true,true);
      if( te._errs!=null ) System.out.println(te._errs);
      else {
        System.out.println(te._hmt.toString());
        System.out.println(te._tmem.sharptr(te._t).toString());
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
  public static String p    () { return Env.ROOT.dumprpo(false,false,false); }  // Debugging hook
  public static String plive() { return Env.ROOT.dumprpo(false,true ,false); }  // Debugging hook
  public static Node f(int uid) { return Env.ROOT.find(uid); }        // Debugging hook
  public static int UID=-1;     // Used to breakpoint on a named Node creation

  // assert AA.once_per() || ...expensive;
  private static int ASSERT_CNT;
  private static int ONCE_PER=127; // Set to zero to fire every time
  public static boolean once_per() {
    return (ASSERT_CNT++ & ONCE_PER)!=0;
  }
}
