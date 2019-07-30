package com.cliffc.aa;

/** an implementation of language AA
 */

@SuppressWarnings("unchecked")
public abstract class AA {
  public static RuntimeException unimpl() { throw new RuntimeException("unimplemented"); }
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
    Env top = Env.top();
    if( args.length > 0 ) System.out.println(Exec.go(top,"args",String.join(" ",args))._t.toString());
    else REPL.go(top);
  }
}
