package com.cliffc.aa;

/** an implementation of language AA
 */

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
    System.out.println("AA built: "+ABV.compiledOn());
    if( args.length > 0 ) System.out.println(Exec.go("args",String.join(" ",args))._t.toString());
    else REPL.go();
  }
}
