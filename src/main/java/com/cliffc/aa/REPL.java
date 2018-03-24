package com.cliffc.aa;

import java.util.Scanner;

/** an implementation of language AA
 */

public abstract class REPL {
  public static void go( ) {
    Env env = Env.top();
    Scanner stdin = new Scanner(System.in);
    while( stdin.hasNextLine() ) {
      String line = stdin.nextLine();
      try { 
        Node p = new Parse("stdin",env,line).go();
        throw AA.unimpl();
        //p = p.resolve();
        //Type t = p.go();
        //System.out.println(t.toString());
      } catch( IllegalArgumentException iae ) {
        System.err.println(iae);
      }
    }
  }
}
