package com.cliffc.aa;

import com.cliffc.aa.node.Node;

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
        Parse p = new Parse("stdin",env,line);
        Node n = p.go();
        Type t = p._gvn.type(n); //pessimistic type
        System.out.println(t.toString());
      } catch( IllegalArgumentException iae ) {
        System.err.println(iae);
      }
    }
  }
}
