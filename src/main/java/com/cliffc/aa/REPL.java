package com.cliffc.aa;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.node.RootNode;

import java.util.Scanner;

/** an implementation of language AA
 */

public abstract class REPL {
  private static final String prompt="> ";
  public static void go( ) {
    try( Env env = Env.top() ) {
   
      Scanner stdin = new Scanner(System.in);
      System.out.print(prompt);
      System.out.flush();
      while( stdin.hasNextLine() ) {
        String line = stdin.nextLine();
        try { 
          Parse p = new Parse("stdin",env,line);
          Node n = p.go();
          Type t = Env._gvn.type(n); //pessimistic type
          System.out.println(t.toString());
          System.out.print(prompt);
          System.out.flush();
        } catch( IllegalArgumentException iae ) {
          System.err.println(iae);
          System.out.print(prompt);
          System.out.flush();
        }
      }

    }
  }
}
