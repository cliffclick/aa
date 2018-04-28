package com.cliffc.aa;

import java.util.Scanner;

/** an implementation of language AA
 */

public abstract class REPL {
  private static final String prompt="> ";
  public static void go( ) {
    Env env = Env.top();
    Scanner stdin = new Scanner(System.in);
    System.out.print(prompt);
    System.out.flush();
    while( stdin.hasNextLine() ) {
      String line = stdin.nextLine();
      TypeEnv te = new Parse("stdin",env,line).go();
      System.out.println( te._errs == null ? te._t.toString() : te._errs.toString());
      env._scope.set_def(0,env._par._scope,Env._gvn);
      System.out.print(prompt);
      System.out.flush();
    }
  }
}
