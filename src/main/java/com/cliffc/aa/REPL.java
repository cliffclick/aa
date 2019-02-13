package com.cliffc.aa;

import java.util.Scanner;

/** an implementation of language AA
 */

public abstract class REPL {
  private static final String prompt="> ";
  public static void go( Env env ) {
    Scanner stdin = new Scanner(System.in);
    System.out.print(prompt);
    System.out.flush();
    while( stdin.hasNextLine() ) {
      String line = stdin.nextLine();
      TypeEnv te = new Parse("stdin",env,line).go_partial();
      System.out.print( te._errs == null ? te._t.toString()+"\n" : te._errs.at(0) );
      env._scope.set_def(0,env._scope,Env.GVN);
      System.out.print(prompt);
      System.out.flush();
    }
  }
}
