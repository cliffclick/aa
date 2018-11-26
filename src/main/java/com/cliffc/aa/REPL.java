package com.cliffc.aa;

import java.util.Scanner;

/** an implementation of language AA
 */

public abstract class REPL {
  private static final String prompt="> ";
  private static final String proerr="--";
  public static void go( ) {
    Env env = Env.top();
    Scanner stdin = new Scanner(System.in);
    System.out.print(prompt);
    System.out.flush();
    while( stdin.hasNextLine() ) {
      String line = stdin.nextLine();
      TypeEnv te = new Parse("stdin",env,line).go_partial();
      if( te._errs == null ) {
        System.out.println( te._t.toString() );
      } else {
        String err = te._errs.at(0);
        String[] msglineoff = err.split("\n");
        System.out.println( proerr + msglineoff[3] + '\n' + msglineoff[1] );
      }
      env._scope.set_def(0,env._scope,Env._gvn);
      System.out.print(prompt);
      System.out.flush();
    }
  }
}
