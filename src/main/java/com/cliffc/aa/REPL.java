package com.cliffc.aa;

import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;

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
      if( te._errs == null ) {
        Type t = te._t;
        if( t instanceof TypeMemPtr )
          t = te._tmem.ld((TypeMemPtr)t); // Peek thru pointer
        SB sb = t.str(new SB(),null,te._tmem); // Print what we see, with memory
        System.out.println( sb.toString() );
      } else
        System.out.print( te._errs.get(0) );
      System.out.print(prompt);
      System.out.flush();
    }
  }
}
