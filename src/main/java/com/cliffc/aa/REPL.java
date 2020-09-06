package com.cliffc.aa;

import com.cliffc.aa.type.*;
import com.cliffc.aa.util.*;

import java.util.Scanner;

/** an implementation of language AA
 */

public abstract class REPL {
  public static final String prompt="> ";
  public static String go( ) {
    String prog = "";
    init();
    Scanner stdin = new Scanner(System.in);
    while( stdin.hasNextLine() )
      prog = go_one(prog,stdin.nextLine());
    return prog;
  }

  static void init() {
    System.out.print(prompt);
    System.out.flush();
  }

  static String go_one( String prog, String line ) {
    String prog2 = prog+line+";"+System.lineSeparator();
    TypeEnv te = Exec.go(Env.file_scope(Env.top_scope()),"stdin",prog2);
    if( te._errs == null ) {
      Type t = te._t;
      if( t instanceof TypeMemPtr )
        t = te._tmem.ld((TypeMemPtr)t); // Peek thru pointer
      SB sb = t.str(new SB(),new VBitSet(),te._tmem); // Print what we see, with memory
      System.out.println( sb.toString() );
      prog = prog2;
    } else
      System.out.print( te._errs.get(0) );
    System.out.print(prompt);
    System.out.flush();
    return prog;
  }

}
