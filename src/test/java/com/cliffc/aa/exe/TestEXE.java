package com.cliffc.aa.exe;

import com.cliffc.aa.tvar.TV3;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.Arrays;

import static org.junit.Assert.assertEquals;

public class TestEXE {
  @Test public void testAll() throws IOException {
    File folder = new File("src/test/java/com/cliffc/aa/exe");
    File[] tests = folder.listFiles(file -> file.getName().endsWith("aa"));
    Arrays.sort(tests);
    for( File f : tests ) {
      //System.out.println(f);
      String prog = Files.readString( f.toPath());
      String extype = get_expected(prog,"// Type: ");
      String exeval = get_expected(prog,"// Eval: ");

      try {
        EXE.Root root = EXE.compile(prog,0,true,true);
        TV3 tv = root.tvar();
        assertEquals(extype,tv.p());
      
        try {
          EXE.Val rez = root.eval(null);
          assertEquals(exeval,rez.toString());
        } catch( NullPointerException npe ) {
          assertEquals(exeval,"CRASH"); // Some are expected
        }
        
      } catch( IllegalArgumentException iae ) {
        // Compile fails as expected
        assertEquals(extype,iae.getMessage());
      }
    }
  }

  private static String get_expected(String prog, String marker) {
    int idx = prog.indexOf(marker);
    if( idx == -1 ) throw new RuntimeException("Test file lacks a "+marker+" comment");
    int eol = prog.indexOf('\n', idx+1);
    return prog.substring(idx+marker.length(),eol).trim();
  }
}
