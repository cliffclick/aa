package com.cliffc.aa;

import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.Util;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.Arrays;

import static org.junit.Assert.assertEquals;

public class TestAST {
  @Test public void testAll() throws IOException {
    testBasic();
  }

  public void testBasic() throws IOException { testSet("Basic"); }

  public void testSet(String filter) throws IOException {
    File folder = new File("src/test/java/com/cliffc/aa/ast");
    File[] tests = folder.listFiles(file -> file.getName().endsWith("aa") && file.getName().contains(filter));
    Arrays.sort(tests, (s0,s1) -> Util.alphanumCompare(s0.toString(),s1.toString()));
    for( File f : tests ) {
      testOne(0,f);
    }
  }

  public void testOne( int rseed, File f ) throws IOException {
    String prog = Files.readString( f.toPath());

    TypeEnv te = Exec.test("test",prog,rseed,true,true);
    if( te._errs == null ) {
      String exgcp = get_expected(prog,"// GCP: ",false);
      Type expect = Type.valueOf(exgcp);
      Type actual = te._t;
      assertEquals(expect,actual);
      // TODO: Get expected HMT

      //Type rez = root.eval(null);
      //assertEquals(f.toString(),exeval,rez.toString());
      throw AA.TODO();

    } else {
      throw AA.TODO();
    }
  }

  private static String get_expected(String prog, String marker, boolean opt) {
    int idx = prog.indexOf(marker);
    if( idx == -1 ) {
      if( opt ) return null;
      throw new RuntimeException("Test file lacks a "+marker+" comment");
    }
    int eol = prog.indexOf('\n', idx+1);
    return prog.substring(idx+marker.length(),eol).trim();
  }

}
