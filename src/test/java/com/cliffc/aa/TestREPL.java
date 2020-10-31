package com.cliffc.aa;

import com.cliffc.aa.util.SB;
import org.junit.*;
import org.junit.contrib.java.lang.system.SystemErrRule;
import org.junit.contrib.java.lang.system.SystemOutRule;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;


public class TestREPL {
  // Replace STDIN/STDOUT and track them
  @Rule public final SystemOutRule sysOut = new SystemOutRule().enableLog().muteForSuccessfulTests();
  @Rule public final SystemErrRule sysErr = new SystemErrRule().enableLog().muteForSuccessfulTests();

  private String _prog;
  @Before public void open_repl() {
    REPL.init();
    _prog = "";
    // Drain the initial prompt string so tests do not expect one
    String actual = sysOut.getLog();
    String expected = REPL.prompt;
    assertEquals(expected,actual);
    sysOut.clearLog();
    assertTrue(sysErr.getLog().isEmpty());
  }

  @After public void close_repl() {
  }

  // Does the REPL test work?
  @Test public void testREPL00() {
    test("2", "2");
  }

  // Basic REPL, with errors & recovery
  @Test public void testREPL01() {
    test("2+3", "5");
    test("x=3", "3");
    test("x*x", "9");
    testerr("y*y", "y*y", "Unknown ref 'y'",4,0);
    test("x=4", "4");
    testerr("x+x", "x=4", "Cannot re-assign final val 'x'",4,0);
    test("3+2", "5");
    test("sq={x->x*x}", "[sq=*{x -> }]");
    test("sq 5","25");
    testerr("sq \"abc\"", "sq={x->x*x}", "*\"abc\" is none of (flt64,int64)", 6,7);
    testerr("x", "x=4", "Cannot re-assign final val 'x'",4,0);
  }

  // Requires multi-pass type inference.
  @Test public void testREPL02() {
    test("do={pred->{body->pred()?body():^; do pred body}}","[do=*{pred -> }]");
    test("sum:=0; i:=0; do {i++ < 100} {sum:=sum+i}; sum","int64");
  }

  // Start of a HashTable class.
  @Test public void testREPL03() {
    test   ("hash := {@{ tab = [3]; get = { key -> idx = key.hash(); tab[idx] } } }","[hash=*{ -> }]");
    testerr("junk := hash:int","junk := hash:int","[hash=*{ -> }] is not a int64",2,12);
    testerr("hash.tab","hash.tab","Unknown field '.tab'",2,5);
    test   ("x := hash()","@{tab==*[3]0/obj?; get==[get=*{key -> }]}");
    testerr("x.#tab","x.#tab","Unknown ref 'tab'",3,3);
    test   ("#x.tab","3");
  }

  @Test public void testREPL04() throws IOException {
    String hash_src = new String(Files.readAllBytes( Paths.get("test/java/com/cliffc/aa","HashTable.aa")));
    test(hash_src,"[HashTable=*{ -> }]");
    test("htab = HashTable()","@{_tab=*[7]0/obj; get=[get=*{key -> }]; put=[put=*{key val -> }]}");
    test("htab.put(\"Monday\",1)","0");
  }

  // Jam the code into STDIN, run the REPL one-step, read the STDOUT and compare.
  private void test( String partial, String expected ) {
    _prog = REPL.go_one(_prog,partial);
    String actual = sysOut.getLog();
    String exp = expected+System.lineSeparator()+REPL.prompt;
    assertEquals(exp,actual);
    sysOut.clearLog();
    assertTrue(sysErr.getLog().isEmpty());
  }
  // Jam the code into STDIN, run the REPL one-step, read the STDOUT and compare.
  // Includes the lengthy error message.
  private void testerr( String partial, String parerr, String expected, int line, int cur_off ) {
    _prog = REPL.go_one(_prog,partial);
    String actual = sysOut.getLog();
    String cursor = new String(new char[cur_off]).replace('\0', ' ');
    String exp = new SB().p("stdin:").p(line).p(":").p(expected).nl().p(parerr).p(';').nl().p(cursor).p('^').nl().p(REPL.prompt).toString();
    assertEquals(exp,actual);
    sysOut.clearLog();
    assertTrue(sysErr.getLog().isEmpty());
  }
}
