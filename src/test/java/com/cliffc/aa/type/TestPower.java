package com.cliffc.aa.type;

import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;


public class TestPower {
  // temp/junk holder for "instant" junits, when debugged moved into other tests
  @Test public void testType() {

    PowerSet ps0 = PowerSet.make(17);
    assertEquals("[17]",ps0.toString());
    
    PowerSet ps1 = PowerSet.make(19);
    assertEquals("[19]",ps1.toString());
    
    PowerSet ps2 = ps1.OR(ps0);
    assertEquals("[17,19]",ps2.toString());
    
  }
}
