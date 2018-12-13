package com.cliffc.aa.node;

import com.cliffc.aa.util.Bits;
import org.junit.Ignore;
import org.junit.Test;

import java.util.HashMap;

import static org.junit.Assert.*;

public class TestNode {
  // temp/junk holder for "instant" junits, when debugged moved into other tests
  @Test public void testNode() {
    
  }

  // Major test for monotonic behavior from value() calls.  Required to prove
  // correctness & linear-time speed from GCP & a major part of GVN.iter().
  // (for GVN.iter(), ideal() calls ALSO have to be monotonic but using a
  // different metric thats harder to test for).
  @Test public void testMonotonic() {
    // How this works: for all Node.value() calls, for all input types, if the
    // input type changes monotonically, so does the output type.  Many input
    // types are illegal for many Nodes, and can/should be asserted for by the
    // Node.  However, all legal inputs should produce an output with the
    // monotonicity invariant.
    
    
  }
  
}
