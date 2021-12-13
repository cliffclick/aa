package com.cliffc.aa;

import com.cliffc.aa.node.StartNode;

import static com.cliffc.aa.AA.unimpl;

// Support for lexically scoped operator parsing.

// An oper is either "balanced op" with parts to the name, or is a uni-op, or
// a binary op with a precedence.

// TODO: Mostly half-baked, and could have a lot of support from Env moved into here
public class Oper {
  final String _name;           // Full name, with '_' where arguments go
  final byte _prec; // Precedence.  Not set for uniops and balanced ops.  Always > 0 for infix binary ops.
  
  Oper(String name, byte prec) { _name=name; _prec=prec; }
  byte op_prec() { return _prec; }
  
}
