package com.cliffc.aa.node;

import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.unimpl;

// Takes a static field name, a TypeStruct, a field value and produces a new TypeStruct
public class SetFieldNode extends Node {

  SetFieldNode(Node struct, String name, Node val) { super((byte)-1,struct,val); }

  @Override public Type value() { throw unimpl(); }

}
