package com.cliffc.aa.node;

import com.cliffc.aa.type.*;

public class KeepNode extends Node {
  public KeepNode() { super(OP_KEEP); _val=Type.ALL; _live=TypeMem.ALIVE; add_def(this); }
  @Override public Type value() { return Type.ALL; }
  @Override public TypeMem live() { return TypeMem.ALIVE; }
  @Override public TypeMem live_use( Node def ) { return def._live.basic_live() ? TypeMem.ALIVE : TypeMem.ALLMEM; }
  @Override public TypeMem all_live() { return TypeMem.ALIVE; }
  @Override public boolean equals(Object o) { return this==o; }
}

