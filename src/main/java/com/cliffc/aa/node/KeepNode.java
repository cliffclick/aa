package com.cliffc.aa.node;

import com.cliffc.aa.type.*;

public class KeepNode extends Node {
  public KeepNode() { super(OP_KEEP); _val = _live = Type.ALL; add_def(this); }
  @Override public Type value() { return Type.ALL; }
  @Override public Type live () { return Type.ALL; }
  // Oddly: keeps you alive as you were before
  @Override public Type live_use( Node def ) { return def._live; }
  @Override public boolean equals(Object o) { return this==o; }
  @Override public boolean has_tvar() { return false; }
}

