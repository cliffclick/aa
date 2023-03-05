package com.cliffc.aa.node;

import com.cliffc.aa.type.*;

public class KeepNode extends Node {
  public KeepNode() { super(OP_KEEP); _val = Type.ALL; _live = TypeMem.ALLMEM; add_def(this); }
  @Override public boolean is_mem() { return true; }
  @Override public Type value() { return Type.ALL; }
  // All memory, except kills
  @Override public Type live () { return RootNode.def_mem(this); }
  @Override public Type live_use( Node def ) {
    if( def.is_mem() ) return _live;
    if( def instanceof   StructNode ) return TypeStruct.ISUSED;
    if( def instanceof SetFieldNode ) return TypeStruct.ISUSED;
    if( def instanceof     LoadNode ) return TypeStruct.ISUSED;
    if( def instanceof    FieldNode fld && fld._val instanceof TypeStruct )
      return TypeStruct.ISUSED; // Fields from CLAZZes can return Struct overloads
    return Type.ALL;
  }
  @Override public boolean equals(Object o) { return this==o; }
  @Override public boolean has_tvar() { return false; }
}

