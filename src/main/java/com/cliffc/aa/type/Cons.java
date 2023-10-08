package com.cliffc.aa.type;

import static com.cliffc.aa.type.TypeFld.Access;

// A collection of global constants to break cyclic class dependencies
public abstract class Cons {

  public static final TypeStruct CLZ_CLZ = TypeStruct.make(false,Type.ANY,TypeFlds.EMPTY);
  public static final TypeMemPtr CLZ_TMP = TypeMemPtr.make_con(BitsAlias.CLZ,true,CLZ_CLZ);
  public static final TypeFld CLZ_FLD = TypeFld.make(TypeFld.CLZ,CLZ_TMP,Access.Final);

  
}
