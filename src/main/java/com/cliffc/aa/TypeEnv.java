package com.cliffc.aa;

import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.type.*;

import java.util.ArrayList;

public class TypeEnv{
  final Type _t;                // Return flow type
  final BitsFun _fidxs;         // Escaping fidxs
  final BitsAlias _aliases;     // Escaping aliases
  final TypeMem _tmem;          // Return mem type; the flow type is sharpened with this, so is probably redundant here
  final TV3 _hmt;               // Return HM type
  final ArrayList<ErrMsg> _errs;// Errors, if any
  TypeEnv( Type t, BitsFun fidxs, BitsAlias aliases, TypeMem tmem, TV3 hmt, ArrayList<ErrMsg> errs ) {
    _t=t; _fidxs = fidxs; _aliases = aliases; _tmem=tmem; _hmt=hmt; _errs = errs;
  }
}
