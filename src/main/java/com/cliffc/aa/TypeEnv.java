package com.cliffc.aa;

import com.cliffc.aa.tvar.TV2;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.type.TypeStruct;

import java.util.ArrayList;

public class TypeEnv{
  final Type _t;
  final TypeStruct _formals;
  final TypeMem _tmem;
  final TV2 _hmt;
  final ArrayList<ErrMsg> _errs;
  TypeEnv( Type t, TypeStruct formals, TypeMem tmem, TV2 hmt, ArrayList<ErrMsg> errs ) {
    _t=t; _formals=formals; _tmem=tmem; _hmt=hmt; _errs = errs;
  }
}
