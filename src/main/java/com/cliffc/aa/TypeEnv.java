package com.cliffc.aa;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.node.ScopeNode;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.tvar.TV2;

import java.util.ArrayList;

public class TypeEnv{
  final ScopeNode _scope;
  final Type _t;
  final TypeMem _tmem;
  final TV2 _hmt;
  final ArrayList<ErrMsg> _errs;
  TypeEnv( ScopeNode scope, Type t, TypeMem tmem, TV2 hmt, ArrayList<ErrMsg> errs ) { _scope=scope; _t=t; _tmem=tmem; _hmt=hmt; _errs = errs; }
}
