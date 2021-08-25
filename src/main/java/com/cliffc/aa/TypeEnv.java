package com.cliffc.aa;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.tvar.TV2;

import java.util.ArrayList;

public class TypeEnv implements AutoCloseable {
  final Type _t;
  final TypeMem _tmem;
  final TV2 _hmt;
  final Env _env;
  final ArrayList<Node.ErrMsg> _errs;
  TypeEnv( Type t, TypeMem tmem, TV2 hmt, Env env, ArrayList<Node.ErrMsg> errs ) { _t=t; _tmem=tmem; _hmt=hmt; _env=env; _errs = errs; }
  @Override public void close() { _env.close(); }
}
