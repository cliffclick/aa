package com.cliffc.aa;

import com.cliffc.aa.node.Node;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;

import java.util.ArrayList;

public class TypeEnv implements AutoCloseable {
  final Type _t;
  final TypeMem _tmem;
  final Env _env;
  final ArrayList<Node.ErrMsg> _errs;
  TypeEnv( Type t, TypeMem tmem, Env env, ArrayList<Node.ErrMsg> errs ) { _t=t; _tmem=tmem; _env=env; _errs = errs; }
  @Override public void close() { _env.close(); }
}
