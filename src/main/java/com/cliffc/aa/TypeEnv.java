package com.cliffc.aa;

import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;
import com.cliffc.aa.util.Ary;

public class TypeEnv implements AutoCloseable {
  final Type _t;
  final TypeMem _tmem;
  final Env _env;
  final Ary<String> _errs;
  TypeEnv( Type t, TypeMem tmem, Env env, Ary<String> errs ) { _t=t; _tmem=tmem; _env=env; _errs = errs; }
  @Override public void close() { _env.close(); }
}
