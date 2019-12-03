package com.cliffc.aa;

import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeObj;
import com.cliffc.aa.util.Ary;

public class TypeEnv implements AutoCloseable {
  final Type _t;
  final TypeObj _tobj;
  final Env _env;
  final Ary<String> _errs;
  TypeEnv( Type t, TypeObj tobj, Env env, Ary<String> errs ) { _t=t; _tobj=tobj; _env=env; _errs = errs; }
  @Override public void close() { _env.close(); }
}
