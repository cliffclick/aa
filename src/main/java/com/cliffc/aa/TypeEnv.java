package com.cliffc.aa;

import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeObj;
import com.cliffc.aa.util.Ary;
import java.util.HashMap;

public class TypeEnv implements AutoCloseable {
  final Type _t;
  final TypeObj _tobj;
  final HashMap<String,Type> _types;
  final Env _env;
  final Ary<String> _errs;
  TypeEnv( Type t, TypeObj tobj, HashMap<String,Type> types, Env env, Ary<String> errs ) { _t=t; _tobj=tobj; _types=types; _env=env; _errs = errs; }
  @Override public void close() { _env.close(); }
}
