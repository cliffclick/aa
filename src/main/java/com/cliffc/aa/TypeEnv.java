package com.cliffc.aa;

import com.cliffc.aa.Env;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.Ary;

public class TypeEnv {
  final Type _t;  final Env _env;  final Ary<String> _errs;
  TypeEnv( Type t, Env env, Ary<String> errs ) { _t=t; _env=env; _errs = errs; }
}
