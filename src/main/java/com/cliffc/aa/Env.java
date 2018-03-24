package com.cliffc.aa;

import java.util.HashMap;
import com.cliffc.aa.util.Ary;

public class Env {
  private final Env _par;
  private final HashMap<String,Type> _vars;
  private Env( Env par ) { _par=par; _vars = new HashMap<>(); }

  private final static Env TOP = new Env(null);
  static {
    HashMap<String,Type> vs = TOP._vars;
    vs.put("pi",TypeFlt.Pi); // TODO: Needs to be under Math.pi
    for( TypeFun tf : Prim.TYPES )
      vs.put(tf._name,add(vs.get(tf._name),tf));
    for( TypeFun tf : TypeFun.TYPES )
      vs.put(tf._name,add(vs.get(tf._name),tf));
  }
  static Env top() { return new Env(TOP); }

  private static Type add( Type ts, Type x ) {
    if( ts == null ) return x;
    // Cannot use ts.join(x) here because mixing unary '-' and binary '-' falls
    // to SCALAR because different arg counts.
    if( ts instanceof TypeUnion ) {
      assert ((TypeUnion)ts)._any; // choice union
      return TypeUnion.make(true,new Ary<>(((TypeUnion)ts)._ts._ts).add(x));
    } else {
      return TypeUnion.make(true,ts,x); // choice union
    }
  }

  // Name lookup is the same for all variables, including function defs (which
  // are literally assigning a lambda to a ref).  Refs and Vars have a fixed
  // type (so can, for instance, assign a new function to a var as long as the
  // type signatures match).  Cannot re-assign to a ref, only var; vars only
  // available in loops.  
  
  // User can write TypeUnions, if they want over-loaded funcs, or name
  // collisions that are decerned by type.  Otherwise stop at 1st hit and
  // return.  If user wants to add a new '+' op with different type args but
  // does not want to shadow all the old '+', needs to do a re-assign op that
  // allows all the old hits as well: makes a typeunion on the spot merging the
  // prior old types and this type.
  Type lookup( String token, Type t ) {
    if( token == null ) return null;
    Type ts = _vars.get(token);
    if( ts == null )
      return _par == null ? null : _par.lookup(token,t);
    Type rez = ts.meet(t);      // Filter by required
    return Type.SCALAR.isa(rez) ? null : rez;
  }
}
