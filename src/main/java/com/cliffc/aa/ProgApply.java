package com.cliffc.aa;

import java.util.Arrays;

// Function application
public class ProgApply extends Prog {
  private final Prog   _fun;
  private final Prog[] _args;
  
  ProgApply( Prog fun, Prog... args ) {
    super(fun._t.ret());
    _fun = fun;
    _args=args;
  }
  // Execution of function application, is to eval the function and all
  // arguments left-to-right, then apply the function.
  @Override Type go( ) {
    assert _fun._t.base()==Type.TFUN; // Strongly typed as a function before eval
    TypeFun fun = (TypeFun)_fun.go(); // Must eval to a function (i.e., cast cannot fail)
    Type ts[] = new Type[_args.length];
    for( int i=0; i<_args.length; i++ )
      ts[i] = _args[i].go();
    return fun.apply(ts);
  }
  @Override Prog resolve_types(int[] x) {
    Prog fun = _fun.resolve_types(x);
    boolean con = fun._t._type == Type.TFUN;
    boolean progress = fun!=_fun;
    Type[] ts = new Type[_args.length];
    for( int i=0; i<_args.length; i++ ) {// Resolve the args
      Prog arg = _args[i].resolve_types(x);
      progress |= arg != _args[i];
      Type t = ts[i] = (_args[i]=arg)._t; 
      con &= t.is_con();
    }
    if( con && fun._t.is_pure() ) // All constants to a pure function; do the apply now
      return new ProgCon(((TypeFun)fun._t).apply(ts));
    return progress ? new ProgApply(fun,_args) : this;
  }
  // Program is type-correct, but has function choices where numeric
  // conversions might be required.  Pick a choice with the least amount of
  // conversions and remove it.
  @Override Prog remove_choice(int[]x) {
    // Recursive remove_choice
    Prog fun = _fun.remove_choice(x);
    if( fun != _fun ) return new ProgApply(fun,_args);
    for( int i=0; i<_args.length; i++ ) {
      Prog arg = _args[i].remove_choice(x);
      if( arg != _args[i] ) { _args[i] = arg; x[0]|=1; return new ProgApply(fun,_args); }
    }
    Type t = _fun._t.remove_choice(_args);
    if( t==null ) return this;
    x[0]|=1;
    return convert(t);
  }
  // If function is a single choice, add needed conversions
  private Prog convert( Type t ) {
    if( t._type!=Type.TFUN ) return this;
    // Insert conversions as-needed
    Type[] fargs = ((TypeFun)t)._ts._ts;
    for( int i=0; i<_args.length; i++ )
      if( !_args[i]._t.isBitShape(fargs[i]) ) {
        TypeFun cvt = Prim.convert(_args[i]._t,fargs[i]);
        if( cvt.is_lossy() ) throw new IllegalArgumentException("Requires lossy conversion");
        _args[i] = new ProgApply(new ProgCon(cvt),_args[i]);
      }
    return new ProgApply(new ProgCon(t),_args); // Pre-pass remove worked, simpler situation
  }
  @Override public String toString() { return _fun.toString()+"("+Arrays.toString(_args)+")"; }
}
