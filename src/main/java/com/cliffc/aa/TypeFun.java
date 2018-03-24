package com.cliffc.aa;

import com.cliffc.aa.util.SB;

public class TypeFun extends Type {
  String _name;                 // Unique identifier (i.e., ptr to the actual code bits)
  String[] _args;               // Helpful arg names
  TypeTuple _ts;                // Arg types
  Type _ret;                    // return types
  protected TypeFun( String name, String[] args, TypeTuple ts, Type ret ) { super(TFUN); init(name,args,ts,ret); }
  private void init(String name, String[] args, TypeTuple ts, Type ret) {  _name = name; _args = args; _ts = ts; _ret = ret; }
  @Override public int hashCode( ) { return TFUN + _ts.hashCode() + _ret.hashCode() + _name.hashCode();  }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFun) ) return false;
    TypeFun tf = (TypeFun)o;
    return _ts==tf._ts && _ret==tf._ret && _name.equals(tf._name);
  }
  @Override public String toString() {
    SB sb = new SB().p(_name).p("::(");
    if( _args == null ) sb.p(_ts.toString());
    else {
      assert _args.length==_ts._ts.length;
      for( int i=0; i<_args.length; i++ )
        sb.p(i==0?"":",").p(_args[i]).p("::").p(_ts._ts[i].toString());
    }
    return sb.p("->").p(_ret).p(")").toString();
  }
  private static TypeFun FREE=null;
  private TypeFun free( TypeFun f ) { FREE=f; return this; }
  static TypeFun make( String name, String[] args, TypeTuple ts, Type ret ) {
    TypeFun t1 = FREE;
    if( t1 == null ) t1 = new TypeFun(name,args,ts,ret);
    else { FREE = null; t1.init(name,args,ts,ret); }
    TypeFun t2 = (TypeFun)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }

  static TypeFun any( String name, int nargs ) {
    return make(name,null,nargs==1?TypeTuple.XSCALAR1:TypeTuple.XSCALAR2,Type.SCALAR);
  }

  static final TypeFun[] TYPES = new TypeFun[]{};
  
  // What is the dual of a function?  Like a constant '3.14' the name is
  // unchanging and totally determined by the lookup rules (for prims) or their
  // definition point.  Hence the name is a constant: it is its own dual.
  // Other args flip structurally.
  @Override protected TypeFun xdual() { return new TypeFun(_name,_args,(TypeTuple)_ts.dual(),_ret.dual()); }
  @Override protected Type xmeet( Type t ) {
    switch( t._type ) {
    case TTUPLE:           return ALL;
    case TFLT:  case TINT: return Type.SCALAR;
    case TFUN:             break;
    default: throw typerr(t);   // All else should not happen
    }
    TypeFun tf = (TypeFun)t;
    Type ret = _ret.join(tf._ret); // Notice JOIN, Functions are contrapositive
    // If name or arglength are not compatible, then a union instead
    if( _name.equals(tf._name) && 
        _ts._ts.length == tf._ts._ts.length ) {
      // If the args are totally isa, then return the exact match
      Type targs = _ts.meet(tf._ts);
      if( targs==   _ts && ret==   _ret ) return this;
      if( targs==tf._ts && ret==tf._ret ) return tf;
    }
    return Type.SCALAR;
  }
  
  // The Main Excitement for functions is that they can be applied
  Type apply( Type[] args ) { throw AA.unimpl(); } // Should not call this
  
  @Override protected Type ret() { return _ret; }
  @Override protected String funame() { return _name; }

  @Override int op_prec() { return 0; }
  @Override protected boolean canBeConst() { return true; }
  boolean is_lossy() { return true; } // A few conversions are not lossy
}
