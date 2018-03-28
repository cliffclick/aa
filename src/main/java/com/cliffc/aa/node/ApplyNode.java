package com.cliffc.aa.node;

import com.cliffc.aa.*;

public class ApplyNode extends Node {
  public ApplyNode( Node... defs ) { super(defs); }
  @Override String str() { return "apply"; }
  @Override public Node ideal(GVNGCP gvn) {

    // If the function is unresolved, see if we can resolve it now
    if( _defs.at(0) instanceof UnresolvedNode )
      return resolve(gvn,(UnresolvedNode)_defs.at(0));
    
    return null;
  }

  // Toss out choices where any args are not "isa" the call requirements.
  // TODO: this tosses out choices too eagerly: no need to force conversions so quickly
  private Node resolve( GVNGCP gvn, UnresolvedNode unr ) {
    Type[] funs = unr.types(gvn); // List of function types
    Type[] actuals = new Type[_defs._len-1];
    for( int i=1; i<_defs._len; i++ )  actuals[i-1] = gvn.type(_defs.at(i));
    TypeFun z=null;  int zcvts=999;  Node zn=null;
    // for each function, see if the actual args isa the formal args.  If not, toss it out.
    for( int i=0,j; i<funs.length; i++ ) {
      TypeFun fun = (TypeFun)funs[i];
      Type[] fargs = fun._ts._ts;
      if( fargs.length != actuals.length ) continue; // Argument count mismatch
      int cvts=0;
      for( j=0; j<actuals.length; j++ )
        if( !(actuals[j].isa(fargs[j])) ) break;
        else if( !actuals[j].isBitShape(fargs[j]) ) cvts++;
      if( j<actuals.length ) continue; // Some argument does not apply; drop this choice
      if( z==null || cvts < zcvts ) { z=fun; zcvts = cvts; zn = unr._defs.at(i); }
      else throw AA.unimpl(); // TODO: Stall on ambiguous as long as possible
    }
    if( z==null ) return null;

    // insert actual conversions
    for( int i=1; i<_defs._len; i++ ) {
      Type formal = z._ts._ts[i-1];
      Node actual = _defs.at(i);
      Type act = gvn.type(actual);
      if( !act.isBitShape(formal) ) {
        PrimNode cvt = PrimNode.convert(act,formal);
        if( cvt.is_lossy() ) throw new IllegalArgumentException("Requires lossy conversion");
        _defs.set(i,gvn.xform(new ApplyNode(gvn.xform(cvt),actual)));
      }
    }
    // upgrade function argument to a constant
    _defs.set(0,zn);
    return this;
  }

  @Override public Type value(GVNGCP gvn) {
    Node nfun = _defs.at(0);
    // Value is the function return type
    Type fun = gvn.type(nfun);
    Type ret = fun.ret();
    if( ret == null )           // Not-a-function application
      return Type.ANY;          // Yeah-Olde-Crash-N-Burn type
    
    // If all args are constant, eval immediately.  Note that the Memory edge
    // will define if a function is "pure" or not; no Memory means must be pure.
    Type[] ts = types(gvn);
    boolean con=true;
    for( int i=1; i<_defs._len; i++ ) if( !ts[i].is_con() ) { con=false; break; }
    if( con && nfun instanceof PrimNode )
      return ((PrimNode)nfun).apply(ts);
    
    return ret;
  }
}
