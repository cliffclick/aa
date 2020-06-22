package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFunPtr;
import com.cliffc.aa.type.TypeMem;

import java.util.Arrays;

public class UnresolvedNode extends Node {
  private Parse _bad;
  UnresolvedNode( Parse bad, Node... funs ) { super(OP_UNR,funs); _bad = bad; }
  @Override String xstr() {
    if( is_dead() ) return "DEAD";
    if( in(0) instanceof FunPtrNode ) {
      FunPtrNode fptr = (FunPtrNode)in(0);
      FunNode fun = fptr.fun();
      return "Unr:"+(fun==null ? "null" : fun.xstr());
    }
    return "Unr???";
  }
  @Override public Node ideal(GVNGCM gvn, int level) {
    if( _defs._len < 2 )               // One function, consumer should treat as a copy
      throw com.cliffc.aa.AA.unimpl(); // Should collapse
    // Back-to-back Unresolved collapse (happens due to inlining)
    boolean progress=false;
    for( int i=0; i<_defs._len; i++ ) {
      if( in(i) instanceof UnresolvedNode ) {
        progress = true;
        Node u = in(i);
        for( int j=0; j<u._defs._len; j++ )
          add_def(u.in(j));
        set_def(i,pop(),gvn);
      }
    }
    return progress ? this : null;
  }

  @Override public Type value(GVNGCM gvn) {
    // Freeze after GVN - only still around for errors
    if( gvn._opt_mode > 2 ) return gvn.self_type(this);
    // If any arg is ALL - that wins; if ANY - ignored.
    // If any arg is not a TFP, then OOB.
    // If any arg is high, ignore - FunPtrs always fall.
    // If opt_mode==2, then high else low
    boolean lifting = gvn._opt_mode!=2;
    Type initial = lifting ? Type.ANY : Type.ALL;
    Type t = initial;
    for( Node def : _defs ) {
      Type td = gvn.type(def);
      if( td==Type.ANY )        // Some arg is at high?
        if( lifting ) continue; // Lifting: ignore it
        else return Type.ANY;   // Falling: wait till it falls.
      if( td==Type.ALL ) return Type.ALL;
      if( !(td instanceof TypeFunPtr) ) return td.oob();
      TypeFunPtr tfp = (TypeFunPtr)td;
      if( tfp.above_center() ) tfp = tfp.dual();
      if( tfp._disp.above_center() ) throw com.cliffc.aa.AA.unimpl(); // mixed-mode
      t = lifting ? t.meet(tfp) : t.join(tfp.dual());
    }
    return t==initial ? Type.ANY : t; // If all inputs are ANY, then ANY result
  }

  // Filter out all the wrong-arg-count functions
  public Node filter( GVNGCM gvn, int nargs ) {
    Node x = null;
    for( Node epi : _defs ) {
      FunNode fun =  ((FunPtrNode)epi).fun();
      // User-nargs are user-visible #arguments.
      // Fun-nargs include the display, hence the +1.
      if( fun.nargs() != nargs+1 ) continue;
      if( x == null ) x = epi;
      else if( x instanceof UnresolvedNode ) x.add_def(epi);
      else x = new UnresolvedNode(_bad,x,epi);
    }
    return x instanceof UnresolvedNode ? gvn.xform(x) : x;
  }

  @Override public boolean basic_liveness() { return false; }
  // Compute local contribution of use liveness to this def.
  // If pre-GCP, same as value() above, use the conservative answer.
  // During GCP, this will resolve so use the optimistic answer.
  @Override public TypeMem live_use( GVNGCM gvn, Node def ) {
    if( gvn._opt_mode < 2 ) return super.live_use(gvn,def);
    if( !(def instanceof FunPtrNode) ) return _live;
    // If any Call has resolved to this def, its alive.
    // If not a Call, must assume it props to some unknown Call and is alive.
    int dfidx = ((FunPtrNode)def).ret()._fidx;
    for( Node call : _uses )
      if( !(call instanceof CallNode) ||
          ((CallNode)call).live_use_call(gvn,dfidx) != TypeMem.DEAD )
        return _live;
    // Only call users, and no call wants this def.
    return TypeMem.DEAD;
  }

  // Return the op_prec of the returned value.  Not sensible except when called
  // on primitives.  Should be the same across all defs.
  @Override public byte op_prec() {
    byte prec = _defs.at(0).op_prec();
    assert _defs._len < 2 || _defs.at(1).op_prec() == prec;
    return prec;
  }
  // Return the op_prec of the returned value.  Not sensible except when called
  // on primitives.  Should be the same across all defs.
  @Override public byte may_prec() {
    byte prec = -1;
    for( Node f : _defs ) if( (prec=f.op_prec()) >= 0 ) return prec;
    return prec;
  }
  @Override public int hashCode() { return super.hashCode()+(_bad==null ? 0 : _bad.hashCode()); }
  @Override public boolean equals(Object o) {
    if( !super.equals(o) ) return false;
    return _bad==((UnresolvedNode)o)._bad;
  }
  // Make a copy with an error message
  public UnresolvedNode copy(Parse bad) {
    return new UnresolvedNode(bad,Arrays.copyOf(_defs._es,_defs._len));
  }
  // Do not walk into the unresolved calls; there is only an error if a Call uses an Unresolved.
  @Override boolean is_uncalled(GVNGCM gvn) { return true; }
  // Choice of typically primitives, all of which are pure.
  // Instead of returning the pre-call memory on true, returns self.
  @Override Node is_pure_call() {
    for( Node fun : _defs )
      if( fun.is_pure_call() == null )
        return null;
    return this;                // Yes, all choices are pure
  }
}
