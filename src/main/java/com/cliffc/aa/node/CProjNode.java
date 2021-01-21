package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeMem;

// Proj control
public class CProjNode extends ProjNode {
  public CProjNode( Node ifn ) { this(ifn,AA.CTL_IDX); }
  public CProjNode( Node ifn, int idx ) { super(OP_CPROJ,ifn,idx); }
  @Override public String xstr() {
    if( !is_dead() && in(0) instanceof IfNode )
      return _idx==0 ? "False" : "True";
    return "CProj"+_idx;
  }
  @Override public Type value(GVNGCM.Mode opt_mode) {
    Type x = super.value(opt_mode);
    if( x==Type.ANY ) return Type.XCTRL;
    if( x==Type.ALL ) return Type. CTRL;
    return x;
  }
  @Override public void add_flow_use_extra(Node chg) {
    // Control from Calls
    if( chg instanceof CallNode ) {
      // if the Call changes val the function might be callable
      for( Node fun : _uses )
        if( fun instanceof FunNode )
          Env.GVN.add_flow(fun);
    }
  }

  @Override public TypeMem all_live() { return TypeMem.ALIVE; }
  @Override public TypeMem live_use(GVNGCM.Mode opt_mode, Node def ) { return def.all_live().basic_live() ? TypeMem.ALIVE : TypeMem.ANYMEM; }

  // Return the op_prec of the returned value.  Not sensible except
  // when call on primitives.
  @Override public byte op_prec() { return _defs.at(0).op_prec(); }

}
