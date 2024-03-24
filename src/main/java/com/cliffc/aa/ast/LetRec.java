package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.ForwardRefNode;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.node.StructNode;
import com.cliffc.aa.type.TypeFld.Access;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;

public class LetRec extends AST {
  final String _var;

  public LetRec(String var, AST def) {
    super(def,null);
    _var = var;
  }
  public void addBody(AST body) {
    if( _kids.at(1)==null )
      _kids.set(1,body);
    else assert body==null;
  }
  AST body() { return _kids.at(1); }


  // name = name = def; ....
  @Override public SB str(SB sb) {
    if( _var!=null ) {
      sb.p(_var).p(" = ");
      _kids.at(0).str(sb);
      sb.p(";");
    }
    if( body()==null ) return sb;
    sb.nl().i();
    return body().str(sb);
  }

  void rollup( Ary<String> defs, Ary<AST> kids ) {
    assert _kids.at(0)!=null;
    defs.push(_var);
    kids.push(_kids.at(0));
    if( _kids.at(1) instanceof LetRec let )
      let.rollup(defs,kids);
  }

  @Override public void nodes( Env e ) {
    // Print the program as Nodes
    if( _var != null ) {
      // TODO: Cannot do this here, need to allow Ident to jam in FRef, plus promote
      // TODO: Or a pre-pass over AST, finds all frefs & pre-sets them
      // along with MUTUAL LetRec cycles.
      // TODO: Node conversion should be dumb now
      StructNode stk = e._scope.stk();
      ForwardRefNode fref = new ForwardRefNode(_var,null).init();
      fref.scope();
      stk.add_fld(_var,Access.Final,fref,null);
      // Make nodes for the def
      _kids.at(0).nodes(e);
      Node def = e._scope.rez();
      // Assign def to name
      stk.set_fld(_var,Access.Final,def,true);
      if( !fref.isDead() ) {
        fref.self();
        fref.close();
        fref.subsume(def);
      }
    }
    body().nodes(e);
  }
}
