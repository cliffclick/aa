package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.ForwardRefNode;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.node.StructNode;
import com.cliffc.aa.type.TypeFld.Access;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;

import static com.cliffc.aa.AA.TODO;


public class LetRec extends AST {
  final Ary<String> _vars;

  public LetRec(String var, AST def, AST body) {
    super(def,body);
    _vars = new Ary<>(new String[]{var});
    if( body() instanceof LetRec let ) {
      _kids.pop();
      _vars.addAll(let._vars);
      _kids.addAll(let._kids);
      assert !(body() instanceof LetRec); // Only 1 round of rollups needed?
    }

  }
  AST body() { return _kids.last(); }


  // name = name = def; ....
  @Override public SB str(SB sb) {
    for( int i=0; i<_vars._len; i++ ) {
      sb.p(_vars.at(i)).p(" = ");
      _kids.at(i).str(sb);
      sb.p(";").nl().i();
    }
    return body()==null ? sb : body().str(sb);
  }


  @Override public void mutLetRec() {
    if( _vars._len==1 ) return;
    //Here



    throw TODO();
  }


  @Override public void nodes( Env e ) {
    // Print the program as Nodes
    if( _vars._len>1 )
      throw TODO();

    // TODO: Cannot do this here, need to allow Ident to jam in FRef, plus promote
    // TODO: Or a pre-pass over AST, finds all frefs & pre-sets them
    // along with MUTUAL LetRec cycles.
    // TODO: Node conversion should be dumb now
    StructNode stk = e._scope.stk();
    String var = _vars.at(0);
    ForwardRefNode fref = new ForwardRefNode(var,null).init();
    fref.scope();
    stk.add_fld(var,Access.Final,fref,null);
    // Make nodes for the def
    _kids.at(0).nodes(e);
    Node def = e._scope.rez();
    // Assign def to name
    stk.set_fld(var,Access.Final,def,true);
    if( !fref.isDead() ) {
      fref.self();
      fref.close();
      fref.subsume(def);
    }

    body().nodes(e);
  }
}
