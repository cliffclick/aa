package com.cliffc.aa.ast;

import com.cliffc.aa.ASTParse;
import com.cliffc.aa.Env;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.node.StructNode;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFld.Access;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;

import static com.cliffc.aa.AA.TODO;

public class LetRec extends AST {
  final Ary<String> _defs;

  public LetRec(Ary<String> defs, AST def) {
    super(def);
    _defs = defs;
  }
  public LetRec(AST body) {
    super(null,body);
    _defs = null;
  }

  // name = name = def; ....
  @Override public SB str(SB sb) {
    if( _defs!=null ) {
      sb.i();
      for( String def : _defs )
        sb.p(def).p(" = ");
      _kids.at(0).str(sb);
      assert( sb.was_nl() );
      sb.unchar(2).p(";").nl();
    }
    if( _kids._len < 2 ) return sb;
    return body().str(sb);
  }

  public void addBody(AST body) {
    assert _kids._len==1;
    _kids.setX(1,body);
  }
  AST body() { return _kids.at(1); }

  @Override public void nodes( Env e ) {
    // Print the program as Nodes
    if( _defs != null ) {
      // Make nodes for the def
      _kids.at(0).nodes(e);
      Node def = e._scope.rez();
      // Assign def to all the names
      StructNode stk = e._scope.stk();
      for( String name : _defs )
        stk.add_fld(name,Access.Final,def,null);
    }
    body().nodes(e);
  }
}
