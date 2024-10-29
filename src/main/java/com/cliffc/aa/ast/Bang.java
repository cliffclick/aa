package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.*;
import com.cliffc.aa.type.TypeFld.Access;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;

import java.util.Arrays;

import static com.cliffc.aa.AA.TODO;

// Side-effect
public class Bang extends AST {
  private final String _name;
  public Bang(String var, AST def, AST body) { super(def,body);  _name = var; }
  public AST def () { return _kids.at(0); }
  public AST body() { return _kids.at(1); }

  // name := def; ....
  @Override public SB str(SB sb) {
    sb.p(_name).p(":=");
    def().str(sb).p(";");
    return body()==null ? sb : body().str(sb.nl().i());
  }
  @Override public void nodes( Env e ) {
    def().nodes(e);     // Go ahead and get the one kid def
    Node val = e._scope.rez();
    // Load the ident from the correct scope, issuing a linked list of display
    // loads along the way.
    Env e2 = e;
    Node ptr = e2._scope.ptr();
    while( e2._scope.stk().find(_name) == -1 ) {
        // Need to walk the display ptr chain
      ptr = new LoadNode(e._scope.mem(),ptr,"^",null).peep();
      e2 = e2._par;
    }

    Node st = new StoreNode(e._scope.mem(),ptr,val,_name,Access.RW,null).peep();
    e._scope.mem(st);
    if( body() != null )
      body().nodes(e);
  }

}
