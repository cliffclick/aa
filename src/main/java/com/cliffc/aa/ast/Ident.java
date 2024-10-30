package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.FreshNode;
import com.cliffc.aa.node.LoadNode;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.util.SB;


public class Ident extends AST {
  final String _name;
  public Ident( String name ) { _name = name; }
  @Override public SB str(SB sb) { return sb.p(_name); }
  @Override public int mutLetRec() {
    int idx;
    // Find a defining LetRec, or null for lambdas and primitives.
    for( AST par = _par; par != null; par = par._par )
      if( par instanceof ASTVars vars && !(vars instanceof Struct) && (idx = vars.find(_name)) != -1 )
        // Edge in the LetRec graph from stack-top to idx
        return vars.addEdge(idx);
    // No defining LetRec, must be a primitive
    return 0;
  }

  @Override public void nodes( Env e ) {

    // Load the ident from the correct scope, issuing a linked list of display
    // loads along the way.
    Env e2 = e;
    Node ptr = e2._scope.ptr();
    while( e2._scope.stk().find(_name) == -1 ) {
        // Need to walk the display ptr chain
      ptr = new LoadNode(e._scope.mem(),ptr,"^",null).peep();
      e2 = e2._par;
    }

    Node ld = new LoadNode(e._scope.mem(),ptr,_name,null).peep();

    // Fresh check: if not needed, skip collecting the nongen and making a fresh
    if( isLetPolymorphic() ) {
      // Fresh: this variable is let-polymorphic, and needs a non-gen set.
      FreshNode frsh = new FreshNode(ld).init();
      // Walk to the Root and collect the non-gen edges
      for( AST par = _par; par != null; par = par._par )
        if( par instanceof ASTVars vars && !(vars instanceof Struct) )
          vars.addNonGen(frsh);
      ld = frsh;
    }

    e._scope.rez(ld);
  }

  private boolean isLetPolymorphic() {
    for( AST par = _par, old=this; par != null; old = par, par = par._par )
      // Find the ident def
      if( par instanceof ASTVars vars && vars.find(_name)!= -1 )
        // If the ident comes from the body side, needs a Fresh, otherwise no.
        return vars instanceof LetRec let && let.body() == old;
    // Not found; happens for named primitives, e.g. math.rand
    return false;
  }

}
