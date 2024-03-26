package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.FreshNode;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.util.SB;

import static com.cliffc.aa.AA.TODO;


public class Ident extends AST {
  final String _name;
  public Ident( String name ) { _name = name; }
  @Override public SB str(SB sb) { return sb.p(_name); }
  @Override public int mutLetRec() {
    int idx;
    // Find a defining LetRec, or null for lambdas and primitives.
    for( AST par = _par; par != null; par = par._par )
      if( par instanceof ASTVars vars && (idx = vars._vars.find(_name)) != -1 )
        // Edge in the LetRec graph from stack-top to idx
        return vars.addEdge(idx);
    // No defining LetRec, must be a primitive
    return 0;
  }
  @Override public void nodes( Env e ) {
    Node x = e.lookup(_name);
    if( x==null ) throw TODO();

    // Find a defining LetRec, or null for lambdas and primitives.
    for( AST par = _par, old=null; par != null; old = par, par = par._par )
      if( par instanceof LetRec let && let._vars.find(_name) != -1 &&
          // If the ident comes from the body side, needs a Fresh
          let.body() == old )
        x = fresh(x,let);

    // No defining LetRec, must be a Lambda or primitive
    e._scope.rez(x);
  }

  private Node fresh( Node x, LetRec def ) {
    FreshNode frsh = new FreshNode(x).init();
    for( AST par = _par; par != def; par = par._par )
      if( par instanceof ASTVars vars )
        vars.addNonGen(frsh);
    return frsh;
  }

}
