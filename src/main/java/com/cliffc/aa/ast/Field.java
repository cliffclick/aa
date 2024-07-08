package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.LoadNode;
import com.cliffc.aa.node.Node;
import com.cliffc.aa.util.SB;

public class Field extends AST {
  final String _name;

  public Field(String name, AST ptr) {
    super(ptr);
    _name = name;
  }

  // .fld
  @Override public SB str(SB sb) {
    AST ptr = _kids.at(0);
    if( ptr==null ) sb.p("self");
    else ptr.str(sb);
    return sb.p(".").p(_name);
  }
  @Override public void nodes( Env e ) {
    // "this" field reference in a struct
    Node ptr;
    if( _kids.at(0)==null ) {
      // Load the ident from the correct scope, issuing a linked list of display
      // loads along the way.
      Env e2 = e;
      ptr = e2._scope.ptr();
      while( e2._scope.stk().find(_name) == -1 ) {
        ptr = new LoadNode(e._scope.mem(),ptr,"^",null).peep();
        e2 = e2._par;
      }
      assert !e2._scope.stk().is_closure(); // Field not a closure
    } else {
      _kids.at(0).nodes(e);
      ptr = e._scope.rez();
    }
    Node mem = e._scope.mem();
    e._scope.rez(new LoadNode(mem,ptr,_name,null).peep());
  }
}
