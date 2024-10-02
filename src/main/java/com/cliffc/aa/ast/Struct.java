package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.*;
import com.cliffc.aa.type.TypeFld.Access;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;

public class Struct extends AST {
  final Ary<String> _vars;

  // Any LetRecs are folded up into a Struct
  public Struct(LetRec let) { this(let._kids,let._vars); }
  public Struct(Ary<AST> kids, Ary<String> vars) { super(kids); _vars = vars; }

  // @{ fld0=expr0; ... }
  @Override public SB str(SB sb) {
    sb.p("@{").nl().ii(1);
    for( int i=0; i<_vars._len; i++ )
      _kids.at(i).str(sb.ip(_vars.at(i)).p(" = ")).p(";").nl();
    return sb.di(1).ip("}");
  }

  @Override public void nodes( Env e ) {
    ScopeNode outScope = e._scope;
    try( Env eStruct = new Env(e,"STRUCT") ) {
      ScopeNode inScope = eStruct._scope;
      StructNode s = inScope.stk();
      // Struct is pre-allocated, fields filled with ANY, then the init code runs
      for( int i=0; i<_vars._len; i++ )
        s.add_fld(_vars.at(i),Access.RW,Env.ANY,null);
      s.close();
      // Initial write, to set the display at least
      inScope.mem( new StoreXNode( inScope.mem(),inScope.ptr(),s,null).init());

      // Now we make a bulk update again, but code within the fields can use
      // the struct display to find things in outer scopes.
      StructNode s2 = new StructNode(0,false,null,s._hint);
      s2.add_fld("^",Access.Final,outScope.ptr(),null);
      for( int i=0; i<_vars._len; i++ ) {
        _kids.at(i).nodes(eStruct);
        s2.add_fld(_vars.at(i),Access.Final,inScope.rez(),null);
      }
      s2.close();
      inScope.mem( new StoreXNode( inScope.mem(),inScope.ptr(),s2,null).init());

      //// See matching comment hack in Env.java
      // The init code runs, then all fields are filled in at once.
      //for( int i=0; i<_vars._len; i++ ) {
      //  _kids.at(i).nodes(eStruct);
      //  s.add_fld(_vars.at(i),Access.Final,inScope.rez(),null);
      //}
      //s.close();
      //inScope.mem( new StoreXNode(inScope.mem(),inScope.ptr(),s,null).init());

      outScope.ctrl(inScope.ctrl());
      outScope.mem (inScope.mem ());
      outScope.rez (inScope.ptr ());
    }
  }
}
