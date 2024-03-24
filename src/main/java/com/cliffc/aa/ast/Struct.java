package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.*;
import com.cliffc.aa.type.BitsAlias;
import com.cliffc.aa.type.TypeFld;
import com.cliffc.aa.type.TypeFld.Access;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;

public class Struct extends AST {
  final Ary<String> _names;

  public Struct(LetRec let) {
    _names = new Ary<>(String.class);
    // Any LetRecs are folded up into a Struct
    let.rollup(_names,_kids);
  }

  // @{ fld0=expr0; ... }
  @Override public SB str(SB sb) {
    sb.ip("@{").nl().ii(1);
    for( int i=0; i<_names._len; i++ )
      _kids.at(i).str(sb.ip(_names.at(i)).p(" = ")).p(";").nl();
    return sb.di(1).ip("}");
  }

  @Override public void nodes( Env e ) {
    ScopeNode scope = e._scope;
    StructNode s = new StructNode(0,false,null);
    s.add_fld(TypeFld.CLZ,Access.Final,PrimNode.PCLZ,null);
    for( int i=0; i<_names._len; i++ ) {
      _kids.at(i).nodes(e);
      s.add_fld(_names.at(i),Access.Final,scope.rez(),null);
    }
    NewNode ptr = new NewNode("STRUCT",BitsAlias.new_alias(),false).init();
    scope.rez(ptr);
    scope.mem(new StoreXNode(scope.mem(),ptr,s,null).init());
  }
}
