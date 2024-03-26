package com.cliffc.aa.ast;

import com.cliffc.aa.util.Ary;
import com.cliffc.aa.Env;
import com.cliffc.aa.util.SB;

public abstract class AST {
  // AST is a Abstract Syntax *TREE*
  public final Ary<AST> _kids;
  AST _par;                     // Parent

  AST(Ary<AST> kids) { _kids = kids; }
  AST(AST... kids) { this(new Ary(kids)); }

  // Default toString
  public final String toString() {  return str(new SB()).toString();  }

  // Everybody has to have a pretty print
  abstract public SB str(SB sb);

  // A default print: class name, nl, increase indent, all kids
  public final SB _str(SB sb) {
    sb.p(getClass().getSimpleName()).nl().ii(1);
    for( AST kid : _kids )
      if( kid!=null )
        kid.str(sb);
    return sb.di(1);
  }

  // Restrucure the AST to group mutual-let-recs, and allow Idents to
  // understand the non-gen set when making Fresh types.
  public int mutLetRec() {
    for( AST kid : _kids )
      if( kid != null ) {
        kid._par = this;        // Set parents
        kid.mutLetRec();
      }
    return 0;
  }


  // "print" your self AST into the Env
  abstract public void nodes( Env e );
}
