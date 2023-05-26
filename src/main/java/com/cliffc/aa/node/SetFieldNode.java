package com.cliffc.aa.node;

import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVLeaf;
import com.cliffc.aa.tvar.TVStruct;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeFld;
import com.cliffc.aa.type.TypeStruct;
import com.cliffc.aa.util.Util;

import static com.cliffc.aa.type.TypeFld.Access;

// Takes a static field name, a TypeStruct, a field value and produces a new
// TypeStruct.  This is an incremental TypeStruct producer, and does not update
// any memory state; the result is a pure value.  Contrast this with StoreNode
// which takes and produces a new memory state; it also takes in a TypeStruct.
public class SetFieldNode extends Node {
  final Access _fin;
  final String _fld;
  final Parse _badf;            // Bad field

  public SetFieldNode(String fld, Access fin, Node struct, Node val, Parse badf) {
    super(OP_SETFLD,struct,val);
    _fin = fin;
    _fld = fld;
    _badf= badf;
    _live = TypeStruct.ISUSED;
  }
  @Override public String xstr() { return "."+_fld+"="; } // Self short name
  String  str() { return xstr(); }   // Inline short name
  public TypeFld find(TypeStruct ts) { return ts.get(_fld); }

  @Override public Type value() {
    Type t = val(0);
    if( !(t instanceof TypeStruct ts) ) return t.oob();
    return ts.update(_fin,_fld,val(1));
  }

  @Override public Type live_use( int i ) {
    // If this node is not alive, neither input is
    if( !(_live instanceof TypeStruct ts) ) return _live;
    Type fld_live = ts.at_def(_fld);
    // For this field, pass liveness thru directly
    if( i==1 ) return fld_live;
    // For memory, pass thru liveness of all fields except this one
    if( fld_live==Type.ANY ) return ts; // Already dead
    // Here liveness depends on incoming value (i.e., value turns around into
    // liveness).  If incoming field is Final, this SetField is in-error and
    // keeps alive the field to preserve the prior SetField.
    TypeFld fld = ts.get(_fld);
    if( fld==null && !ts.above_center()     ) return ts;
    if( fld!=null && fld._access!=Access.RW ) return ts;
    // SetField resolved the demand for this field, so remove from live-use
    return ts.replace_fld(TypeFld.make(_fld,Type.ANY));
  }
  @Override boolean assert_live(Type live) { return live instanceof TypeStruct; }

  @Override public Node ideal_reduce() {
    Node in0 = in(0);
    // SetField directly against a Struct; just use the Struct.
    if( in0 instanceof StructNode st ) {
      int idx = st.find(_fld);
      Access access = st._accesses.at(idx);
      if( in(1) == st.in(idx) && access == _fin )
        return st; // Storing same over same, no change

      if( access==Access.RW ) {
        if( st._uses.len()==1 ) {
          st.set_fld(_fld,_fin,in(1),false);
          st.xval();            // Since moved field sideways, force type
          st._live = _live;     // The field is now alive in st
          return st;
        } else {
          // Track when uses drop to 1
          for( Node use : st._uses ) use.deps_add(this);
        }
      } 
    }

    return null;
  }

  @Override public boolean has_tvar() { return true; }
  
  @Override public TV3 _set_tvar() {
    TV3 rec  = new TVStruct(new String[]{_fld},new TV3[]{new TVLeaf()    },true);
    TV3 self = new TVStruct(new String[]{_fld},new TV3[]{in(1).set_tvar()},true);
    in(0).set_tvar().unify(rec,false);
    return self;
  }

  // Already unified a self-struct with the set field.
  // Need to unify matching other fields, same as TVStruct unification,
  // minus the one set field.
  @Override public boolean unify( boolean test ) {
    TVStruct self = tvar( ).as_struct();
    TVStruct rec  = tvar(0).as_struct();
    // Unify all other common fields, same as normal struct unification
    // TODO: verify i need this both ways
    return 
      self.half_unify(rec ,_fld,test) |
      rec .half_unify(self,_fld,test);
  }

  @Override public ErrMsg err( boolean fast ) {
    if( !(val(0) instanceof TypeStruct ts) )
      return val(0).above_center() ? null : bad("Unknown",fast,null);
    TypeFld fld = ts.get(_fld);
    if( fld==null )
      return ts.above_center() ? null : bad("No such",fast,ts);
    Access access = fld._access;
    if( access!=Access.RW )
      return bad("Cannot re-assign "+access,fast,ts);
    if( in(1) instanceof ForwardRefNode fref )
      return fast ? ErrMsg.FAST : fref.err(fast);
    return null;
  }
  private ErrMsg bad( String msg, boolean fast, TypeStruct to ) {
    if( fast ) return ErrMsg.FAST;
    // TODO: Detect closures
    return ErrMsg.field(_badf,msg,_fld,false,to);
  }


  @Override public int hashCode() { return super.hashCode()+_fld.hashCode()+_fin.hashCode(); }
  // Stores are can be CSE/equal, and we might force a partial execution to
  // become a total execution (require a store on some path it didn't happen).
  // This can be undone later with splitting.
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !(o instanceof SetFieldNode set) || !super.equals(o) ) return false;
    return _fin==set._fin && Util.eq(_fld,set._fld);
  }

}
