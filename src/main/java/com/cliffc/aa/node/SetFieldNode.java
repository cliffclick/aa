package com.cliffc.aa.node;

import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV2;
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
  }
  @Override public String xstr() { return "."+_fld+"="; } // Self short name
  String  str() { return xstr(); }   // Inline short name
  public TypeFld find(TypeStruct ts) { return ts.get(_fld); }

  @Override public Type value() {
    Type t = val(0);
    if( !(t instanceof TypeStruct ts) ) return t.oob();
    return ts.update(_fin,_fld,val(1));
  }

  @Override public boolean has_tvar() { return true; }

  // Unify the named field against a TV2.is_obj same named field.
  // Other fields are just passed through.
  @Override public boolean unify( boolean test ) {
    TV2 self = tvar();
    TV2 rec = tvar(0);
    TV2 tvf = tvar(1);

    // Unify all other fields common to both
    boolean progress = false;
    if( self.is_obj() && rec.is_obj() )
      for( String fld : self._args.keySet() )
        if( !Util.eq(fld,_fld) ) { // All fields except the replaced one
          TV2 rfld = rec.arg(fld);
          progress |= rfld!=null && self.arg(fld).unify(rfld,test);
          if( test && progress ) return true;
        }

    // Lookup field in self
    TV2 fld = self.arg(_fld);
    if( fld!=null )
      return fld.unify(tvf,test) | progress;

    // Add struct-ness if possible
    if( !self.is_obj() && !self.is_nil() ) {
      if( test ) return true;
      self.make_struct_from();
    }

    // Add the field
    if( self.is_obj() && self.is_open() ) {
      if( !test ) self.add_fld(_fld,tvf);
      return true;
    }

    // Closed/non-record, field is missing
    return self.set_err(("Missing field "+_fld).intern(),test);
  }

  @Override public ErrMsg err( boolean fast ) {
    if( !(val(0) instanceof TypeStruct ts) )
      return val(0).above_center() ? null : bad("Unknown",fast,null);
    TypeFld fld = ts.get(_fld);
    if( fld==null ) return bad("No such",fast,ts);
    Access access = fld._access;
    if( access!=Access.RW )
      return bad("Cannot re-assign "+access,fast,ts);
    return null;
  }
  private ErrMsg bad( String msg, boolean fast, TypeStruct to ) {
    if( fast ) return ErrMsg.FAST;
    // TODO: Detect closures
    return ErrMsg.field(_badf,msg,_fld,false,to);
  }

  @Override public Node ideal_reduce() {
    Node in0 = in(0);
    // SetField directly against a Struct; just use the Struct.
    if( in0 instanceof StructNode st ) {
      int idx = st.find(_fld);
      if( in(1) == st.in(idx) ) return st; // Storing same over same, no change

      // TODO: When profitable to replicate a StructNode ?
    }
    
    //// Find the field being updated
    //StructNode rec = nnn.rec();
    //TypeFld tfld = rec.get(_fld);
    //if( tfld== null ) return false;
    //// Folding unambiguous functions?
    //if( rez() instanceof FunPtrNode || rez() instanceof UnresolvedNode ) {
    //  if( rez().is_forward_ref() ) return false;
    //  nnn.add_fun(_fld, _fin, (FunPtrNode) rez(), _bad); // Stacked FunPtrs into an Unresolved
    //  // Field is modifiable; update New directly.
    //} else if( tfld._access==Access.RW )
    //  //nnn.set_fld(tfld.make_from(tfld._t,_fin),rez()); // Update the value, and perhaps the final field
    //  throw unimpl();
    //else  return false;      // Cannot fold
    //nnn.xval();
    //Env.GVN.add_flow_uses(this);
    //add_reduce_extra();     // Folding in allows store followers to fold in
    //return true;            // Folded.
    return null;
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
