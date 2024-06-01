package com.cliffc.aa.node;

import com.cliffc.aa.Combo;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;

import java.util.HashSet;

import static com.cliffc.aa.AA.*;

// Does a normal load, except the field label is inferred.
//
// Requires a "TVDynTable" typed input, which has the dynamic field name,
// based on the lexical path used to reach here.
//
// DynTables are passed in to every call, and loaded Fresh from the environment
// like a normal variable; they get an original definition next to Root.  Since
// they get loaded Fresh, they can have different types, hence different fields
// at every call site.
//
// Most of the exciting inference now is handed off to TVDynTable, and the
// setup of passing "$dyn" arguments around.

public class DynLoadNode extends LoadNode {

  // Set of resolved field names
  public final HashSet<String> _resolves;

  public DynLoadNode( Node mem, Node adr, Node dyn, Parse bad ) {
    super(mem,adr,"_",true,bad);
    addDef(dyn);
    _resolves = new HashSet<>();
  }

  @Override public String label() { return "._"; }   // Self short name

  public Node dyn() { return in(ARG_IDX); }

  @Override Type lookup( TypeStruct ts, TypeMem mem ) {
    // Still resolving, dunno which field yet
    if( Combo.pre() ) {
      Type t = ts._def;
      for( TypeFld tf : ts )
        t = t.meet( lookup(ts,mem,tf._fld) );
      return t;
    }

    // Meet over all possible choices.  This DynLoad might have resolved
    // differently with different TV3s from different paths, so meet over all
    // possible choices.
    Type t = TypeNil.XSCALAR;
    if( dyn().tvar() instanceof TVDynTable dyn )
      for( String label : dyn.fields(_resolves,this,Combo.HM_AMBI) )
        t = t.meet(lookup(ts,mem,label));
    return t;
  }


  // The only memory required here is what is needed to support the Load.
  // If the Load is alive, so is the address.
  @Override public Type _live_use( TypeNil ptr, TypeMem mem ) {

    // TODO: not quite monotonic, if def is high and falls to mem
    TypeStruct obj =
      // Named fields are live
      mem.ld(ptr).flatten_live_fields();
    return TypeMem.make(ptr._aliases,obj);
  }

  @Override public Node ideal_reduce() {
    if( _resolves.size()==1 ) {
      String label = _resolves.iterator().next();
      LoadNode load = new LoadNode(mem(),adr(),label,_fresh,_bad);
      load._live = _live;
      load._val = _val;
      return load;
    }
    return null;
  }

  @Override public TV3 _set_tvar() {
    _tvar = new TVLeaf();
    // Load takes a pointer
    TV3 ptr0 = adr().set_tvar();
    TVPtr ptr;
    if( ptr0 instanceof TVPtr ptr1 ) ptr = ptr1;
    else ptr0.unify(ptr = new TVPtr(BitsAlias.EMPTY, new TVStruct(true) ),false);

    // Also prep the DynTable
    TV3 _dyn = dyn().set_tvar();
    TVDynTable dyn = new TVDynTable();
    _dyn.unify(dyn,false);
    dyn = dyn.find();

    // Load self into the table
    dyn.add_dyn(this,ptr,_tvar);
    return _tvar;
  }

  @Override public boolean unify( boolean test ) {
    return dyn().tvar() instanceof TVDynTable tab && tab.resolve(this,test);
  }
}
