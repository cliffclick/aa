package com.cliffc.aa.node;

import com.cliffc.aa.AA;
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

public class DynLoadNode extends Node {

  // Where to report errors
  private final Parse _bad;

  // Set of resolved field names
  private final HashSet<String> _resolves;
  
  public DynLoadNode( Node mem, Node adr, Node dyn, Parse bad ) {
    super(null,mem,adr,dyn);
    _bad = bad;
    _resolves = new HashSet<>();
  }

  @Override public String label() { return "._"; }   // Self short name
  
  public Node mem() { return in(MEM_IDX); }
  public Node adr() { return in(DSP_IDX); }
  public Node dyn() { return in(ARG_IDX); }
  
  @Override public Type value() {
    Type tadr = adr()._val;
    Type tmem = mem()._val;

    if( !(tadr instanceof TypeNil ta) || (tadr instanceof TypeFunPtr) )
      return tadr.oob(); // Not an address
    if( !(tmem instanceof TypeMem tm) )
      return tmem.oob(); // Not a memory

    if( ta==TypeNil.NIL || ta==TypeNil.XNIL )
      ta = (TypeNil)ta.meet(PrimNode.PINT._val);
    if( !(ta instanceof TypeMemPtr tmp) )
      return TypeNil.SCALAR.oob(ta);

    // Set of fields being picked over
    TypeStruct ts = tmp.is_simple_ptr() ? tm.ld(ta) : tmp._obj;

    // Still resolving, dunno which field yet
    if( Combo.pre() ) {
      Type t = ts._def;
      for( TypeFld tf : ts ) {
        Type q = tf._t;
        if( tf._t instanceof TypeMemPtr tmp2 && tmp2.is_simple_ptr() )
          q = tmp2.make_from(tm.ld(tmp2));
        t = t.meet(q);
      }
      return t;
    }

    // Meet over all possible choices.  This DynLoad might have resolved
    // differently with different TV3s from different paths, so meet over all
    // possible choices.
    Type t = TypeNil.XSCALAR;
    if( dyn().tvar() instanceof TVDynTable dyn )
      for( String label : dyn.fields(_resolves,this,Combo.HM_AMBI) )
        t = t.meet(LoadNode.lookup(ts,tm,label));
    return t;
  }

  
  // The only memory required here is what is needed to support the Load.
  // If the Load is alive, so is the address.
  @Override public Type live_use( int i ) {
    //assert _live==Type.ALL;
    Type adr = adr()._val;
    // Since the Load is alive, the address is alive
    if( i!=MEM_IDX ) return Type.ALL;
    // Memory demands
    Node def = mem();
    // If adr() value changes, the def liveness changes; this is true even if
    // def is ALSO adr().def() which the normal deps_add asserts prevent.
    adr().deps_add_live(def);
    if( adr.above_center() ) return Type.ANY; // Nothing is demanded

    // Demand everything not killed at this field.
    if( !(adr instanceof TypeNil ptr) || // Not a ptr, assume it becomes one
        ptr._aliases==BitsAlias.NALL )   // All aliases, then all mem needed
      return RootNode.removeKills(def);  // All mem minus KILLS
  
    if( ptr._aliases.is_empty() )  return Type.ANY; // Nothing is demanded still

    // TODO: not quite monotonic, if def is high and falls to mem
    TypeStruct obj = def._val instanceof TypeMem mem
      // Named fields are live
      ? mem.ld(ptr).flatten_live_fields()
      // All fields are live
      : TypeStruct.ISUSED;
    return TypeMem.make(ptr._aliases,obj);
  }

  @Override public Node ideal_reduce() {
    if( _resolves.size()==1 ) {
      String label = _resolves.iterator().next();
      //return new LoadNode(mem(),adr(),label,_bad).peep().setLive(_live);
      throw AA.TODO("UNTESTED");
    }
    return null;
  }

  // No matches to pattern (no YESes, no MAYBEs).  Empty patterns might have no NOs.
  public boolean resolve_failed_no_match( TV3 pattern, TVStruct rhs, boolean test ) {
    throw TODO();
  }
  
  @Override public boolean has_tvar() { return true; }
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
    dyn = (TVDynTable)dyn.find();

    // Load self into the table
    dyn.add_dyn(this,ptr,_tvar);
    return _tvar;
  }

  @Override public boolean unify( boolean test ) {
    return dyn().tvar() instanceof TVDynTable tab && tab.resolve(this,test);
  }  
}
