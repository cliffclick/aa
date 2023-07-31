package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TV3;
import com.cliffc.aa.tvar.TVPtr;
import com.cliffc.aa.tvar.TVStruct;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.unimpl;

// Store a whole struct into memory.
public class StoreXNode extends StoreAbs {
  public StoreXNode( Node mem, Node adr, StructNode val, Parse bad ) {
    super(mem,adr,val,bad);
  }

  StructNode struct() { return (StructNode)in(3); }

  @Override Type _value( TypeMem tm, TypeMemPtr tmp ) {
    TypeStruct tvs = rez()._val instanceof TypeStruct tvs0 ? tvs0 : rez()._val.oob(TypeStruct.ISUSED);
    return tm.update(tmp,tvs);
  }

  @Override TypeMem _live_use( TypeMem live0, TypeMemPtr tmp ) {
    if( tmp.above_center() ) {
      throw unimpl();
    } else {
      // Constant ptr, so precise update
      if( tmp.is_con() ) {
        TypeStruct ts = rez()._val instanceof TypeStruct ts0 ? ts0.flatten_live_fields() : rez()._val.oob(TypeStruct.ISUSED);
        return live0.update(tmp,ts);
      } else {
        // Imprecise update; everything remains live
        return live0;
      }
    }    
  }

  // Is this Store alive, based on given liveness?
  @Override boolean _is_live( TypeStruct live ) {  return live==TypeStruct.ISUSED; }

 
  @Override public TV3 _set_tvar() {
    assert rez()!= Env.ANY; // Did not clear out during iter; return mem().tvar()

    // Demands rez is a struct
    TV3 rez = rez().set_tvar();    TVStruct stz;
    if( rez instanceof TVStruct stz0 ) stz = stz0;
    else rez.unify(stz = new TVStruct(true),false);

    // Demands address is a ptr to above struct.
    TV3 adr = adr().set_tvar();    TVPtr ptr;
    if( adr instanceof TVPtr ptr0 ) (ptr=ptr0).load().unify(stz,false);
    else adr.unify(ptr=new TVPtr(BitsAlias.EMPTY,stz),false);
    assert ptr.aliases()!=BitsAlias.NALL;
    
    return null;
  }

  @Override public boolean unify( boolean test ) {
    TVPtr ptr = (TVPtr)adr().tvar();
    return unify(ptr.aliases(),rez().tvar(),test);
  }
}
