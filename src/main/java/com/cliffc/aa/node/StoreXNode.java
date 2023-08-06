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

  @Override Type _live_use( TypeMem live0, TypeMemPtr tmp, int i ) {
    TypeMem live1;
    if( tmp.above_center() ) {
      throw unimpl();
    } else if( tmp.is_con() ) { // Constant ptr, so precise update
      TypeStruct ts = rez()._val instanceof TypeStruct ts0 ? ts0.flatten_live_fields() : rez()._val.oob(TypeStruct.ISUSED);
      live1 = live0.update(tmp,ts);
    } else {                    // Imprecise update; everything remains live
      live1 = live0;
    }
    // Asking for live-in, give it
    if( i==1 ) return live1;
    // Struct live passes through
    TypeStruct luse = live0.ld(tmp);
    if( i==3 ) return luse;
    assert i==2;                // Address live
    return luse.oob();          // Address is ANY/ALL
  }

  @Override TypeMem _live_kill(TypeMemPtr tmp) {
    throw unimpl();
  }

  // Is this Store alive, based on given liveness?
  @Override boolean _is_live( TypeStruct live ) {  return live==TypeStruct.ISUSED; }

 
  @Override public TV3 _set_tvar() {
    assert rez()!= Env.ANY; // Did not clear out during iter; return mem().tvar()

    // Address is a ptr to a struct
    TV3 adr = adr().set_tvar();
    TVPtr ptr = adr instanceof TVPtr ptr0 ? ptr0 : new TVPtr(BitsAlias.EMPTY, new TVStruct(true));
    adr.unify(ptr,false);

    // Result must be the struct
    TVStruct stz = ptr.load();
    rez().set_tvar().unify(stz,false);    
    
    return null;
  }

  @Override public boolean unify( boolean test ) {
    TVPtr   ptr = (TVPtr   )adr().tvar();
    TVStruct ts = (TVStruct)rez().tvar();
    return unify(ptr.aliases(),ts,test);
  }
  public static final boolean unify( BitsAlias aliases, TVStruct ts, boolean test ) {
    assert aliases!=BitsAlias.NALL;
    boolean progress = false;
    for( int alias : aliases ) {
      // Each alias unifies into the global field state
      TVPtr nptr = (TVPtr)(NewNode.get(alias)).tvar();
      progress |= nptr.load().unify(ts,test);
      if( test && progress ) return true;
    }
    return progress;
  }

}
