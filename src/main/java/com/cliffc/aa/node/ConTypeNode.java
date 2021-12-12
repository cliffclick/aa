package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;
import com.cliffc.aa.util.VBitSet;

// Naming names is hard, and I dont like this name.

// Node computes a flow-type, generally a TypeMemPtr to a TypeStruct which is
// somehow recursive.  The type recursion can be direct or indirect (or not at
// all).  Other than the Env.START input all other inputs are other ConTypes.
// Once all ConTypes (all user type variables) are parsed, all ConTypes taken
// together can GCP to actual constants and be replaced with ConNodes.
public class ConTypeNode extends Node {
  public final String _tname;   // Type-def name
  public Type _t;               // Updated when closing a forward-ref cycle
  public ConTypeNode( String tname, Type t, ScopeNode scope ) {
    super(OP_CONTYPE,Env.START);
    _tname = tname;
    _t = t;
  }
  public int alias() { return ((TypeMemPtr)_t).getbit0(); }
  public BitsAlias aliases() { return ((TypeMemPtr)_t)._aliases; }

  // Define a forward-ref Type
  public void def_fref(TypeStruct tc, Env e) {
    assert tc._name.equals(_tname+":");
    // Close, and set an initial value
    _t = ((TypeMemPtr)_t).make_from(tc);

    // Inspect the struct for aliases matching other ConTypes.  Force those as inputs.
    // Updates to their types will force the value call to update as well.
    VBitSet visit = new VBitSet();
    tc.walk( tx -> {
        if( visit.tset(tx._uid) ) return false;
        if( !(tx instanceof TypeMemPtr) ) return true;
        int alias = ((TypeMemPtr)tx)._aliases.strip_nil().abit();
        if( alias == -1 ) return true;
        ConTypeNode ctn = e.lookup_type(alias);
        if( ctn==null ) return true; // Not a named type
        if( _defs.find(ctn)== -1 ) // One-time only
          add_def(ctn);            // Add the ConType per unique alias
        return false;
      });
    xval();                     // Sets value equal to _t
    xval();                     // Closes any self-recursive cycle, but will leave forward-ref types alone
  }

  @SuppressWarnings("unchecked")
  @Override public Type value() {
    // Simple (non-recursive) constants have no inputs and already have their named type
    if( _defs._len==1 ) return _t;
    assert _t instanceof TypeMemPtr;

    // Walk 't' recursively.  Instances of TypeMemPtr with aliases same as the
    // input ConTypeNodes, use their value instead of 't's value.  This might
    // make a recursive-type, unrolled once (if, through a cycle, we reference
    // ourselves).  Approximate the unrolled type.
    TypeMem mem = TypeMem.EMPTY;
    for( Node ctn : _defs )
      if( ctn instanceof ConTypeNode ) {
        TypeObj obj = ctn._val instanceof TypeMemPtr  ? ((TypeMemPtr)ctn._val)._obj : TypeObj.UNUSED;
        mem = mem.set(((ConTypeNode)ctn).alias(),obj);
      }
    VBitSet visit = new VBitSet();

    TypeMemPtr t1 = (TypeMemPtr)_t.make_from(_t,mem,visit);
    TypeStruct t2 = ((TypeStruct)(t1._obj)).approx(1,aliases());
    TypeMemPtr t3 = t1.make_from(t2);
    return t3;
  }
  @Override public int hashCode() { return super.hashCode()+ _tname.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !(o instanceof ConTypeNode) ) return false;
    ConTypeNode ct = (ConTypeNode)o;
    return Util.eq(_tname,ct._tname) && super.equals(ct);
  }
}
