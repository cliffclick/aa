package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;

import static com.cliffc.aa.AA.unimpl;

// ValNodes behave like FunPtrNodes in some contexts (can be called; acts like
// a constructor), and like a Memory in other contexts (can be loaded through
// like a pointer).  Marker interface to help keep uses correct.
public abstract class ValFunNode extends Node {
  ValFunNode(byte op, Node... defs) { super(op,defs); }
  abstract int nargs();
  abstract int fidx();
  abstract String name();       // Debug name, might be empty string
  // The formals.  Comes from FunPtr->Fun->Parms._t or from ValNode->proto->_ts[idx]
  abstract Type formal(int idx);
  // The actual value, as a TypeFunPtr (or OOB).
  // For ValNodes, it is the constructor signature.
  //abstract TypeFunPtr funtype();

  // Value types also appear in TypeFunPtr contexts and in TypeMemPtr otherwise.
  public static String valtype( Type t ) {
    if( !(t instanceof TypeMemPtr tmp) ) return null;
    String tname = tmp._obj._name;
    return tname.length() > 0 ? tname : null;
  }

  // Value types also appear in TypeFunPtr contexts and in TypeMemPtr otherwise.
  public static TypeFunPtr as_tfp( Type t ) {
    if( t instanceof TypeFunPtr ) return (TypeFunPtr)t;
    String tname = valtype(t);
    if( tname==null) return (TypeFunPtr)t.oob(TypeFunPtr.GENERIC_FUNPTR);
    // Convert value type to the constructor function
    NewNode nnn = Env.PROTOS.get(tname);
    assert ((TypeMemPtr)t)._aliases.getbit()==nnn._alias;
    assert nnn._nargs>0;
    for( Node use : nnn._uses )
      if( use instanceof ValNode )
        return TypeFunPtr.make(((ValNode)use)._fidx,nnn._nargs,TypeMemPtr.NO_DISP,t);
    throw unimpl();             // Do not understand the situation
  }

  // Find ValFunNode by fidx
  private static int FLEN;      // Primitives length; reset amount
  static Ary<ValFunNode> FUNS = new Ary<>(new ValFunNode[]{null,});
  public static void init0() { FLEN = FUNS.len(); }
  public static void reset_to_init0() { FUNS.set_len(FLEN); }

  // Null if not a FunPtr to a Fun.  Dead or ValNode returns null.
  public static ValFunNode get( int fidx ) {
    ValFunNode vfn = FUNS.atX(fidx);
    if( vfn==null || vfn.is_dead() ) return null;
    if( vfn.fidx()==fidx ) return vfn;
    // Split & renumbered FunNode, fixup in FUNS.
    throw unimpl();
  }
  // First match from fidxs
  public static ValFunNode get( BitsFun fidxs ) {
    for( int fidx : fidxs ) {
      ValFunNode vfn = get(fidx);
      if( vfn!=null ) return vfn;
    }
    return null;
  }

  public static FunPtrNode get_fptr( int fidx ) {
    ValFunNode vfn = get(fidx);
    return vfn instanceof FunPtrNode ? ((FunPtrNode)vfn) : null;
  }
}
