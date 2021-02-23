package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.util.*;

import java.util.HashMap;
import java.util.HashSet;

// Type Variable.  TVars unify (ala Tarjan Union-Find), and can have structure
// (such as "{ A -> B }").  TVars are tied to a TNode to enforce Type structure
// on Types.  TVars with no structure either refer to a plain Node, or get
// unioned into another TVar.  TVars with structure have to match structure to
// be unified, but then can be recursively unified.

public class TV2 {
  // Unique ID
  static private int UID=1;
  public final int _uid;
  // - Structural tag for the H-M "type", Args, Ret, Fun, Mem, Obj, Base (some
  // constant Type).  These typically have to be equal during unification (Base
  // Types MEET).
  // - Can also be "Fresh", which is a one-off indirection to another TV2 which
  // needs to be fresh-unified instead of normal-unification of this TV2.  The
  // freshable TV2 is in _args under the key "Fresh".
  // - Can also be "Unified", which is a one-off indirection for Tarjan U-F.
  // The unified TV2 is in _args under the key "Unified".
  public String _name;
  // Set of structural H-M parts.  Indexed by dense integer for fixed-size (ala
  // Args,Ret,Fun), indexed by sparse integer alias for TMem, indexed by String
  // for Obj field names.  Can be null if empty.
  public HashMap<Object,TV2> _args;

  // Set of dependent CallEpiNodes, to be re-worklisted if the called function changes TV2.
  public HashSet<CallEpiNode> _deps;

  // Debug only.  Set of unioned Nodes.  null for empty.  Helpful to track where TV2s come from.
  public HashSet<Node> _ns;     //
  public String _alloc_site;    // Creation site; used to track excessive creation.

  // 
  TV2() { throw com.cliffc.aa.AA.unimpl(); }

  // Accessors
  public boolean is_unified() { return Util.eq(_name,"Unified"); }
  
  
  // Track allocation statistics
  static private class ACnts { int _malloc, _free; }
  static private HashMap<String,ACnts> ALLOCS = new HashMap<>; // Counts at alloc sites
  public String pcounts() {
    throw com.cliffc.aa.AA.unimpl();
  }
  
  @Override public final String toString() { return str(new SB(),new VBitSet(),true).toString();  }

  // Pretty print
  public final SB str(SB sb, VBitSet bs, boolean debug) {
    // Explicit U-F chain
    if( is_unified() ) {
      if( debug ) sb.p("V").p(_uid).p(">>");
      return get_unified().str(sb,bs,debug);
    }
    if( _uid != -1 && bs.tset(_uid) )
      return sb.p("V").p(_uid).p("$");
    // Print all unioned nodes
    if( _ns!=null && _ns.size() != 0 ) { // Have any
      for( TNode tn : _ns.iterator() ) // For all unioned
        if( !tn.is_dead() ) {   // Dead lazily cleared out, do not both  to print
          sb.p('N').p(tn.uid()).p(':');
          if( !debug ) break;   // Debug, see them all; non-debug just the first
        }
      sb.unchar();
    } else                      // No unioned nodes
      sb.p("V").p(_uid);        // So just the _uid
    // Structural contents
    if( _args != null ) {
      sb.p(":[ ");
      for( Object key : _args.keySet() )
        _args.get(key).str(sb.p(key.toString).p(':'),bs,debug).p(' ');
      sb.p("]");
    }
    return sb;
  }
}
