package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.*;

// Load a struct from memory.  Does it's own nil-check testing.
public class LoadNode extends Node {
  private final Parse _bad;

  public LoadNode( Node mem, Node adr, Parse bad ) {
    super(OP_LOAD,null,mem,adr);
    _bad = bad;
    _live=TypeStruct.ISUSED;
  }
  Node mem() { return in(MEM_IDX); }
  Node adr() { return in(DSP_IDX); }
  private Node set_mem(Node a) { return set_def(MEM_IDX,a); }
  //public TypeFld find(TypeStruct ts) { return ts.get(_fld); }

  @Override public Type value() {
    Type tadr = adr()._val;
    Type tmem = mem()._val;       // Memory
    return switch(tadr ) {
    case TypeMemPtr tmp ->    // Loading from a pointer
      tmem instanceof TypeMem tm ? tm.ld(tmp) : tmem.oob();
    case TypeNil tn -> tn;      // Load from prototype/primitive is a no-op
    default -> tadr.oob();      // Nothing sane
    };
  }

  // The only memory required here is what is needed to support the Load.
  // If the Load is alive, so is the address.

  // If the Load computes a constant, the address live-ness is determined how
  // Combo deals with constants, and not here.
  @Override public Type live_use(Node def ) {
    assert _live instanceof TypeStruct ts && ts.flatten_live_fields()==ts;
    if( def==adr() ) return Type.ALL;
    // Memory demands
    adr().deps_add(def);
    Type ptr = adr()._val;
    if( ptr instanceof TypeStruct ) return ptr.oob(TypeMem.ALLMEM); // Loading from a clazz
    TypeMemPtr tptr=null;
    if( !(ptr instanceof TypeMemPtr tptr0) ) {
      // Go from the incoming primitive to a Clazz struct
      StructNode clz = FieldNode.clz_node(ptr);
      if( clz==null ) return RootNode.def_mem(def);
      // Use the One True Alias for the primitive Clazz
      for( Node use : clz._uses ) {
        if( use instanceof StoreNode st ) {
          if( st.adr() instanceof NewNode nnn ) tptr = nnn._tptr;
          break;
        }
      }
      if( tptr==null ) return ptr.oob(TypeMem.ALLMEM);
    } else tptr=tptr0;

    if( tptr.above_center() ) return TypeMem.ANYMEM; // Loaded from nothing
    if( tptr._aliases.is_empty() ) return TypeMem.ANYMEM;
    // Demand memory produce the desired structs
    return TypeMem.make(tptr._aliases,(TypeStruct)_live);
  }
  // Only structs are demanded from a Load
  @Override boolean assert_live(Type live) { return live instanceof TypeStruct; }
  
  // Strictly reducing optimizations
  @Override public Node ideal_reduce() {
    Node adr = adr();
    Type tadr = adr._val;
    // We allow Loads against structs to allow for nested (inlined) structs.
    //if( tadr instanceof TypeStruct ) return adr();
    
    // We allow Loads against unwrapped primitives, as part of the normal Oper
    // expansion in the Parser.  These are no-ops.
    if( tadr instanceof TypeInt ) return adr;
    if( tadr instanceof TypeFlt ) return adr;
    if( tadr instanceof TypeStruct ) return adr; // Overload struct
    // Dunno about other things than pointers
    if( !(tadr instanceof TypeMemPtr tmp) ) return null;
    if( adr instanceof FreshNode frsh ) adr = frsh.id();
    // If we can find an exact previous store, fold immediately to the value.
    Node ps = find_previous_struct(this, mem(),adr,tmp._aliases);
    if( ps!=null ) {
      if( ps instanceof StoreNode st ) {
        Node rez = st.rez();
        if( rez==null ) return null;
        if( _live.isa(rez._live) ) return rez; // Stall until liveness matches
        deps_add(this);                        // Self-add if live-ness updates
        return null;
      } else throw unimpl();
    }
    return null;
  }

  // Changing edges to bypass, but typically not removing nodes nor edges
  @Override public Node ideal_mono() {
    Node mem = mem();
    Node adr = adr();
    Type tadr = adr._val;
    BitsAlias aliases = tadr instanceof TypeMemPtr ? ((TypeMemPtr)tadr)._aliases : null;

    // Load can move past a Join if all aliases align.
    if( mem instanceof MemJoinNode && aliases != null ) {
    //  Node jmem = ((MemJoinNode)mem).can_bypass(aliases);
    //  if( jmem != null ) {
    //    jmem.xval();
    //    return set_mem(jmem);
    //  }
      throw unimpl();
    }

    // Load can move out of a Call, if the function has no Parm:mem - happens
    // for single target calls that do not (have not yet) inlined.
    if( mem instanceof MProjNode && mem.in(0) instanceof CallNode )
    //  return set_mem(((CallNode)mem.in(0)).mem());
      throw unimpl();

    return null;
  }

  @Override public Node ideal_grow() {
    Node mem = mem();
    Node adr = adr();
    // Load from a memory Phi; split through in an effort to sharpen the memory.
    // TODO: Only split thru function args if no unknown_callers, and must make a Parm not a Phi
    // TODO: Hoist out of loops.
    if( mem instanceof PhiNode mphi && adr instanceof NewNode && !(mphi instanceof ParmNode) ) {
      Node lphi = new PhiNode(TypeNil.SCALAR,mphi._badgc,mphi.in(0));
      for( int i=1; i<mphi._defs._len; i++ ) {
        Node ld = Env.GVN.add_work_new(new LoadNode(mphi.in(i),adr,_bad).init());
        ld._live = _live;
        lphi.add_def(ld);
      }
      lphi._live = _live;
      return lphi.init();
    }

    return null;
  }

  // Find a matching prior Store - matching address.
  // Returns null if highest available memory does not match address.
  static Node find_previous_struct(Node ldst, Node mem, Node adr, BitsAlias aliases ) {
    if( mem==null ) return null;
    // Walk up the memory chain looking for an exact matching Store or New
    int cnt=0;
    while(true) {
      cnt++; assert cnt < 100; // Infinite loop?
      if( mem instanceof StoreNode st ) {
        if( st.adr()==adr ) return st.err(true)== null ? st : null; // Exact matching store
        if( mem == st.mem() ) return null; // Parallel unrelated stores
        // Wrong address.  Look for no-overlap in aliases
        Type tst = st.adr()._val;
        if( !(tst instanceof TypeMemPtr tmp) ) return null; // Store has weird address
        BitsAlias st_alias = tmp._aliases;
        if( aliases.join(st_alias) != BitsAlias.EMPTY )
          return null;        // Aliases not disjoint, might overlap but wrong address
        // Disjoint unrelated store.
        mem = st.mem(); // Advance past

      //} else if( mem instanceof MemPrimNode.LValueWrite ) {
      //  // Array stores and field loads never alias
      //  mem = ((MemPrimNode)mem).mem();
      } else if( mem instanceof SetFieldNode sfn ) {
        throw unimpl();

      } else if( mem instanceof MProjNode ) {
        Node mem0 = mem.in(0);
        switch( mem0 ) {
        case MemSplitNode node -> mem = node.mem(); // Lifting out of a split/join region
        case CallNode     node -> mem = node.mem(); // Lifting out of a Call
        case RootNode     node -> { return null; }
        case PrimNode     prim -> { return null; }
        case CallEpiNode  node -> {
          mem = node.is_copy(MEM_IDX); // Skip thru a copy
          if( mem == null ) {
            CallNode call = node.call();
            BitsAlias esc_aliases = Env.ROOT.ralias();
            // Collides, might be use/def by call
            if( aliases.overlaps(esc_aliases) ) {
              Env.ROOT.deps_add(ldst); // Revisit if fewer escapes
              return null;
            }
            // Peek through call
            mem = call.mem();
          }
        } 

        case null, default -> throw unimpl(); // decide cannot be equal, and advance, or maybe-equal and return null
        }
      //} else if( mem instanceof MemJoinNode ) {
      //  Node jmem = ((MemJoinNode)mem).can_bypass(aliases);
      //  if( jmem == null ) return null;
      //  mem = jmem;
      //} else if( mem instanceof ParmNode ) {
      //  if( mem.in(0) instanceof FunNode && mem.in(0).is_copy(1)!=null ) mem = mem.in(1); // FunNode is dying, copy, so ParmNode is also
      //  else return null;
      //
      } else if( mem instanceof PhiNode || // Would have to match on both sides, and Phi the results'
                 mem instanceof ConNode) {
        return null;
      } else {
        throw unimpl(); // decide cannot be equal, and advance, or maybe-equal and return null
      }
    }
  }
  
  @Override public boolean has_tvar() { return true; }

  // Standard memory unification; the Load unifies with the loaded field.
  @Override public boolean unify( boolean test ) {
    TV3 self = tvar();
    TV3 adr = adr().tvar();
    return switch (adr) {
      // Wait until forced to either TVStruct or TVPtr
    case TVLeaf leaf -> leaf.deps_add_deep(this);
    case TVPtr ptr -> self.unify(ptr.load(),test);
    case TVStruct tstr -> self.unify(adr, test); // Load from prototype, just pass-thru
    case TVClz tclz    -> self.unify(adr, test); // Load from prototype, just pass-thru
    case TVBase   base -> self.unify(FieldNode.clz_tv(base._t), test); // Unify against primitive CLZ
    case TVErr err -> err.unify(self,test);
    default -> throw unimpl();
    };
  }

}
