package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.*;

// Load a struct from memory.  Does its own nil-check testing.
//
// Load is used on primitives as well as normal struct loads.  Display/Frames
// are normal structs, so local vars are ALSO normal struct loads.

//"x.y"
// Op   Adr   Value
// Load ptr   TypeStruct
// Field y    field       
// Bind ptr   bound lambda, or original field
//
//"1._+_._"
// Op   Adr   Value
// Load  1    @{ INT CLAZZ }
// Field _+_  (unbound function choices)
// Bind  1    (  bound function choices)
// Load  ts   (  bound function choices) --since ptr is TypeStruct, no-op
// Field _       bound function
// Bind  ts      bound function          --since ptr is TypeStruct, no-op

//"1+2"
// Load  1    @{ INT CLAZZ }
// Field y    (unbound function choices)
// Field _     unbound function
// Bind  1       bound function

public class LoadNode extends Node {
  private final Parse _bad;
  private boolean _mid_grow;

  public LoadNode( Node mem, Node adr, Parse bad ) {
    super(OP_LOAD,null,mem,adr);
    _bad = bad;
    _live=TypeStruct.ISUSED;
  }
  Node mem() { return in(MEM_IDX); }
  Node adr() { return in(DSP_IDX); }
  private Node set_mem(Node a) { return set_def(MEM_IDX,a); }

  @Override public Type value() {
    Type tadr = adr()._val;
    Type tmem = mem()._val;

    // Loads can be issued directly against a TypeStruct, if we are loading
    // against an inlined object.  In this case the Load is a no-op.
    if( (tadr instanceof TypeStruct ts) )
      return ts;                // Happens if user directly calls an oper
    if( !(tadr instanceof TypeNil ta) )
      return tadr.oob(TypeStruct.ISUSED); // Not a address
    if( !(tmem instanceof TypeMem tm) )
      return tmem.oob(TypeStruct.ISUSED); // Not a memory
    if( ta==TypeNil.NIL || ta==TypeNil.XNIL )
      ta = (TypeNil)ta.meet(PrimNode.PINT._val);

    return tm.ld(ta);
  }

  // The only memory required here is what is needed to support the Load.
  // If the Load is alive, so is the address.

  // If the Load computes a constant, the address live-ness is determined how
  // Combo deals with constants, and not here.
  @Override public Type live_use( int i ) {
    assert _live instanceof TypeStruct ts && ts.flatten_live_fields()==ts;
    if( i==DSP_IDX )
      // If the input is a Struct and not a Pointer, this Load is a nop
      return adr()._val instanceof TypeStruct ? _live : Type.ALL;
    // Memory demands
    Node def=in(i);
    adr().deps_add(def);
    Type adr = adr()._val;
    if( adr==Type.ANY ) return TypeMem.ANYMEM;
    if( !(adr instanceof TypeNil ptr) )
      return adr.oob(RootNode.def_mem(def));

    if( ptr.above_center() ) return TypeMem.ANYMEM; // Loaded from nothing
    // Loading from a struct does not require memory
    if( ptr instanceof TypeStruct ) return TypeMem.ANYMEM;
    
    // Demand memory produce the desired structs
    if( ptr._aliases==BitsAlias.NALL ) return RootNode.def_mem(def);
    return TypeMem.make(ptr._aliases,(TypeStruct)_live);
  }
  // Only structs are demanded from a Load
  @Override boolean assert_live(Type live) { return live instanceof TypeStruct; }
  
  // Strictly reducing optimizations
  @Override public Node ideal_reduce() {
    Node adr = adr();
    Type tadr = adr._val;
    // We allow Loads against structs to allow for inlined structs.
    // The Load is a no-op
    if( tadr instanceof TypeStruct ) return adr();
    
    // Dunno about other things than pointers
    if( !(tadr instanceof TypeNil tn) ) return null;
    if( adr instanceof FreshNode frsh ) adr = frsh.id();
    // If we can find an exact previous store, fold immediately to the value.
    Node ps = find_previous_struct(this, mem(),adr,tn._aliases);
    if( ps instanceof StoreNode st ) {
      Node rez = st.rez();
      if( rez==null ) return null;
      if( _live.isa(rez._live) ) return rez; // Stall until liveness matches
      deps_add(this);                        // Self-add if live-ness updates
      return null;
    }

    // Load can move past a Call if there's no escape.  Not really a reduce,
    // but depends on the deps mechanism.
    Node mem = mem();
    if( mem instanceof MProjNode mprj ) {
      if( mprj.in(0) instanceof CallEpiNode cepi && !cepi._is_copy ) {
        if( adr instanceof NewNode nnn && !nnn.escaped(this) ) {
          Env.GVN.add_reduce(this); // Re-run reduce
          return set_mem(cepi.call().mem());
        } else adr.deps_add(this);
      }
    } else mem.deps_add(this);
    
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

    return null;
  }

  @Override public Node ideal_grow() {
    // Load from a memory Phi; split through in an effort to sharpen the memory.
    // TODO: Hoist out of loops.
    if( !_mid_grow && mem() instanceof PhiNode mphi && split_load_profit() ) {
      _mid_grow=true;           // Prevent recursive trigger when calling nested xform
      Node adr = adr();
      Node[] ns = new Node[mphi.len()];
      for( int i=1; i<mphi.len(); i++ ) {
        ns[i] = Env.GVN.xform(new LoadNode(mphi.in(i),adr,_bad));
        ns[i].push();
      }
      Node.pops(mphi.len()-1);
      Node lphi = new PhiNode(TypeStruct.ISUSED,mphi._badgc,mphi.in(0));
      for( int i=1; i<mphi.len(); i++ )
        lphi.add_def(ns[i]);
      lphi._live = _live;
      lphi.xval();
      return lphi;
    }

    return null;
  }

  // Profit to split a load thru a Phi?
  private boolean split_load_profit() {
    Node adr = adr();
    // Only split if the address is known directly
    if( !(adr instanceof NewNode) ) return false;
    // Do not split if we think a following store will fold already
    if( _uses._len==1 && _uses.at(0) instanceof StoreNode st && st.adr()==adr )
      return false;
    return true;
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
        st.adr().deps_add(ldst); // If store address changes
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
        case CallEpiNode  cepi -> {
          mem = cepi.is_copy(MEM_IDX); // Skip thru a copy
          if( mem == null ) {
            CallNode call = cepi.call();
            assert call.is_copy(0)==null;
            // The load is allowed to bypass the call if the alias is not killed.
            // Conservatively: the alias is not available to any called function,
            // so its not in the reachable argument alias set and not globally escaped.
            BitsAlias esc_aliases = Env.ROOT.ralias();
            // Collides, might be use/def by call
            if( aliases.overlaps(esc_aliases) ) {
              Env.ROOT.deps_add(ldst); // Revisit if fewer escapes
              return null;
            }
            // Compute direct call argument set
            BitsAlias as = BitsAlias.EMPTY;
            for( int i=DSP_IDX; i<call.nargs(); i++ ) {
              Type targ = call.val(i);
              if( targ instanceof TypeFunPtr tfp ) targ = tfp.dsp();
              if( targ instanceof TypeMemPtr tmp ) as = as.meet(tmp.aliases());
            }
            // Check for overlap with the reachable aliases
            TypeMem cmem = CallNode.emem((TypeTuple)call._val);
            if( aliases.overlaps(as) || aliases.overlaps(cmem.all_reaching_aliases(as)) ) {
              call.deps_add(ldst); // Revisit if fewer escapes
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
      } else if( mem instanceof  PhiNode ||  // Would have to match on both sides, and Phi the results'
                 mem instanceof ParmNode ||  // Would have to match all callers, after all is wired
                 mem instanceof  ConNode) {
        return null;
      } else {
        throw unimpl(); // decide cannot be equal, and advance, or maybe-equal and return null
      }
    }
  }
  
  @Override public boolean has_tvar() { return true; }
  @Override public TV3 _set_tvar() {
    TV3 ptr = adr().set_tvar();
    // This load could be a no-op, eventually, if it's loading from a struct
    if( ptr instanceof TVPtr tptr ) return tptr.load();
    return new TVLeaf();
  }

  // All field loads against a pointer.
  @Override public boolean unify( boolean test ) {
    TV3 ptr = adr().tvar();
    if( ptr instanceof TVPtr tptr )
      return tptr.load().unify(tvar(),test);
    // No-Op load against an inlined struct
    if( ptr instanceof TVStruct ts )
      throw unimpl();
    // Stall
    assert ptr instanceof TVLeaf || ptr instanceof TVErr;
    return false;
  }

}
