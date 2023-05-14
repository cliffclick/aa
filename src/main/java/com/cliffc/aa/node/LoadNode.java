package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;

import static com.cliffc.aa.AA.*;

// Load a struct from memory.  Does its own nil-check testing.
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

    // Load can move past a Call if there's no escape.  Not really a reduce,
    // but depends on the deps mechanism.
    Node mem = mem();
    if( mem instanceof MProjNode mprj ) {
      if( mprj.in(0) instanceof CallEpiNode cepi ) {
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
    // Force mem input to be a mem
    TV3 t0 = mem().set_tvar(); 
    if( !(t0 instanceof TVMem) )
      t0.unify(new TVMem(),false);
    // Address needs to be one of a TVPtr or TVBase, but cannot tell.
    // IF its a TVBase, we can get the CLZ ptr from it.
    // Self is just an open TVStruct
    return new TVStruct(true);
  }

  // Incoming address is
  // - Leaf - stall, need address TV3
  // - Nil  - stall, need address TV3
  // - Ptr  - classic memory/struct unify Clz:[---,@{instance}]
  // - Base - Base._t dictates clz ptr; memory/clz-struct unify
  // - Clz  - [clz ptr, instance]; memory/clz-struct unify but report a new Clz:[@{CLZ},@{instance}]
  // - Clz  - [clz ptr, ptr     ]; memory/clz-struct unify but report a new Clz:[@{CLZ},@{instance}] (load both)
  // Self type is always a Clz:[@{CLZ},@{instance}]
  // - Either part might be empty & closed (use same single instance, Combo:TVStruct EMPTY).
  
  @Override public boolean unify( boolean test ) {
    TVStruct self = (TVStruct)tvar();
    TVMem mem = (TVMem)mem().tvar();
    TV3 adr = adr().tvar();
    return switch( adr ) {
    // Stall until forced to Base,Clz or Err of same
    case TVLeaf leaf   -> leaf.deps_add_deep(this);
    //case TVStruct tstr -> self.unify(adr, test); // Load from prototype, just pass-thru
    //case TVClz tclz    -> do_clz (self,tclz,test);
    case TVBase base   -> do_base(self,base,test);
    //case TVErr err     -> {
    //  if( err.as_int()!=null ) yield do_base(self,err.as_int(),test);
    //  if( err.as_flt()!=null ) yield do_base(self,err.as_flt(),test);
    //  if( err.as_clz()!=null ) yield do_clz (self,err.as_clz(),test);
    //  yield err.unify(self,test);// Pass error along
    //}
    //case TVNil tnil    -> tnil.deps_add_deep(this); // Stall until this settles out
    //case TVPtr ptr     -> mem.unify(ptr,self,test);
    default -> throw unimpl();
    };
  }

  private static boolean do_base(TVStruct self, TVBase base, boolean test) {
    // Bases field their prototype via the TypeNil type, and from there the CLZ
    StructNode proto = FieldNode.clz_node(base._t);
    TVStruct base_clz = proto.tvar().as_struct();
    return self.unify(base_clz, test); // Unify against primitive CLZ
  }
  //
  //private boolean do_clz(TVClz self, TVClz clz, boolean test) {
  //  // Loading from a prior struct case: "e0._*_._".  No "Load" action is
  //  // required, but the parser inserts in case the prior was a ptr.
  //  if( clz.arg(1) instanceof TVStruct )
  //    return self.unify(clz,test);
  //  //  mem.unify(tclz.ptr(),self,test); // Load from prototype
  //  throw unimpl();
  //}
  
}
