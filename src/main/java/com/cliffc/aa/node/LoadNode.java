package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;

import static com.cliffc.aa.AA.*;

// Load a struct from memory.  Does its own nil-check testing.  Display/Frames
// are normal structs, so local vars are ALSO normal struct loads.

public class LoadNode extends Node {
  // Field being loaded from a TypeStruct.  If "_", the field name is inferred
  // from amongst the field choices.  If not present, then error.
  public       String _fld;
  // Where to report errors
  private final Parse _bad;
  // Prevent recursive expansion during ideal_grow
  private boolean _mid_grow;

  // A struct using just the field; just a cache for faster live-use
  private final TypeStruct _live_use;

  public LoadNode( Node mem, Node adr, String fld, Parse bad ) {
    super(null,mem,adr);
    _fld = fld;
    _bad = bad;
    _live_use = TypeStruct.UNUSED.add_fldx(TypeFld.make(_fld,Type.ALL));
  }
  // A plain "_" field is a resolving field
  @Override public String label() { return "."+_fld; }   // Self short name
  
  Node mem() { return in(MEM_IDX); }
  Node adr() { return in(DSP_IDX); }
  private Node set_mem(Node a) { return setDef(MEM_IDX,a); }

  @Override public Type value() {
    Type tadr = adr()._val;
    Type tmem = mem()._val;

    if( !(tadr instanceof TypeNil ta) || (tadr instanceof TypeFunPtr) )
      return tadr.oob(); // Not an address
    if( !(tmem instanceof TypeMem tm) )
      return tmem.oob(); // Not a memory
    if( ta==TypeNil.NIL || ta==TypeNil.XNIL )
      ta = (TypeNil)ta.meet(PrimNode.PINT._val);

    // Exactly only prior Operator Binds produce Deep Ptrs, and these do
    // field-selects from the struct instead of loads.
    TypeStruct ts = ta instanceof TypeMemPtr tmp && !tmp.is_simple_ptr()
      ? tmp._obj
      : tm.ld(ta);

    Type t = lookup(ts,tm,_fld);
    if( t!=null ) return t;

    // Did not find field
    return Env.ROOT.ext_scalar(this);
  }


  // Field lookup, might check superclass
  static Type lookup( TypeStruct ts, TypeMem mem, String fld ) {
    
    // Check for direct field
    int idx = ts.find(fld);
    if( idx != -1 ) return ts.at(idx);

    // Have a super class?
    if( ts.len()==0 || !Util.eq(ts.fld(0)._fld,TypeFld.CLZ) )
      return ts._def.above_center() ? TypeNil.XSCALAR : null;

    // Miss on closed structs looks at superclass.
    TypeNil ptr = (TypeNil)ts.fld(0)._t; // Load clazz ptr
    // Load the clazz struct type from memory
    ts = mem.ld(ptr);
    return lookup(ts,mem,fld);
  }

  
  // The only memory required here is what is needed to support the Load.
  // If the Load is alive, so is the address.
  @Override public Type live_use( int i ) {
    //assert _live==Type.ALL;
    Type adr = adr()._val;
    // Since the Load is alive, the address is alive
    if( i!=MEM_IDX ) return Type.ALL;
    // Memory demands
    Node def=mem();
    // If adr() value changes, the def liveness changes; this is true even if
    // def is ALSO adr().def() which the normal deps_add asserts prevent.
    adr().deps_add_live(def);
    if( adr.above_center() ) return Type.ANY; // Nothing is demanded
    
    // Demand everything not killed at this field.
    if( !(adr instanceof TypeNil ptr) || // Not a ptr, assume it becomes one
        ptr._aliases==BitsAlias.NALL )   // All aliases, then all mem needed
      return RootNode.removeKills(def);  // All mem minus KILLS
  
    // TODO: Liveness for generic clazz fields
    //if( ptr instanceof TypeMemPtr tmp && !tmp.is_simple_ptr() ) {
    //  tmp._obj.get(TypeFld.CLZ);
    //}
    
    if( ptr._aliases.is_empty() ) return Type.ANY; // Nothing is demanded still

    // Demand field "_fld" be "ALL", which is the default
    return TypeMem.make(ptr._aliases,_live_use);
  }
  
  // Strictly reducing optimizations
  @Override public Node ideal_reduce() {
    Node adr = adr();
    Type tadr = adr._val;

    // Dunno about other things than pointers
    if( !(tadr instanceof TypeNil tn) ) return null;
    //if( adr instanceof FreshNode frsh ) adr = frsh.id();
    // If we can find an exact previous store, fold immediately to the value.
    Node ps = find_previous_struct(this, mem(), adr, tn._aliases);
    if( ps instanceof StoreAbs sta ) {
      if( sta instanceof StoreNode st ) {
        if( Util.eq(_fld,st._fld) ) // match field in store
          return st.rez();
      } else {
        // find struct, match field in struct
        StructNode str = ((StoreXNode)sta).struct();
        int idx = str.find(_fld);
        if( idx == -1 ) return null; // Repeat a fixed-class lookup?
        Node val = str.in(idx);
        // demand val&live monotonic or deps_add
        if( val._val.isa(_val) && _live.isa(val._live) )
          return val;
        deps_add(this);         // Self-add if updates
        val.deps_add(this);     // Val -add if updates
        return null;        
      }
    }

    return null;
  }

  // Changing edges to bypass, but typically not removing nodes nor edges
  @Override public Node ideal_mono() {
    Node mem = mem();
    Node adr = adr();
    Type tadr = adr._val;
    BitsAlias aliases = tadr instanceof TypeMemPtr ? ((TypeMemPtr)tadr)._aliases : null;

    // Load can move past a Call if there's no escape.  Not really a reduce,
    // but depends on the deps mechanism.
    if( mem instanceof MProjNode mprj ) {
      if( mprj.in(0) instanceof CallEpiNode cepi && !cepi._is_copy ) {
        if( adr instanceof NewNode nnn && !nnn.escaped(this) ) {
          //Env.GVN.add_reduce(this); // Re-run reduce
          //return set_mem(cepi.call().mem());
          throw TODO();
        }
      }
    }

    // Load can move past a Join if all aliases align.
    if( mem instanceof MemJoinNode && aliases != null ) {
    //  Node jmem = ((MemJoinNode)mem).can_bypass(aliases);
    //  if( jmem != null ) {
    //    jmem.xval();
    //    return set_mem(jmem);
    //  }
      throw TODO();
    }

    return null;
  }

  @Override public Node ideal_grow() {
    // Load from a memory Phi; split through in an effort to sharpen the memory.
    // TODO: Hoist out of loops.
    if( !_mid_grow && mem() instanceof PhiNode mphi && split_load_profit() ) {
      _mid_grow=true;           // Prevent recursive trigger when calling nested xform
      //Node adr = adr();
      //Node[] ns = new Node[mphi.len()];
      //for( int i=1; i<mphi.len(); i++ ) {
      //  ns[i] = new LoadNode(mphi.in(i),adr,_fld,_bad).peep();
      //  ns[i].push();
      //}
      //Node.pops(mphi.len()-1);
      //Node lphi = new PhiNode(TypeStruct.ISUSED,mphi._badgc,mphi.in(0));
      //for( int i=1; i<mphi.len(); i++ )
      //  lphi.addDef(ns[i]);
      //lphi._live = _live;
      //return lphi.peep();
      throw TODO();
    }

    return null;
  }

  // Profit to split a load thru a Phi?
  private boolean split_load_profit() {
    Node adr = adr();
    // Only split if the address is known directly
    if( !(adr instanceof NewNode) ) return false;
    // Do not split if we think a following store will fold already
    if( nUses()==1 && use0() instanceof StoreNode st && st.adr()==adr )
      return false;
    return true;
  }

  // If true, can bypass.
  @Override boolean ld_st_check(StoreAbs st) {
    assert adr()==st.adr();
    // Check if fld hits in a StoreX or direct StoreNode.fld
    if( st instanceof StoreNode stf )
      return !Util.eq(stf._fld,_fld);
    // Assume the StoreX hits the field in question
    return false;
  }

  
  // Find a matching prior Store - matching address.
  // Returns null if highest available memory does not match address.
  static Node find_previous_struct(Node ldst, Node mem, Node adr, BitsAlias aliases ) {
    if( mem==null ) return null;
    // Walk up the memory chain looking for an exact matching Store or New
    int cnt=0;
    while(true) {
      cnt++; assert cnt < 100; // Infinite loop?
      if( mem instanceof StoreAbs st ) {
        if( st.adr()==adr ) {
          if( !ldst.ld_st_check(st)  )
            return st.err(true)== null ? st : null; // Exact matching store
        } else {
          st.adr().deps_add(ldst); // If store address changes
          if( mem == st.mem() ) return null; // Parallel unrelated stores
          // Wrong address.  Look for no-overlap in aliases
          Type tst = st.adr()._val;
          if( !(tst instanceof TypeMemPtr tmp) ) return null; // Store has weird address
          BitsAlias st_alias = tmp._aliases;
          if( aliases.join(st_alias) != BitsAlias.EMPTY )
            return null;        // Aliases not disjoint, might overlap but wrong address
        }
        // Disjoint unrelated store.
        mem = st.mem(); // Advance past

      } else if( mem instanceof MProjNode ) {
        Node mem0 = mem.in(0);
        switch( mem0 ) {
        case MemSplitNode node -> mem = node.mem(); // Lifting out of a split/join region
        case CallNode     node -> mem = node.mem(); // Lifting out of a Call
        case RootNode     node -> { return null; }
        case PrimNode     prim -> { return null; }
        case CallEpiNode  cepi -> {
          mem = cepi.isCopy(MEM_IDX); // Skip thru a copy
          if( mem == null ) {
            CallNode call = cepi.call();
            assert call.isCopy(0)==null;
            // The load is allowed to bypass the call if the alias is not killed.
            // Conservatively: the alias is not available to any called function,
            // so it's not in the reachable argument alias set and not globally escaped.
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

        case null, default -> throw TODO(); // decide cannot be equal, and advance, or maybe-equal and return null
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
        throw TODO(); // decide cannot be equal, and advance, or maybe-equal and return null
      }
    }
  }

  @Override public boolean has_tvar() { return true; }
  @Override public TV3 _set_tvar() {
    // Load takes a pointer
    TV3 ptr0 = adr().set_tvar();
    TVPtr ptr;
    if( ptr0 instanceof TVPtr ptr1 ) {
      ptr = ptr1;
    } else {
      ptr0.unify(new TVPtr(BitsAlias.EMPTY, new TVStruct(true) ),false);
      ptr = ptr0.find().as_ptr();
    } 

    // Struct needs to have the named field
    TVStruct str = ptr.load();
    TV3 fld = str.arg_clz(_fld);
    TV3 self = new TVLeaf();
    if( fld==null ) {
      str.add_fld(_fld,self );
    } else {
      self.unify(fld,false);
    }
    
    return self.find();
  }

  // All field loads against a pointer.
  @Override public boolean unify( boolean test ) {
    TV3 ptr0 = adr().tvar();

    if( ptr0 instanceof TVErr ) throw TODO();
    TVPtr ptr = ptr0.as_ptr();
    TVStruct tstr = ptr.load();
    
    // If the field is in the struct, unify and done
    TV3 fld = tstr.arg(_fld);
    if( fld!=null ) return do_fld(fld,test);
    // If the struct is open, add field here and done.
    if( tstr.is_open() ) return test || tstr.add_fld(_fld,tvar() );

    // Search up the super-clazz chain
    for( ; tstr.len()>0; tstr = tstr.pclz().load() ) {
      assert !tstr.is_open();  // Invariant: superclazzes not open
      // If the field is in the struct, unify and done
      fld = tstr.arg(_fld);
      if( fld!=null ) return do_fld(fld,test);
    }

    // struct is end-of-super-chain, miss_field
    //return tvar().unify_err(resolve_failed_msg(),tvar(0),null,test);
    throw TODO();
  }

  private boolean do_fld( TV3 fld, boolean test ) {
    if( tvar() instanceof TVLeaf leaf ) leaf.set_no_progress();
    return tvar().unify(fld,test);
  }

  @Override int hash() { return _fld.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof LoadNode fld) ) return false;
    return Util.eq(_fld,fld._fld);
  }

}
