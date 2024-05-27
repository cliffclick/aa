package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;

import static com.cliffc.aa.AA.*;

// Load a struct from memory.  Does its own nil-check testing.  Display/Frames
// are normal structs, so local vars are ALSO normal struct loads.

// Loaded function pointers are *bound* - the base ptr is passed as the first
// argument to the function pointer, and are the "display" in the TFP.
// Currying by any other name!

// DynLoads inherit from Load, and have basically the same behavior except
// that the field is specified as an offset passed in an extra input.  The
// field is selected based on overload resolution using the HM TVars.

// Value matrix:
// Address is not a TMP - return OOB(adr)
// Memory  is not a MEM - return OOB(mem)
// TMP is deep - use given TS; true for primitives and overloads
// TMP is shallow - use MEM.ld(TMP)
//
// For DynLoads, meet all/resolved fields.
// For    Loads, just the loaded field.
//
// If TMP is shallow, attempt a Bind:
//   If DSP is alive use adr else use XSCALAR.
//   If loading a single field and its a TFP, Bind it (even if already bound -error)
//   If loading a TMP, load again to a TS and Bind deep, returning a deep TMP.


public class LoadNode extends Node {
  // Field being loaded from a TypeStruct.  If "_", the field name is inferred
  // from amongst the field choices.  If not present, then error.
  public String _fld;
  // Where to report errors
  final Parse _bad;
  // When doing HM, treat this Load as a identifier load and allow the type
  // LET-polymorphism.  When false, this Load could be a struct field load,
  // OR it could be self-recursive definition, OR it could be unknown.
  boolean _fresh;

  // Prevent recursive expansion during ideal_grow
  private boolean _mid_grow;

  // A struct using just the field; just a cache for faster live-use
  private final TypeStruct _live_use;

  public LoadNode( Node mem, Node adr, String fld, boolean fresh, Parse bad ) {
    super(null,mem,adr);
    _fld = fld;
    _bad = bad;
    _live_use = TypeStruct.UNUSED.add_fldx(TypeFld.make(_fld,Type.ALL));
  }
  // A plain "_" field is a resolving field
  @Override public String label() { return ("."+_fld).intern(); }   // Self short name

  Node mem() { return in(MEM_IDX); }
  Node adr() { return in(DSP_IDX); }
  private Node set_mem(Node a) { return setDef(MEM_IDX,a); }

  @Override public final Type value() {
    Type tadr = adr()._val;
    Type tmem = mem()._val;

    if( !(tadr instanceof TypeNil ta) || (tadr instanceof TypeFunPtr) )
      return tadr.oob(); // Not an address
    if( !(tmem instanceof TypeMem tm) )
      return tmem.oob(); // Not a memory
    if( ta==TypeNil.NIL || ta==TypeNil.XNIL )
      ta = (TypeNil)ta.meet(PrimNode.PINT._val);

    // Load the matching struct from memory / deep ptr
    TypeStruct ts = ta instanceof TypeMemPtr tmp && !tmp.is_simple_ptr()
      ? tmp._obj                // Primitives are not-simple
      : tm.ld(ta);

    // Field lookup, might check superclass.
    // DynLoads check all fields.
    Type t = lookup(ts,tm);

    // See if binding to the display:
    // If a deep (and not primitive) pointer, it has already been bound
    TypeNil dsp = ta instanceof TypeMemPtr tmp && !tmp.is_simple_ptr() && !tmp.is_prim() ? null : ta;

    // Optionally bind Display
    return value_bind(t, tm, dsp, true);
  }

  private Type value_bind( Type t, TypeMem tm, TypeNil dsp, boolean over ) {
    // t is high - might fall to TFP or TMP or neither, no binding (yet)
    if( t.above_center() )
      return t;

    // t is TFP  - assert input does NOT transit unbound->bound.  If unbound bind, else no-op.
    if( t instanceof TypeFunPtr tfp ) {
      if( dsp == null ) return tfp; // No display to bind
      if( tfp.has_dsp() ) return tfp; // Already bound, no double-binding
      // Bind
      return tfp.make_from(dsp);
    }

    // t is TMP  - Bind recursively one-step, else treat as lo
    if( t instanceof TypeMemPtr tmp && !tmp.is_prim() && over ) {
      assert tmp.is_simple_ptr();
      TypeStruct ts = tm.ld(tmp);
      TypeFld[] flds = TypeFlds.get(ts.len());
      for( int i=0; i<flds.length; i++ )
        flds[i] = ts.fld(i).make_from(value_bind(ts.fld(i)._t,tm,dsp,false));
      return tmp.make_from(ts.make_from(flds));
    }

    // t is lo (or TMP 2steps deep) - no-op/pass-thru
    return t;
  }

  // Lookup and return field type.
  // If no field, be conservative.
  Type lookup( TypeStruct ts, TypeMem mem ) {
    return lookup(ts,mem,_fld);
  }

  static Type lookup( TypeStruct ts, TypeMem mem, String fld ) {
    Type t = _lookup(ts,mem,fld);
    if( t!=null ) return t;     // Got it
    if( ts._def.above_center() ) return Type.ANY; // Might fall to having field
    // Return worse possible escaped scalar
    return Env.ROOT.ext_scalar(null);
  }

  // Field lookup, might recursively check superclass.
  // Returns field type or null.
  private static Type _lookup( TypeStruct ts, TypeMem mem, String fld ) {

    // Check for direct field
    int idx = ts.find(fld);
    if( idx != -1 ) return ts.at(idx);

    // Have a super class?
    if( ts.len()==0 || !Util.eq(ts.fld(0)._fld,TypeFld.CLZ) )
      return null;

    // Miss on closed structs looks at superclass.
    TypeNil ptr = (TypeNil)ts.fld(0)._t; // Load clazz ptr
    // Load the clazz struct type from memory
    ts = mem.ld(ptr);
    return _lookup(ts,mem,fld);
  }

  // The only memory required here is what is needed to support the Load.
  // If the Load is alive, so is the address.
  @Override public final Type live_use( int i ) {
    // Since the Load is alive, the address is alive
    if( i!=MEM_IDX ) return Type.ALL;
    Type adr = adr()._val;
    // Memory demands
    Node def = mem();
    // If adr() value changes, the def liveness changes; this is true even if
    // def is ALSO adr().def() which the normal deps_add asserts prevent.
    adr().deps_add_live(def);
    // Not a pointer yet
    if( !(adr instanceof TypeNil ptr) )
      return adr.oob();
    // Not a memory yet
    if( !(def._val instanceof TypeMem mem) )
      return def._val.oob();
    // Check for sane aliases
    if( ptr._aliases.is_empty() || ptr.above_center() )
      return Type.ANY;          // Nothing is demanded still
    if( ptr._aliases==BitsAlias.NALL )  // All memory?
      return RootNode.removeKills(def); // All mem minus KILLS

    // Demand field "_fld" be "ALL", which is the default
    return _live_use(ptr,mem);
  }

  Type _live_use(TypeNil ptr, TypeMem mem) {
    return TypeMem.make(ptr._aliases,_live_use);
  }

  // Strictly reducing optimizations
  @Override public Node ideal_reduce() {
    boolean progress = false;
    Node adr = adr();
    Type tadr = adr._val;

    // Dunno about other things than pointers
    if( !(tadr instanceof TypeNil tn) ) return null;
    //if( adr instanceof FreshNode frsh ) adr = frsh.id();
    Node ps = find_previous_struct(this, mem(), adr, tn._aliases);
    // Move memory higher, bypassing unrelated memory ops
    if( ps != mem() ) {
      set_mem(ps);
      progress = true;
    }

    // If we can find an exact previous store, fold immediately to the value.
    if( ps instanceof StoreAbs sta && sta.adr()==adr ) {
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

    return progress ? this : null;
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
      //throw TODO();
      return null;
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
    if( Util.eq(_fld,"$dyn")) return false; // TODO, unblock this
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


  // Bypasses as much memory as possible, returning the highest memory possible.
  static Node find_previous_struct(Node ldst, Node mem, Node adr, BitsAlias aliases ) {
    if( mem==null ) return null;
    // Walk up the memory chain looking for an exact matching Store or New
    int cnt=0;
    while(true) {
      cnt++; assert cnt < 100; // Infinite loop?
      if( mem instanceof StoreAbs st ) {
        if( st.adr()==adr ) {
          if( !ldst.ld_st_check(st)  )
            return mem; // Exact matching store
        } else {
          st.adr().deps_add(ldst); // If store address changes
          if( mem == st.mem() ) return mem; // Parallel unrelated stores
          // Wrong address.  Look for no-overlap in aliases
          Type tst = st.adr()._val;
          if( !(tst instanceof TypeMemPtr tmp) ) return mem; // Store has weird address
          BitsAlias st_alias = tmp._aliases;
          if( aliases.join(st_alias) != BitsAlias.EMPTY )
            return mem;        // Aliases not disjoint, might overlap but wrong address
        }
        // Disjoint unrelated store.
        mem = st.mem(); // Advance past

      } else if( mem instanceof MProjNode ) {
        Node mem0 = mem.in(0);
        switch( mem0 ) {
        case MemSplitNode node -> mem = node.mem(); // Lifting out of a split/join region
        case CallNode     node -> mem = node.mem(); // Lifting out of a Call
        case RootNode     node -> { return mem; }
        case PrimNode     prim -> { return mem; }
        case CallEpiNode  cepi -> {
          Node copymem = cepi.isCopy(MEM_IDX); // Skip thru a copy
          if( copymem == null ) {
            CallNode call = cepi.call();
            assert call.isCopy(0)==null;
            // The load is allowed to bypass the call if the alias is not killed.
            // Conservatively: the alias is not available to any called function,
            // so it's not in the reachable argument alias set and not globally escaped.
            BitsAlias esc_aliases = Env.ROOT.ralias();
            // Collides, might be use/def by call
            if( aliases.overlaps(esc_aliases) ) {
              Env.ROOT.deps_add_live(ldst); // Revisit if fewer escapes
              return mem;
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
              return mem;
            }
            // Peek through call
            mem = call.mem();
          } else {
            mem = copymem;
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
        return mem;
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
    if( !(o instanceof LoadNode ld) ) return false;
    if( _fresh != ld._fresh ) return false;   // Fresh field does differ
    return Util.eq(_fld,ld._fld);
  }

}
