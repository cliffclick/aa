package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;

import static com.cliffc.aa.AA.*;

// Load a struct from memory.  Does its own nil-check testing.
//
// Load is used on primitives as well as normal struct loads.  Display/Frames
// are normal structs, so local vars are ALSO normal struct loads.

//"x.y"
// Op     Adr   Value
// Load.y ptr   field
// Bind   ptr   bound lambda, or original field
//
//"1._+_._"
// Op       Adr   Value
// Load._+.  1    (unbound function choices from INT CLZ)
// Bind      1    (  bound function choices)
// Load._   ts       bound function
// Bind     ts       bound function --since ptr is TypeStruct, no-op

//"1+2"
// Load._+_  1    (unbound function choices)
// Bind      1       bound function

public class LoadNode extends Node implements Resolvable {
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
    super(OP_LOAD,null,mem,adr);
    _fld = resolve_fld_name(fld);
    _bad = bad;
    _live_use = TypeStruct.UNUSED.add_fldx(TypeFld.make(_fld,Type.ALL));
  }
  // A plain "_" field is a resolving field
  private String resolve_fld_name(String fld) { return Util.eq(fld,"_") ? ("&"+_uid).intern() : fld; }
  @Override public String xstr() { return "."+(is_resolving() ? "_" : _fld); }   // Self short name
  String  str() { return xstr(); } // Inline short name
  @Override public boolean is_resolving() { return Resolvable.is_resolving(_fld); }
  @Override public String fld() { assert !is_resolving(); return _fld; }
  // Set the resolved field label
  @Override public String resolve(String label) {
    assert !Combo.HM_AMBI;  // Must resolve before ambiguous field pass
    unelock();                  // Hash changes since label changes
    String old = _fld;
    _fld = label;
    add_flow();
    in(1).add_flow(); // Liveness sharpens to specific field
    return old;
  }

  
  Node mem() { return in(MEM_IDX); }
  Node adr() { return in(DSP_IDX); }
  private Node set_mem(Node a) { return set_def(MEM_IDX,a); }

  @Override public Type value() {
    Type tadr = adr()._val;
    Type tmem = mem()._val;

    if( !(tadr instanceof TypeNil ta) || (tadr instanceof TypeFunPtr) )
      return tadr.oob(); // Not an address
    if( !(tmem instanceof TypeMem tm) )
      return tmem.oob(); // Not a memory
    if( ta==TypeNil.NIL || ta==TypeNil.XNIL )
      ta = (TypeNil)ta.meet(PrimNode.PINT._val);

    // Loads can be issued directly against a TypeStruct, if we are loading
    // against an inlined object.  In this case the Load is a no-op.
    TypeStruct ts = ta instanceof TypeStruct ts0 ? ts0 : tm.ld(ta);

    // Still resolving, dunno which field yet
    if( is_resolving() ) {
      if( ts.above_center() ) return TypeNil.XSCALAR;
      // TODO: include clz fields
      Type t2 = ts._def;
      if( Combo.pre() || Combo.HM_AMBI ) {
        for( TypeFld t3 : ts )  t2 = t2.meet(t3._t);
      } else {
        for( TypeFld t3 : ts )  t2 = t2.join(t3._t);
      }
      return t2;
    }

    return lookup(ts,tm);
  }


  // Field lookup, might check superclass
  private Type lookup( TypeStruct ts, TypeMem mem ) {
    // Check for direct field
    int idx = ts.find(_fld);
    if( idx != -1 ) return ts.at(idx);
    // Miss on open structs dunno if the field will yet appear
    if( ts._def==Type.ANY ) return Type.ANY;
    // Miss on closed structs looks at superclass.
    if( ts.len()>=1 && Util.eq(ts.fld(0)._fld,TypeFld.CLZ) ) {
      TypeMemPtr ptr = (TypeMemPtr)ts.fld(0)._t;
      TypeStruct obj = mem.ld(ptr);
      return lookup(obj,mem);
    }
    return ts._def;
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
    adr().deps_add(def);
    if( adr.above_center() ) return Type.ANY; // Nothing is demanded
    if( !(adr instanceof TypeNil ptr) )  // Demand everything not killed at this field
      // TODO: use kills and _live_use
      return TypeMem.ALLMEM;
  
    if( ptr._aliases.is_empty() )  return Type.ANY; // Nothing is demanded still
    // Loading from a struct does not require memory, but still needs the field
    if( ptr instanceof TypeStruct ) throw unimpl();

    // Demand memory produce the desired field from a struct
    if( ptr._aliases==BitsAlias.NALL )
      return TypeMem.ALLMEM; // return RootNode.def_mem(def);
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
        // match field in store
        throw unimpl();
      } else {
        // find struct, match field in struct
        StructNode str = ((StoreXNode)sta).struct();
        int idx = str.find(_fld);
        if( idx == -1 ) throw unimpl(); // Repeat a fixed-class lookup?
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
    //      Env.GVN.add_reduce(this); // Re-run reduce
    //      return set_mem(cepi.call().mem());
          throw unimpl();
        } else adr.deps_add(this);
      }
    } else mem.deps_add(this);

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
        ns[i] = Env.GVN.xform(new LoadNode(mphi.in(i),adr,_fld,_bad));
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
      if( mem instanceof StoreAbs st ) {
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
    if( is_resolving() )
      TVField.FIELDS.put(_fld,this); // Track resolving field names
    // Unsure if input is a ptr or a struct
    return new TVLeaf();
  }

  // All field loads against a pointer.
  @Override public boolean unify( boolean test ) {
    boolean progress = false;
    TV3 ptr0 = adr().tvar();
    Type ta = adr()._val;

    // See if we force the input to choose between ptr and struct.
    // Get a struct in the end
    if( ptr0 instanceof TVErr ) throw unimpl();
    TV3 ptr1 = ptr0;            // TODO: error might already be a Ptr or Struct
    TVStruct tstr=null;
    if( ptr1 instanceof TVLeaf ) { // Leaf, because we do not know if looking at a ptr or struct yet
      if( ta instanceof TypeStruct ) { // Struct: standard for wrapped primitives
        //tstr = (TVStruct)TV3.from_flow(ta);
        tstr = new TVStruct(true);
        progress = ptr1.unify(tstr,test);
      } else if( ta instanceof TypeMemPtr ) {
        throw unimpl();         // Force ptr
      } if( ta == TypeNil.NIL || ta == TypeNil.XNIL ) {
        throw unimpl();
      }
      // No progress, just stall until adr falls to ptr or struct
      if( !progress ) {
        adr().deps_add(this);
        return false;
      }
      // Progress!
      if( test ) return true;
    } else if( ptr1 instanceof TVPtr ptr ) tstr = ptr.load();
    else if( ptr1 instanceof TVStruct ts1 ) tstr = ts1;
    else throw unimpl();

    // Attempt resolve
    if( is_resolving() )
      return try_resolve(tstr,test) | progress;
    // Look for self-resolved field; can happen
    if( TVField.FIELDS.get(resolve_fld_name(_fld)) != null )
      TVStruct.trial_resolve_all(true,tstr);

    // Search up the super-clazz chain
    for( ; tstr!=null; tstr = tstr.pclz().load() ) {
      // If the field is in the struct, unify and done
      TV3 fld = tstr.arg(_fld);
      if( fld!=null ) return do_fld(fld,test);
      // If the struct is open, add field here and done.
      // Field is not pinned, because it might belong in a superclazz
      if( tstr.is_open() ) return tstr.add_fld(_fld,tvar(),false);
    }

    // struct is end-of-super-chain, miss_field
    //return tvar().unify_err(resolve_failed_msg(),tvar(0),null,test);
    throw unimpl();
  }

  private boolean do_fld( TV3 fld, boolean test ) {
    if( tvar() instanceof TVLeaf leaf ) leaf.set_no_progress();
    return tvar().unify(fld,test);
  }

  private boolean try_resolve( TVStruct str, boolean test ) {
    // Put the resolving field in the struct; it will be present in the answer
    // in SOME field we just don't which one.
    if( str.idx(_fld) == -1 )
      str.add_fld(_fld, tvar(), false);
    // If struct is open, more fields might appear and cannot do a resolve.    
    if( str.is_open() ) {
      str.deps_add(this);
      return false;
    }
    if( trial_resolve(true, tvar(), str, test) )
      return true;              // Resolve succeeded!
    // No progress, try again if self changes
    if( !test ) tvar().deps_add_deep(this);
    return false;
  }


  
  // Build a sane error message for a failed resolve.
  //   @{x=7}.y            Unknown field '.y' in @{x= int8}          - LHS   known, no  clazz, field not found in instance, instance yes struct
  //   "abc".y             Unknown field '.y' in "abc"               - LHS   known, yes clazz, field not found in either  , not pinned, report instance
  //   "abc"&1             Unknown operator '_&_' in str:            - LHS   known, yes clazz, field not found in either  , yes pinned, report clazz
  //   { x -> x+1 }        Unable to resolve operator '_+_' "        - LHS unknown, no  clazz but pinned field
  //   { x -> 1+x }                                                  - LHS   known, yes clazz, ambiguous, report choices and match
  //                       Ambiguous, matching choices ({ int:int64 int:int64 -> int:int64 }, { int:int64 flt:nflt64 -> flt:flt64 }) vs { int:1 A -> B }
  //   ( { x -> x*2 }, { x -> x*3 })._ 4                             - LHS   known, no  clazz, ambiguous, report choices and match
  //                       Ambiguous, matching choices ({ A B -> C }, { D E -> F }) vs { G int:4 -> H }

  private String resolve_failed_msg() {
    String fld = null;          // Overloaded field name
    // If overloaded field lookup, reference field name in message
    if( is_resolving() ) {
      if( in(0) instanceof LoadNode xfld )
        fld = xfld._fld;        // Overloaded field name
    } else fld = _fld;
    if( fld==null ) return "";
    return (Oper.is_oper(fld) ? " operator '" : " field '.") + fld + "'";
    //boolean oper = fld!=null && Oper.is_oper(fld); // Is an operator?
    //if( oper && !_clz ) {
    //  String clz = FieldNode.clz_str(fldn.val(0));
    //  if( clz!=null ) fld = clz+fld; // Attempt to be clazz specific operator
    //}
    //TVStruct tvs = match_tvar() instanceof TVStruct ts ? ts : null;
    //String err, post;
    //if( !is_resolving() ) { err = "Unknown"; post=" in %: "; }
    //else if( tvs!=null && ambi(tvar(),tvs) ) { err = "Ambiguous, matching choices %"; post = " vs "; }
    //else if( unable(tvs) ) { err = "Unable to resolve"; post=": "; }
    //else { err = "No choice % resolves"; post=": "; }
    //if( fld!=null )
    //  err += (oper ? " operator '" : " field '.")+fld+"'";
    //err += post;
    //return err;
  }


  // No matches to pattern (no YESes, no MAYBEs).  Empty patterns might have no NOs.
  public boolean resolve_failed_no_match() {
    String err = "No choice % resolves"+resolve_failed_msg()+": ";
    TV3 pattern = tvar();
    TV3 tv0 = tvar(0);
    assert tv0.as_struct().idx(_fld)==-1;             // No resolving field on RHS?  TODO: Delete & progress
    return tv0.unify_err(err,pattern,_bad,false);
  }


  @Override public TV3 match_tvar() { return tvar(0); }

  // clones during inlining change resolvable field names
  @Override public LoadNode copy(boolean copy_edges) {
    LoadNode nnn = (LoadNode)super.copy(copy_edges);
    if( nnn.is_resolving() ) nnn._fld = nnn.resolve_fld_name("_");
    Env.GVN.add_flow(this);     // Alias changes flow
    return nnn;
  }

  @Override public int hashCode() { return super.hashCode()+_fld.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof LoadNode fld) ) return false;
    return Util.eq(_fld,fld._fld);
  }

}
