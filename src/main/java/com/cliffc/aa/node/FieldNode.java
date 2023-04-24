package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.Util;
import org.jetbrains.annotations.NotNull;

import static com.cliffc.aa.AA.unimpl;

// Takes a static field name, a TypeStruct and returns the field value.
// Basically a ProjNode except it does lookups by field name in TypeStruct
// instead of by index in TypeTuple.
//
// Fields with a fixed name either lookup in the incoming self record or in the
// prototype, based on a Parser flag.
//
// Fields with the "_" name resolve locally only via H-M matching to one choice
// field.  Once resolved the Field name changes to match.

public class FieldNode extends Node implements Resolvable {
  
  // Field being loaded from a TypeStruct.  If "_", the field name is inferred
  // from amongst the field choices.  If not present, then error.
  public       String _fld;
  // Field lookup is strictly in the clazz and not locally.
  public final boolean _clz;
  // Where to report errors
  public final Parse _bad;

  public FieldNode(Node struct, String fld, boolean clz, Parse bad) {
    super(OP_FIELD,struct);
    // A plain "_" field is a resolving field
    _fld = resolve_fld_name(fld);
    _bad = bad;
    _clz = clz;
    assert !(clz && is_resolving()); // One or the other for now
  }
  // A plain "_" field is a resolving field
  private String resolve_fld_name(String fld) { return Util.eq(fld,"_") ? ("&"+_uid).intern() : fld; }
  @Override public String xstr() { return "."+(is_resolving() ? "_" : _fld); }   // Self short name
  String  str() { return xstr(); } // Inline short name
  @Override public boolean is_resolving() { return Resolvable.is_resolving(_fld); }
  @Override public String fld() { assert !is_resolving(); return _fld; }
  // Set the resolved field label
  @Override public String resolve(String label) {
    unelock();                  // Hash changes since label changes
    String old = _fld;
    _fld = label;
    add_flow();
    in(0).add_flow(); // Liveness sharpens to specific field
    return old;
  }
  
  @Override public TV3 match_tvar() { return tvar(0); }
  
  @Override public Type value() {
    Type t = val(0);
    if( t==Type.ANY || t==Type.ALL ) return t;
    // Here down, always return +/- SCALAR not ANY/ALL
    if( is_resolving() ) {
      // Pre-HMT, dunno which one, use meet.
      // Still resolving, use the join of all fields.
      boolean lo = _tvar==null || Combo.HM_AMBI;
      if( t instanceof TypeStruct ts )
        return lo ? meet(ts) : join(ts);
      return t.oob(TypeNil.SCALAR);
    }

    // Clazz or local struct ?
    Type tstr = null;
    if( _clz ) {
      StructNode clazz = clz_node(t);
      if( clazz !=null ) {
        tstr = clazz._val;      // Value from clazz
        // Add a dep edge to the clazz, so value changes propagate permanently
        if( len()==2 ) assert in(1)==clazz;
        else add_def(clazz);
      } // Else clazz not defined, no clazz, no struct to field from
    } else {
      tstr = t;                 // Value direct from input
    }
    // Hit on a field
    if( tstr instanceof TypeStruct ts && ts.find(_fld)!= -1 )
      return ts.at(_fld).join(TypeNil.SCALAR).meet(TypeNil.XSCALAR);
    return (tstr==null ? t : tstr).oob(TypeNil.SCALAR);
  }

  private static Type meet(TypeStruct ts) { Type t = TypeNil.XSCALAR; for( TypeFld t2 : ts )  t = t.meet(t2._t); return t; }
  private static Type join(TypeStruct ts) {
    Type t = TypeNil.SCALAR;
    for( TypeFld t2 : ts )
      t = t.join( t2._t instanceof TypeFunPtr tfp2  ? tfp2.make_from(tfp2.fidxs().dual()) : t2._t );
    return t.meet(TypeNil.XSCALAR);
  }

  // If the field is resolving, we do not know which field to demand, so demand
  // them all when lifting and none when lowering.  
  @Override public Type live_use( Node def ) {
    if( is_resolving() ) {
      if( Combo.pre() || Combo.post() | Combo.HM_AMBI )
        return TypeStruct.ISUSED; // Not sure which one, so pick all
      // Still might resolve, and therefore keep alive only the resolved field.
      deps_add(def);
      return TypeStruct.UNUSED;
    }
    // Clazz load, the instance is normal-live
    if( _clz && def==in(0) ) return TypeStruct.ISUSED;
    // Otherwise normal fields and clazz fields are field-alive.
    return TypeStruct.UNUSED.replace_fld(TypeFld.make(_fld,Type.ALL));
  }

  @Override public Node ideal_reduce() {
    if( is_resolving() ) return null;
    
    // Back-to-back SetField/Field
    if( in(0) instanceof SetFieldNode sfn ) {
      if( sfn.err(true)==null ) {
        if( Util.eq(_fld, sfn._fld) ) {
          if( sfn.val(1).isa(_val) ) return sfn.in(1); // Same field, use same
          else sfn.in(1).deps_add(this);
        } else {
          return Env.GVN.add_reduce(set_def(0, sfn.in(0))); // Unrelated field, bypass
        }
      } else {
        // Depends on sfn.err which depends on sfn.in(0)
        sfn.in(0).deps_add(this);
      }
    }

    // Back-to-back CLZ-Struct/Field
    StructNode str = in(0) instanceof StructNode str0 ? str0 : clz_node(val(0));
    // Back-to-back Struct/Field
    if( str!=null && str.err(true)==null ) {
      int idx = str.find(_fld);
      if( idx >= 0 ) {
        if( str.val(idx).isa(_val) ) return str.in(idx);
        else str.deps_add(this); // Revisit if input changes
      }
    } else {
      in(0).deps_add(this); // Revisit if input changes
    }

    // Field from a Bind of a Struct (overload)
    if( _live==Type.ALL && in(0) instanceof BindFPNode bind && bind.fp() instanceof StructNode sn ) {
      assert bind._over;
      Node fp = new FieldNode(sn,_fld,_clz,_bad).init();
      return new BindFPNode(fp,bind.dsp(),false).init();
    }
    
    return null;
  }
  
    
  @Override public Node ideal_grow() {
    // Load from a memory Phi; split through in an effort to sharpen the memory.
    // TODO: Only split thru function args if no unknown_callers, and must make a Parm not a Phi
    // TODO: Hoist out of loops.
    if( in(0) instanceof PhiNode phi ) {
      int fcnt=0;
      for( int i=1; i<phi.len(); i++ )
        if( phi.in(i)._op == OP_SETFLD || phi.in(i)._op == OP_BINDFP ) fcnt++;
      if( fcnt>0 ) {
        Node lphi = new PhiNode(TypeNil.SCALAR,phi._badgc,phi.in(0));
        for( int i=1; i<phi.len(); i++ )
          lphi.add_def(Env.GVN.add_work_new(new FieldNode(phi.in(i),_fld,_clz,_bad)));
        return lphi;
      }
    }

    return null;
  }

  @Override public boolean has_tvar() { return true; }
  
  @Override public TV3 _set_tvar() {
    if( is_resolving() )
      TVField.FIELDS.put(_fld,this); // Track resolving field names
    return new TVLeaf();
  }

  @Override public boolean unify( boolean test ) {
    boolean progress = false;

    TV3 tv0 = tvar(0);          // If an instance field, need the input struct
    // Clazz fields do clazz lookups, expect clazz structures.
    // - if a TVClz, we got the clz
    // - if a TVLeaf, try a prototype lookup from the flow type; if that works use the prototype
    //                else unify to a pending clz
    // - if a TVNil , try a prototype lookup from the flow type; if that works use the prototype
    //                else stall
    // - if a TVErr , try a clz (repeat above), or a nil (repeat), or a leaf
    //
    // Else do an instance lookup
    // - if a TVStruct, use it
    // - if a TVErr   , get the struct
    // - else unify with TVStruct (handles Leafs, or forces TVErr with Struct)
    //
    // With struct in-hand, proceed to resolve & do lookup
    if( _clz ) {
      switch( tv0 ) {
      case TVClz clz -> tv0 = clz.clz(); // Clazz part from a clazzed TV
      case TVLeaf leaf -> {              // Expand to a clazzed TV
        StructNode proto = clz_node(val(0)); // Existing prototypes for int/flt/named-clazz-types
        if( proto == null ) {            // Unknown inferred clazz
          if( test ) return true;        // Always progress
          progress = true;
          TVStruct obj = new TVStruct(new String[]{_fld}, new boolean[]{true}, new TV3[]{tvar()}, true);
          TVClz clz = new TVClz(obj, new TVLeaf());
          tv0.unify(clz, test);
          tv0 = clz.clz();
        } else {
          tv0 = proto.tvar();
        }
      }
      case TVNil nil -> {                    // Expand to a clazzed TV
        StructNode proto = clz_node(val(0)); // Existing prototypes for int/flt/named-clazz-types
        if( proto == null ) return false;    // Unknown inferred clazz, stall until we get something better
        tv0 = proto.tvar();
      }
      case TVErr err -> {
        if( err.as_clz()!=null ) tv0 = err.as_clz().clz(); // Try a CLZ
        else if( err.as_nil()!= null ) throw unimpl();     // Try the NIL (repeat clz_node lookup)
        else {
          if( test ) return true;
          // Treat as Leaf; make a Clz, unify and use it
          TVLeaf lclz = err.make_clz();
          progress |= lclz.unify(new TVClz(new TVStruct(new String[0],new TV3[0],true),tv0=new TVLeaf()),false);
        }
      }
      default -> throw unimpl();
      };
      
    } else {
      // ----------------------
      // Instance field lookup
      
      // Errors have a struct to unify against
      if( tv0 instanceof TVErr terr ) {
        tv0 = terr.as_clz();      // If TVErr has a Clz, take it, fetch RHS
        if( tv0==null ) {         // No CLZ
          tv0 = terr.as_struct(); // If TVErr has a Struct, take it
          if( tv0 == null )       // Force struct under error
            tv0 = terr.make_struct();
        }
      }
      if( tv0 instanceof TVClz clz ) tv0 = clz.rhs();
    }

    // Still not a struct?  Make one, add field
    TVStruct str;
    if( tv0 instanceof TVStruct str0 ) str = str0;
    else {
      if( test ) return true;
      TVStruct inst = new TVStruct(new String[]{}, new TV3[]{}, true);
      if( !is_resolving() )
        inst.add_fld(_fld,Oper.is_oper(_fld),tvar());
      progress = tv0.unify(str=inst,test);
    }

    // If resolving, cannot do a field lookup.  Attempt resolve first.
    if( is_resolving() ) {
      if( Combo.HM_AMBI ) return false; // Failed earlier, can never resolve
      progress |= try_resolve(str,test);
      if( is_resolving() || test ) return progress;
      str = (TVStruct)str.find();
    }
    assert !is_resolving();

    // Look up field normally
    TV3 fld = str.arg(_fld);
    if( fld!=null )           // Unify against a pre-existing field
      return tvar().unify(fld, test) | progress;

    // If field is doing overload resolution, inject even if rec is closed
    if( is_resolving() ) {
      if( test ) return true;
      throw unimpl();
    }
    
    // If the field is resolved, and not in struct and not in proto and the
    // struct is closed, then the field is missing.
    if( !str.is_open() )
      return tvar().unify_err(resolve_failed_msg(),tvar(0),test);

    // Add the field, make progress
    if( !test ) str.add_fld(_fld,_clz,tvar());
    return true;
  }


  public static String clz_str(Type t) {
    return switch( t ) {
    case TypeInt ti -> "int:";
    case TypeFlt tf -> "flt:";
    case TypeMemPtr tmp -> { throw unimpl(); } // Fetch from tmp._obj._clz?
    case TypeStruct ts -> ts._clz;
    case TypeNil tn -> tn==TypeNil.NIL || tn==TypeNil.XNIL ? "int:" : null;
    default -> null;
    };
  }

  // Prototype or null
  static StructNode clz_node(Type t) {
    String clz = clz_str(t);
    return clz==null ? null : Env.PROTOS.get(clz);  // CLZ from instance
  }

  public static TVStruct clz_tv(Type t) {
    return (TVStruct)clz_node(t).tvar();
  }

  private static TV3 CLZ;
  boolean clz_lookup( boolean test ) {
    StructNode proto = clz_node(val(0)); // Existing prototypes for int/flt/named-clazz-types
    if( proto!=null )                    // Known clazz
      { CLZ = proto.tvar(); return false; }

    // Unknown inferred clazz
    if( test ) return true;        // Always progress
    TVStruct obj = new TVStruct(new String[]{_fld}, new boolean[]{true}, new TV3[]{tvar()}, true);
    CLZ = new TVClz(obj, new TVLeaf());
    tvar(0).unify(CLZ, test);
    return true;
  }

  
  private boolean try_resolve( TVStruct str, boolean test ) {
    // If struct is open, more fields might appear and cannot do a resolve.
    if( str.is_open() ) {
      str.deps_add(this);
      return false;
    }
    if( trial_resolve(true, tvar(), str, str, test) )
      return true;              // Resolve succeeded!
    // No progress, try again if self changes
    if( !test ) tvar().deps_add_deep(this);
    return false;
  }

  @Override public ErrMsg err( boolean fast ) {
    if( !(tvar() instanceof TVErr tverr) ) return null;
    Ary<String> errs = tverr._errs;
    if( errs==null ) return null; // Even if an error here, somebody else will report
    if( fast ) return ErrMsg.FAST;
    TV3 tv0 = tvar(0);
    if( tv0 instanceof TVLeaf )
      //return ErrMsg.unresolved(_bad,"Not a struct loading field "+_fld);
      throw unimpl();
    return new ErrMsg(_bad,tverr.p(),ErrMsg.Level.Field);
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
  public String resolve_failed_msg() {
    FieldNode fldn = this;
    String fld = null;          // Overloaded field name
    // If overloaded field lookup, reference field name in message
    if( is_resolving() ) {
      if( in(0) instanceof FieldNode xfld ) {
        fldn = xfld;            // Use parent field
        fld = fldn._fld;        // Overloaded field name
      }
    } else fld = _fld;
    boolean oper = fld!=null && Oper.is_oper(fld); // Is an operator?
    if( oper && !_clz ) {
      String clz = FieldNode.clz_str(fldn.val(0));
      if( clz!=null ) fld = clz+fld; // Attempt to be clazz specific operator
    }
    TVStruct tvs = match_tvar() instanceof TVStruct tv0 ? tv0 : null;
    String err, post;
    if( !is_resolving() ) { err = "Unknown"; post=" in %: "; }
    else if( tvs!=null && ambi(tvar(),tvs) ) { err = "Ambiguous, matching choices %"; post = " vs "; }
    else if( tvs==null || tvs.len()==0 ) { err = "Unable to resolve"; post=": "; }
    else { err = "No choice % resolves"; post=": "; }
    if( fld!=null )
      err += (oper ? " operator '" : " field '.")+fld+"'";
    err += post;
    return err;
  }
  
  // True if ambiguous (more than one match), false if no matches.
  private boolean ambi(TV3 self, TVStruct tvs) {
    for( int i=0; i<tvs.len(); i++ )
      if( !Resolvable.is_resolving(tvs.fld(i)) &&
          self.trial_unify_ok(tvs.arg(i),false) )
        return true;
    return false;
  }
  
  // clones during inlining change resolvable field names
  @Override public @NotNull FieldNode copy(boolean copy_edges) {
    FieldNode nnn = (FieldNode)super.copy(copy_edges);
    if( nnn.is_resolving() ) nnn._fld = nnn.resolve_fld_name("_");
    Env.GVN.add_flow(this);     // Alias changes flow
    return nnn;
  }

  @Override public int hashCode() { return super.hashCode()+_fld.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof FieldNode fld) ) return false;
    return Util.eq(_fld,fld._fld);
  }

}
