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
  // TRUE:  Field lookup is strictly in the clazz and not locally.
  // FALSE: Can be either/unknown
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
    //if( _clz && def==in(0) ) return TypeStruct.ISUSED;
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
    // Force CLZ:[@{...},@{...}].    
    // Under SOME situations but not ALL, we can tell were to put the field
    // (either CLZ or instance struct).  Since we sometimes need to wait, we
    // put that logic in the unify call.

    // Next New Think:
    // - must jam the unify-able type in, without a proper field name.
    // - so bring back the "&123" field names.
    // - if not flagged clz/instance and both are open, still dunno where to go
    // - can temp put it in e.g. rhs, and claim it floats until resolved
    // - or gets a clz/inst user.
    // - opers alreayd flagged as clz
    // 
    
    in(0).set_tvar().unify( new TVClz(new TVStruct(true),new TVStruct(true)), false);
    return new TVLeaf();
  }

  @Override public boolean unify( boolean test ) {
    TVClz clz = tvar(0).as_clz();  TV3 fld;
    // Where is the field?
    // RHS  - if !_clz && resolving
    if( is_resolving() ) return do_resolve(clz,test);
    // OR   - if  found in one or other
    if( (fld=clz.clz().arg(_fld))!=null ) return do_clz(fld,clz,test);
    if( (fld=clz.rhs().arg(_fld))!=null ) return do_rhs(fld,clz,test);
    // CLZ  - If  _clz
    if( _clz )
      return clz.clz().is_open() ? add_clz(clz,test) : do_miss(clz,test);
    // STALL- if !found in either and both are open
    // CLZ  - Only CLZ is open so must be there
    if( clz.clz().is_open() )
      return clz.rhs().is_open() ? false : add_clz(clz,test);
    // RHS  - Only RHS is open so must be there
    // MISS - if !found in either and both are closed
    return clz.rhs().is_open() ? add_rhs(test) : do_miss(clz,test);
  }    

  private boolean do_clz( TV3 fld, TVClz clz, boolean test ) {
    assert clz.rhs().arg(_fld)==null;
    return tvar().unify(fld,test);
  }
  private boolean do_rhs( TV3 fld, TVClz clz, boolean test ) {
    assert !_clz && clz.clz().arg(_fld)==null;
    return tvar().unify(fld,test);
  }
  private boolean add_clz( TVClz clz, boolean test ) {
    assert clz.rhs().arg(_fld)==null;
    return test || clz.clz().add_fld(_fld,tvar());
  }
  private boolean add_rhs( boolean test ) {
    throw unimpl();
  }
  private boolean do_resolve( TVClz clz, boolean test ) {
    assert !_clz;
    if( Combo.HM_AMBI ) return false; // Failed earlier, can never resolve
    boolean progress = try_resolve(clz.rhs(),test);
    if( is_resolving() || test ) return progress; // Failed to resolve, or resolved but testing
    // Known to be resolved and in RHS
    do_rhs(clz.rhs().arg(_fld),clz,test);
    return true;                // Progress
  }
  private boolean do_miss(TVClz clz, boolean test) {
    return tvar().unify_err(resolve_failed_msg(),clz,test);
  }


  public static String clz_str(Type t) {
    return switch( t ) {
    case TypeInt ti -> "int:";
    case TypeFlt tf -> "flt:";
    case TypeMemPtr tmp -> { throw unimpl(); } // Fetch from tmp._obj._flds[0]?
    case TypeStruct ts -> { throw unimpl(); } // Fetch from _flds[0]?
    case TypeNil tn -> tn==TypeNil.NIL || tn==TypeNil.XNIL ? "int:" : null;
    default -> null;
    };
  }

  // Prototype or null
  static StructNode clz_node(Type t) {
    String clz = clz_str(t);
    return clz==null ? null : Env.PROTOS.get(clz);  // CLZ from instance
  }

  private static TV3 CLZ;
  boolean clz_lookup( boolean test ) {
    StructNode proto = clz_node(val(0)); // Existing prototypes for int/flt/named-clazz-types
    if( proto!=null )                    // Known clazz
      { CLZ = proto.tvar(); return false; }

    // Unknown inferred clazz
    if( test ) return true;        // Always progress
    //TVStruct obj = new TVStruct(new String[]{_fld}, new boolean[]{true}, new TV3[]{tvar()}, true);
    //CLZ = new TVClz(obj, new TVLeaf());
    //tvar(0).unify(CLZ, test);
    //return true;
    throw unimpl();
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
    TVStruct tvs = match_tvar() instanceof TVClz tv0 ? tv0.rhs() : null;
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
