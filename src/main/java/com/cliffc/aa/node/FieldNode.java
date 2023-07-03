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
  // Where to report errors
  public final Parse _bad;

  public FieldNode(Node struct, String fld, Parse bad) {
    super(OP_FIELD,struct);
    // A plain "_" field is a resolving field
    _fld = resolve_fld_name(fld);
    _bad = bad;
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
      return TypeNil.EXTERNAL;
    }

    // Field from Base looks in the base CLZ.
    // One of TypeInt, TypeFlt, NIL or XNIL
    Type tstr = t;
    if( t instanceof TypeNil && !(t instanceof TypeStruct) ) {
      throw unimpl();
    }
    // Hit on a field
    if( tstr instanceof TypeStruct ts ) {
      if( ts.find(_fld)!= -1 ) return ts.at(_fld);
      // Miss on closed structs looks at superclass.
      // Miss on open structs dunno if the field will yet appear
      if( ts.len()>=1 && Util.eq(ts.fld(0)._fld,TypeFld.CLZ) )
        throw unimpl();
      return ts._def;
    }
    return tstr.oob(Type.ALL);
  }

  private static Type meet(TypeStruct ts) {
    if( ts.len()==0 ) return ts._def;
    Type t = Type.ANY; for( TypeFld t2 : ts )  t = t.meet(t2._t); return t;
  }
  private static Type join(TypeStruct ts) {
    if( ts.len()==0 ) return ts._def;
    Type t = Type.ALL;
    for( TypeFld t2 : ts )
      t = t.join( t2._t instanceof TypeFunPtr tfp2  ? tfp2.make_from(tfp2.fidxs().dual()) : t2._t );
    return t;
  }

  // If the field is resolving, we do not know which field to demand, so demand
  // them all when lifting and none when lowering.
  @Override public Type live_use( int i ) {
    if( is_resolving() ) {
      if( Combo.pre() || Combo.post() || Combo.HM_AMBI )
        return TypeStruct.ISUSED; // Not sure which one, so pick all
      // Still might resolve, and therefore keep alive only the resolved field.
      deps_add(in(i));
      return TypeStruct.UNUSED;
    }
    // Otherwise normal fields and clazz fields are field-alive.
    return TypeStruct.UNUSED.replace_fld(TypeFld.make(_fld,Type.ALL));
  }

  @Override public Node ideal_reduce() {
    // Field from a Bind of a Struct (overload)
    if( in(0) instanceof BindFPNode bind && bind._val instanceof TypeStruct && bind._uses._len==1 ) {
      assert bind._over;
      Node fp = new FieldNode(bind.fp(),_fld,_bad).init();
      return new BindFPNode(fp,bind.dsp(),false).init();
    }

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
          lphi.add_def(Env.GVN.add_work_new(new FieldNode(phi.in(i),_fld,_bad)));
        return lphi;
      }
    }

    return null;
  }

  @Override public boolean has_tvar() { return true; }

  @Override public TV3 _set_tvar() {
    TVLeaf self = new TVLeaf();
    _tvar = self;               // Stop cycles
    // Force input to be a struct
    TV3 t0 = in(0).set_tvar();
    TVStruct ts;
    if( t0 instanceof TVStruct ts0 ) ts = ts0;
    else t0.unify(ts=new TVStruct(true),false);
    // If resolving, force insert
    if( is_resolving() )
      TVField.FIELDS.put(_fld,this); // Track resolving field names
    return _tvar;
  }

  @Override public boolean unify( boolean test ) {
    TVStruct tstr = tvar(0).as_struct();  TV3 fld;
    // Attempt resolve
    if( is_resolving() )
      return try_resolve(tstr,test);
    // Search up the super-clazz chain
    for( ; tstr!=null; tstr = tstr.clz() ) {
      // If the field is in the struct, unify and done
      if( (fld=tstr.arg(_fld))!=null ) return do_fld(fld,test);
      // If the struct is open, add field here and done.
      // Field is not pinned, because it might belong in a superclazz
      if( tstr.is_open() ) return tstr.add_fld(_fld,tvar(),false);
    }

    // struct is end-of-super-chain, miss_field
    return tvar().unify_err(resolve_failed_msg(),tvar(0),null,test);
  }

  private boolean do_fld( TV3 fld, boolean test ) {
    if( tvar() instanceof TVLeaf leaf ) leaf.set_no_progress();
    return tvar().unify(fld,test);
  }


  public static String clz_str(Type t) {
    return switch( t ) {
    case TypeInt ti -> "int:";
    case TypeFlt tf -> "flt:";
    case TypeMemPtr tmp -> { throw unimpl(); } // Fetch from tmp._obj._flds[0]?
    case TypeNil tn -> tn==TypeNil.NIL || tn==TypeNil.XNIL ? "int:" : null;
    default -> null;
    };
  }

  // Prototype or null
  static StructNode clz_node(Type t) {
    String clz = clz_str(t);
    return clz==null ? null : Env.PROTOS.get(clz);  // CLZ from instance
  }

  private boolean try_resolve( TVStruct str, boolean test ) {
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

  @Override public ErrMsg err( boolean fast ) {
    TV3 tv = tvar();
    if( !(tv instanceof TVErr tverr) ) return null;
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

  private String resolve_failed_msg() {
    String fld = null;          // Overloaded field name
    // If overloaded field lookup, reference field name in message
    if( is_resolving() ) {
      if( in(0) instanceof FieldNode xfld )
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

  public boolean resolve_ambiguous_msg() {
    TV3 pattern = tvar();
    TVStruct rhs = tvar(0).as_struct();
    assert rhs.idx(_fld)==-1;   // No resolving field on RHS?
    boolean progress=false;
    // TODO: I tried fresh_unify the pattern against each valid choice.
    // TODO: throws too many false positives?
    //for( int i=0; i<rhs.len(); i++ ) {
    //  TV3 rhsx = rhs.arg(i);
    //  if( pattern.trial_unify_ok( rhsx ) >= 0 ) {
    //    progress |= pattern.fresh_unify(null,rhsx,null,false);
    //  }
    //}
    return tvar(0).unify_err("Ambiguous, matching choices % vs ",pattern,_bad,false) | progress;
  }

  // True if ambiguous (more than one match), false if no matches.
  private boolean ambi(TV3 self, TVStruct tvs) {
    for( int i=0; i<tvs.len(); i++ )
      if( !Resolvable.is_resolving(tvs.fld(i)) )
        //
        //  self.trial_unify_ok(tvs.arg(i)) )
        //return true;
        throw unimpl();
    return false;
  }
  private static boolean unable( TVStruct tvs ) {
    if( tvs==null ) return true;
    for( int i=0; i<tvs.len(); i++ )
      if( !Resolvable.is_resolving(tvs.fld(i)) )
        return false;
    return true;
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
