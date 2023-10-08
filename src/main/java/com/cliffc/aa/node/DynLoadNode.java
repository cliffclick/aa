package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.Util;

import static com.cliffc.aa.AA.*;

// Load a struct from memory.  Does its own nil-check testing.  Display/Frames
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

public class DynLoadNode extends Node implements Resolvable {

  private String _fld;
  // Resolved fields
  private final Ary<Resolved> _resolveds;
  
  // Where to report errors
  private final Parse _bad;
  
  public DynLoadNode( Node mem, Node adr, Parse bad ) {
    super(OP_DYNLD,null,mem,adr);
    _bad = bad;
    _fld = "&"+_uid;
    _resolveds = new Ary<>(Resolved.class);
  }

  @Override public String xstr() { return "."+_fld; }   // Self short name
  String  str() { return xstr(); } // Inline short name
  
  Node mem() { return in(MEM_IDX); }
  Node adr() { return in(DSP_IDX); }

  @Override public String fld() { return _fld; }
  @Override public String resolve(String lab) {
    unelock();                  // Hash changes
    String old = _fld;
    _fld = lab;
    add_flow();
    return old;
  }
  @Override public String match(TVStruct rhs) {
    for( Resolved r : _resolveds )
      if( r.rhs()==rhs )
        return r._label;
    return null;
  }
  @Override public void record_match(TVStruct rhs, String lab) {
    Resolved r = new Resolved(rhs,lab);
    // Assert no dups on entry
    for( Resolved r2 : _resolveds )
      throw AA.unimpl();
    _resolveds.push(r);
  }

  
  @Override public boolean is_resolving() {
    return true;
  }
  
  @Override public Type value() {
    Type tadr = adr()._val;
    Type tmem = mem()._val;

    if( !(tadr instanceof TypeNil ta) || (tadr instanceof TypeFunPtr) )
      return tadr.oob(); // Not an address
    if( !(tmem instanceof TypeMem tm) )
      return tmem.oob(); // Not a memory
    if( ta==TypeNil.NIL || ta==TypeNil.XNIL )
      ta = (TypeNil)ta.meet(PrimNode.PINT._val);
    
    // Still resolving, dunno which field yet
    if( !Combo.HM_AMBI )
      return TypeNil.XSCALAR.oob(AA.LIFTING);

    // Set of fields being picked over
    TypeStruct ts = ta instanceof TypeMemPtr tmp && !tmp.is_simple_ptr()
      ? tmp._obj
      : tm.ld(ta);

    // Meet over all possible choices
    Type t = TypeNil.XSCALAR;
    for( Resolved r : _resolveds )
      t = t.meet(LoadNode.lookup(ts,ta,tm,r._label));
    if( t!=null ) return t;

    // Did not find field
    return Env.ROOT.ext_scalar(this);
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
      return RootNode.def_mem(def);
  
    if( ptr._aliases.is_empty() )  return Type.ANY; // Nothing is demanded still

    // Demand memory produce the desired field from a struct
    if( ptr._aliases==BitsAlias.NALL )
      return RootNode.def_mem(def);
    // All fields are live
    return TypeMem.make(ptr._aliases,TypeStruct.ISUSED);
  }

  @Override public boolean has_tvar() { return true; }
  @Override public TV3 _set_tvar() {
    TVField.FIELDS.put(_fld,this); // Track resolving field names which are DynLoad node ids

    // Load takes a pointer
    TV3 ptr0 = adr().set_tvar();
    TVPtr ptr;
    if( ptr0 instanceof TVPtr ptr1 ) ptr = ptr1;
    else ptr0.unify(ptr = new TVPtr(BitsAlias.EMPTY, new TVStruct(true) ),false);

    // Struct needs to have the named field
    TVStruct str = ptr.load();
    TV3 fld = str.arg(_fld), self;
    if( fld==null ) str.add_fld(_fld,self=new TVLeaf(),false);
    else            self = fld;
    return self;
  }

  // All field loads against a pointer.
  @Override public boolean unify( boolean test ) {
    TV3 ptr0 = adr().tvar();
    Type ta = adr()._val;

    // See if we force the input to choose between ptr and struct.
    // Get a struct in the end
    if( ptr0 instanceof TVErr ) throw unimpl();
    TVPtr ptr = ptr0.as_ptr();
    TVStruct str = ptr.load();

    // If struct is open, more fields might appear and cannot do a resolve.    
    if( str.is_open() ) {
      str.deps_add(this);
      return false;
    }
    if( match(str) != null )
      return false;             // Already matched

    if( trial_resolve(true, tvar(), str, test) )
      return true;              // Resolve made progress!
    // No progress, try again if self changes
    if( !test ) tvar().deps_add_deep(this);
    return false;
  }


  // A mapping from TVStruct pattern to the field that matches 'this._tvar'.
  // TVStructs can unify, so a normal HashMap doesn't work.
  private static class Resolved {
    TVStruct _rhs;
    final String _label;
    Resolved(TVStruct rhs, String lab) {
      assert !rhs.unified();
      _rhs=rhs;
      _label=lab;
    }
    @Override public String toString() { return "["+_label+": "+_rhs+"]"; }

    TVStruct rhs() {
      TVStruct rhs = (TVStruct)_rhs.find();
      if( rhs == _rhs ) return rhs;
      // Since RHS rolled up, might need to check for dups in match
      throw AA.unimpl();
    }
  }

  
  @Override public void resolve_or_fail() {
    //// Go ahead and resolve a field using only 1 choice.
    //if( _flds.size()== 1 ) {
    //  unelock();                // Hash changes since label changes
    //  _fld = _flds.iterator().next();
    //}
    //// No error if there are many choices, but requires a dynamic field lookup
    //add_flow();
    //in(1).add_flow(); // Liveness sharpens to specific field
    throw unimpl();
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
    throw unimpl();
    //// If overloaded field lookup, reference field name in message
    //if( is_resolving() ) {
    //  if( adr() instanceof LoadNode xfld )
    //    fld = xfld._fld;        // Overloaded field name
    //} else fld = _fld;
    //if( fld==null ) return "";
    //return (Oper.is_oper(fld) ? " operator '" : " field '.") + fld + "'";

    
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

  @Override public ErrMsg err( boolean fast ) {
    //if( is_resolving() ) {
    //  String fld = adr() instanceof LoadNode xfld ? xfld._fld : _fld;
    //  return ErrMsg.field(_bad,"Unresolved field loading",fld,false,null);
    //}
    return null;
  }
  
  // No matches to pattern (no YESes, no MAYBEs).  Empty patterns might have no NOs.
  public boolean resolve_failed_no_match( TV3 pattern, TVStruct rhs, boolean test ) {
    String err = "No choice % resolves"+resolve_failed_msg()+": ";
    boolean old = rhs.del_fld(_fld);
    assert old;                 // Expecting to remove pattern
    return pattern.unify_err(err,rhs,_bad,false);
  }


  //@Override public TV3 match_tvar() { return tvar(0); }

  // clones during inlining change resolvable field names
  @Override public DynLoadNode copy(boolean copy_edges) {
    DynLoadNode nnn = (DynLoadNode)super.copy(copy_edges);
    nnn._fld = "&"+nnn._uid;
    Env.GVN.add_flow(this);     // Alias changes flow
    return nnn;
  }

  @Override public int hashCode() { return super.hashCode()+_fld.hashCode(); }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof DynLoadNode fld) ) return false;
    return Util.eq(_fld,fld._fld);
  }

}
