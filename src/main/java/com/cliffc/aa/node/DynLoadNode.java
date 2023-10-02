package com.cliffc.aa.node;

import com.cliffc.aa.*;
import com.cliffc.aa.tvar.*;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Util;

import static com.cliffc.aa.AA.*;
import java.util.HashSet;

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
  
  // Where to report errors
  private final Parse _bad;
  
  public DynLoadNode( Node mem, Node adr, Parse bad ) {
    super(OP_DYNLD,null,mem,adr);
    _bad = bad;
    _fld = "&"+_uid;
  }

  @Override public String xstr() { return "."+_fld; }   // Self short name
  String  str() { return xstr(); } // Inline short name
  
  Node mem() { return in(MEM_IDX); }
  Node adr() { return in(DSP_IDX); }
  private Node set_mem(Node a) { return set_def(MEM_IDX,a); }

  @Override public String fld() { return _fld; }
  @Override public String resolve(String lab) { throw AA.unimpl(); }
  @Override public boolean is_resolving() { return true; }
  
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
    if( ts.above_center() ) return TypeNil.XSCALAR;
    // TODO: include clz fields
    Type t2 = ts._def;
    if( Combo.pre() || Combo.HM_AMBI ) {
      for( TypeFld t3 : ts )  t2 = t2.meet(t3._t);
      t2 = t2.join(TypeNil. SCALAR);
    } else {
      for( TypeFld t3 : ts )  t2 = t2.join(t3._t);
      t2 = t2.meet(TypeNil.XSCALAR);
    }
    return t2;
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
    TVField.FIELDS.put(_fld,this); // Track resolving field names

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
    TV3 fld = str.arg(_fld);
    TV3 self = new TVLeaf();
    if( fld==null ) {
      str.add_fld(_fld,self,false);
    } else {
      self.unify(fld,false);
    }
    
    return self.find();
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

    // Attempt resolve
    // Put the resolving field in the struct; it will be present in the answer
    // in SOME field we just do not which one.
    if( str.idx(_fld) == -1 )
      str.add_fld(_fld, tvar(), false);
    // If struct is open, more fields might appear and cannot do a resolve.    
    if( str.is_open() ) {
      str.deps_add(this);
      return false;
    }
    if( trial_resolve(true, tvar(), str, test) )
      return true;              // Resolve made progress!
    // No progress, try again if self changes
    if( !test ) tvar().deps_add_deep(this);
    return false;
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


  @Override public TV3 match_tvar() { return tvar(0); }

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
