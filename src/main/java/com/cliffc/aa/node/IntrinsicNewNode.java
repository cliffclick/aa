package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

import java.util.HashMap;

// Known (intrinsic) library calls.  They typically have memory side effects,
// or else they would be a PrimNode instead.  Like PrimNodes they are wrapped
// in a Fun/Epilog but include memory effects.
//
// These intrinsics take in memory of their alias# (same as a NewNode) and
// update it (like a Store would) producing a new instance of the same alias#.
// They also take in other arguments, and typically use them to define the
// contents of memory.  They output a TypeTuple[ctrl,mem,val] same as a
// CallNode, although the [ctrl] is always true and ignored.
//
// The function wrapping these takes in all memory (like all functions do) and
// split out just the alias in question, and remerge with all memory before the
// epilog.
public abstract class IntrinsicNewNode extends IntrinsicNode {
  int _alias;                   // Alias class for new memory
  TypeMemPtr _ptr;              // private cache of the alias pointer
  IntrinsicNewNode( String name, String[] args, TypeTuple targs, Type funret, int alias ) {
    super(name,args,targs,funret);
    update_alias(alias);
  }
  private IntrinsicNewNode update_alias(int alias) {
    _alias = alias;
    _ptr = TypeMemPtr.make(alias);
    _all_type = TypeTuple.make(Type.CTRL,TypeMem.make(alias,TypeStr.STR),_ptr);
    return this;
  }
  public static IntrinsicNewNode[] INTRINSICS = new IntrinsicNewNode[] {
    new ConvertI64Str(BitsAlias.I64),
    new ConvertF64Str(BitsAlias.F64)
  };
  // Clones during inlining all become unique new sites
  @Override IntrinsicNewNode copy(GVNGCM gvn) {
    IntrinsicNewNode nnn = (IntrinsicNewNode)super.copy(gvn);
    return nnn.update_alias(BitsAlias.new_alias(_alias,TypeStr.STR)); // Children alias classes
  }
  @Override public String xstr() { return _name+"_#"+_alias; }
  // --------------------------------------------------------------------------
  static class ConvertI64Str extends IntrinsicNewNode {
    ConvertI64Str(int alias) { super("str",ARGS1,TypeTuple.INT64, TypeMemPtr.STRPTR,alias); }

    // Conversion to String allocates memory - so the apply() call returns a new
    // pointer aliased to a hidden String allocation site.  The memory returned
    // is read-only (and can be shared).
    @Override public Type value(GVNGCM gvn) {
      
      // If the meet with _targs.dual stays above center for all inputs, then we
      // return _ptr.dual, the highest allowed result; if all inputs are
      // constants we constant fold; else some input is low so we return _ptr,
      // the lowest possible result.
      Type mem = gvn.type(in(1));
      if( !(mem instanceof TypeMem) ) return mem.above_center() ? _all_type.dual() : _all_type;
      Type val = gvn.type(in(2));
      Type t = TypeInt.INT64.dual().meet(val);
      if( t.above_center() ) return _all_type.dual();
      if( !t.is_con() )      return _all_type;
      
      // Conversion to String allocates memory - so return a new pointer
      // aliased to a hidden String allocation site.  The memory returned is
      // read-only (and can be shared).
      TypeObj obj = ((TypeMem)mem).at(_alias);  // Prior memory contents at this alias
      TypeObj obj2= (TypeObj)obj.join(TypeStr.STR); // Expect memory at least correct, or else type error was feed in
      TypeStr str = TypeStr.con(Long.toString(val.getl()));
      TypeObj obj3 = (TypeObj)obj2.meet(str);
      TypeMem res = TypeMem.make(_alias,obj3);
      return TypeTuple.make(Type.CTRL,res,_ptr);
    }
  }
  
  static class ConvertF64Str extends IntrinsicNewNode {
    ConvertF64Str(int alias) { super("str",ARGS1,TypeTuple.FLT64, TypeMemPtr.STRPTR, alias); }
            
    // Conversion to String allocates memory - so the apply() call returns a new
    // pointer aliased to a hidden String allocation site.  The memory returned
    // is read-only (and can be shared).
    @Override public Type value(GVNGCM gvn) {
      // If the meet with _targs.dual stays above center for all inputs, then we
      // return _ptr.dual, the highest allowed result; if all inputs are
      // constants we constant fold; else some input is low so we return _ptr,
      // the lowest possible result.
      Type mem = gvn.type(in(1));
      if( !(mem instanceof TypeMem) ) return mem.above_center() ? _all_type.dual() : _all_type;
      Type val = gvn.type(in(2));
      Type t = TypeFlt.FLT64.dual().meet(val);
      if( t.above_center() ) return _all_type.dual();
      if( !t.is_con() )      return _all_type;
      
      // Conversion to String allocates memory - so return a new pointer
      // aliased to a hidden String allocation site.  The memory returned is
      // read-only (and can be shared).
      TypeObj obj = ((TypeMem)mem).at(_alias);  // Prior memory contents at this alias
      TypeObj obj2= (TypeObj)obj.join(TypeStr.STR); // Expect memory at least correct, or else type error was feed in
      TypeStr str = TypeStr.con(Double.toString(val.getd()));
      TypeObj obj3 = (TypeObj)obj2.meet(str);
      TypeMem res = TypeMem.make(_alias,obj3);
      return TypeTuple.make(Type.CTRL,res,_ptr);
    }
  }
}
