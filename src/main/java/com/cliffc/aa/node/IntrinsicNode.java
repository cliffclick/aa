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
public abstract class IntrinsicNode extends Node {
  final TypeTuple _targs;       // Argument types, 0-based, no memory.
  final Type _ret;              // Primitive return type, no memory
  public final String _name;    // Unique name (and program bits)
  final String[] _args;         // Handy; 0-based
  Parse _badargs;               // Filled in when inlined in CallNode
  int _alias;                   // Alias class for new memory
  IntrinsicNode( String name, String[] args, TypeTuple targs, Type ret, int alias ) {
    super(OP_LIBCALL);
    _name=name; _args=args; _targs = targs; _ret = ret;
    _badargs=null;
    _alias = alias;
  }

  private final static String[] ARGS1 = new String[]{"x"};
  
  public static IntrinsicNode[] INTRINSICS = new IntrinsicNode[] {
    new ConvertI64Str(BitsAlias.I64),
    new ConvertF64Str(BitsAlias.F64)
  };

  @Override public Type all_type() { return TypeTuple.CALL; }

  // Wrap the PrimNode with a Fun/Epilog wrapper that includes memory effects.
  public EpilogNode as_fun( GVNGCM gvn ) {
    FunNode  fun = ( FunNode) gvn.xform(new  FunNode(this,TypeMemPtr.make(_alias),TypeMem.make(_alias,TypeObj.OBJ)));
    ParmNode rpc = (ParmNode) gvn.xform(new ParmNode(-1,"rpc",fun,gvn.con(TypeRPC.ALL_CALL),null));
    ParmNode memp= (ParmNode) gvn.xform(new ParmNode(-2,"mem",fun,gvn.con(TypeMem.MEM     ),null));
    // Pre-split memory by alias
    Node split  = gvn.xform(new MemSplitNode(memp,_alias));
    Node memall = gvn.xform(new MProjNode(split,0));
    Node memali = gvn.xform(new MProjNode(split,_alias));
    // Add input edges to the intrinsic
    add_def(null);              // Control for the primitive in slot 0
    add_def(memali);            // Aliased Memory in slot 1
    for( int i=0; i<_args.length; i++ ) // Args follow
      add_def(gvn.xform(new ParmNode(i,_args[i],fun, gvn.con(_targs.at(i)),null)));
    Node prim = gvn.xform(this);
    Node mem2= gvn.xform(new MProjNode(prim,1));
    Node val = gvn.xform(new  ProjNode(prim,2));
    Node merge= gvn.xform(new MemMergeNode(memall,mem2));
    return new EpilogNode(fun,merge,val,rpc,fun,fun._fidx,null);
  }
  
  // Clones during inlining all become unique new sites
  @Override IntrinsicNode copy(GVNGCM gvn) {
    IntrinsicNode nnn = (IntrinsicNode)super.copy(gvn);
    nnn._alias = BitsAlias.new_alias(_alias); // Children alias classes
    return nnn;
  }
  @Override public String xstr() { return _name+"_#"+_alias; }
  @Override public Node ideal(GVNGCM gvn) { return null; }
  
  @Override public String err(GVNGCM gvn) {
    for( int i=0; i<_targs._ts.length; i++ ) {
      Type tactual = gvn.type(in(i+1));
      Type tformal = _targs._ts[i];
      if( !tactual.isa(tformal) )
        return _badargs==null ? "bad arguments" : _badargs.typerr(tactual,tformal);
    }
    return null;
  }

  // --------------------------------------------------------------------------
  public static IntrinsicNode convertTypeName( TypeObj from, TypeName to, Parse badargs ) {
    // Builds a function which takes in a TypeMemPtr.STRUCT and TypeMem[#REC,
    // from] (memory is constrained to match the 'from' type), and returns a a
    // TypeMem[#REC,to].  The input is asserted to be sharper than a plain #REC
    // alias, in both iter() and opto() phases, and can never be nil.
    return new ConvertPtrTypeName(from,to,badargs);
  }
  static class ConvertPtrTypeName extends IntrinsicNode {
    private final HashMap<String,Type> _lex; // Unique lexical scope
    final TypeObj _from;
    final TypeName _to;
    ConvertPtrTypeName(TypeObj from, TypeName to, Parse badargs) {
      super(to._name,ARGS1,TypeTuple.make(TypeMemPtr.STRUCT),TypeStruct.ALLSTRUCT, BitsAlias.REC);
      //_lex = to._lex;
      //_badargs = badargs;
      //_from = from;
      //_to = to;
      throw AA.unimpl();
    }
    // Take in any struct alias or subclass thereof, with the given 'from'
    // type.  Most structs will NOT have this type.  The pointer passed in must
    // have this type to type-check.
    @Override public Type all_type() { return TypeTuple.make(TypeMem.make(BitsAlias.RECBITS,_to),TypeMemPtr.STRUCT); }
    
    @Override public Type value(GVNGCM gvn) {
      Node nmem = _defs.at(1);
      Node nptr = _defs.at(2);
      Type tmem0= gvn.type(nmem);
      Type tptr0= gvn.type(nptr);
      if( !(tmem0 instanceof TypeMem) )
        throw AA.unimpl();
      TypeMem tmem = (TypeMem)tmem0;
      if( !(tptr0 instanceof TypeMemPtr) )
        throw AA.unimpl();
      TypeMemPtr tptr = (TypeMemPtr)tptr0;
      TypeObj ld = tmem.ld(tptr);

      if( !ld.isa(_from) ) {
        return TypeTuple.make(Type.CTRL,TypeMem.make(BitsAlias.REC,_to.dual()),_to.dual());
      }
      TypeName named_object = TypeName.make(_name,_lex,ld);
      TypeMem named_memory = TypeMem.make(tptr._aliases,named_object);
      TypeMem mem = tmem.merge(named_memory); // Overall memory
      return TypeTuple.make(Type.CTRL,mem,tptr);
    }
    @Override public String err(GVNGCM gvn) {
      Type actual = gvn.type(in(1));
      Type formal = _targs.at(0);
      if( !actual.isa(formal) ) // Actual is not a formal
        return _badargs.typerr(actual,formal);
      return null;
    }
  }
    
  // --------------------------------------------------------------------------
  // Default name constructor using expanded args list
  public static IntrinsicNode convertTypeNameStruct( TypeStruct from_ts, TypeName to, Parse badargs ) {
    return new ConvertTypeNameStruct(from_ts,to,badargs);
  }
  static class ConvertTypeNameStruct extends IntrinsicNode {
    private final HashMap<String,Type> _lex; // Unique lexical scope
    final TypeStruct _from;
    ConvertTypeNameStruct(TypeStruct from, TypeName to, Parse badargs) {
      super(to._name,from._flds,make_targs(from),TypeStruct.ALLSTRUCT,BitsAlias.REC);
      _lex=to._lex;
      _badargs=badargs;
      _from=from;
    }

    // Tuple from Struct
    private static TypeTuple make_targs(TypeStruct from) {
      return TypeTuple.make(from._ts);
    }
    @Override public Node ideal(GVNGCM gvn) {
      Node[] flds = new Node[_args.length];
      for( int i=1; i<flds.length; i++ )
        flds[i] = _defs.at(i);
      Node nn = gvn.xform(new   NewNode(flds,_args));
      Node mn = gvn.xform(new MProjNode(nn,0));
      Node an = gvn.xform(new  ProjNode(nn,1));
      TypeStruct ts = TypeStruct.make(_args,_targs._ts);
      TypeName tn = TypeName.make(_name,_lex,ts);
      Node cvt = new ConvertPtrTypeName(ts,tn,_badargs);
      cvt.add_def(null); // Control
      cvt.add_def(mn);   // Memory
      cvt.add_def(an);   // Ptr
      return cvt;
    }
    
    @Override public Type value(GVNGCM gvn) { throw AA.unimpl(); }
  }

  // --------------------------------------------------------------------------
  static class ConvertI64Str extends IntrinsicNode {
    final TypeTuple _all_type;
    ConvertI64Str(int alias) {
      super("str",ARGS1,TypeTuple.INT64, TypeMemPtr.make(alias), alias);
      _all_type = TypeTuple.make(Type.CTRL,TypeMem.make(alias,TypeStr.STR),_ret);
    }
            
    // Conversion to String allocates memory - so the apply() call returns a new
    // pointer aliased to a hidden String allocation site.  The memory returned
    // is read-only (and can be shared).
    @Override public Type value(GVNGCM gvn) {
      // If the meet with _targs.dual stays above center for all inputs, then we
      // return _ret.dual, the highest allowed result; if all inputs are
      // constants we constant fold; else some input is low so we return _ret,
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
      TypeStr str = TypeStr.con(Long.toString(val.getl()));
      TypeObj obj2 = (TypeObj)obj.meet(str);
      TypeMem res = TypeMem.make(_alias,obj2);
      return TypeTuple.make(Type.CTRL,res,_ret);
    }
  }
  
  static class ConvertF64Str extends IntrinsicNode {
    final TypeTuple _all_type;
    ConvertF64Str(int alias) {
      super("str",ARGS1,TypeTuple.FLT64, TypeMemPtr.make(alias), alias);
      _all_type = TypeTuple.make(Type.CTRL,TypeMem.make(alias,TypeStr.STR),_ret);
    }
            
    // Conversion to String allocates memory - so the apply() call returns a new
    // pointer aliased to a hidden String allocation site.  The memory returned
    // is read-only (and can be shared).
    @Override public Type value(GVNGCM gvn) {
      // If the meet with _targs.dual stays above center for all inputs, then we
      // return _ret.dual, the highest allowed result; if all inputs are
      // constants we constant fold; else some input is low so we return _ret,
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
      TypeStr str = TypeStr.con(Double.toString(val.getd()));
      TypeObj obj2 = (TypeObj)obj.meet(str);
      TypeMem res = TypeMem.make(_alias,obj2);
      return TypeTuple.make(Type.CTRL,res,_ret);
    }
  }
}
