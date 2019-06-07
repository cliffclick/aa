package com.cliffc.aa.node;

import com.cliffc.aa.AA;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.type.*;

import java.util.HashMap;

// Known (intrinsic) library calls.  They typically have memory side effects,
// or else they would be a PrimNode instead.  Like PrimNodes they are wrapped
// in a Fun/Epilog but include memory effects.
public abstract class LibCallNode extends PrimNode {
  int _alias;                   // Alias class for new memory
  LibCallNode( String name, String[] args, TypeTuple targs, Type ret, int alias ) {
    super(OP_LIBCALL,name,args,targs,ret);
    _alias = alias;
  }

  public static LibCallNode[] LIBCALLS = new LibCallNode[] {
    new ConvertI64Str(BitsAlias.new_string()),
    new ConvertF64Str(BitsAlias.new_string())
  };

  // Return is a ptr-to-memory; tuple of: (mem#alias:obj, ptr#alias)
  private static TypeTuple ret(int alias, TypeObj obj) {
    return TypeTuple.make(TypeMem.make(alias,obj),TypeMemPtr.make(alias));
  }
  // Worse-case type for this Node.  Preserves precise alias - so improves Type
  // after copy/clone.  Required to be precise for GVNGCM.opto starting point.
  @Override public Type all_type() { return ret(_alias,TypeStr.STR); }

  static TypeMem argmem(TypeObj from) { return TypeMem.make(BitsAlias.REC,from); }
  abstract TypeMem argmem();
  
  // Wrap the PrimNode with a Fun/Epilog wrapper that includes memory effects.
  @Override public EpilogNode as_fun( GVNGCM gvn ) {
    FunNode  fun = ( FunNode) gvn.xform(new  FunNode(this,((TypeTuple)_ret).at(1),argmem())); // Points to ScopeNode only
    ParmNode rpc = (ParmNode) gvn.xform(new ParmNode(-1,"rpc",fun, gvn.con(TypeRPC.ALL_CALL),null));
    add_def(null);              // Control for the primitive in slot 0
    for( int i=0; i<_args.length; i++ ) // Args follow
      add_def(gvn.xform(new ParmNode(i,_args[i],fun, gvn.con(_targs.at(i)),null)));
    Node prim = gvn.xform(this);
    Node mem_prim = gvn.xform(new MProjNode(prim,0));
    Node val = gvn.xform(new ProjNode(prim,1));
    Node mem = in(1);
    Node mem2 = gvn.xform(new MergeMemNode(mem,mem_prim));
    return new EpilogNode(fun,mem2,val,rpc,fun,fun._fidx,null);
  }
  
  // Clones during inlining all become unique new sites
  @Override LibCallNode copy(GVNGCM gvn) {
    LibCallNode nnn = (LibCallNode)super.copy(gvn);
    nnn._alias = BitsAlias.new_alias(_alias); // Children alias classes
    return nnn;
  }
  @Override public String xstr() { return _name+"_#"+_alias; }
  
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
  public static LibCallNode convertTypeName( TypeObj from, TypeName to, Parse badargs ) {
    // Builds a function which takes in a TypeMemPtr.STRUCT and TypeMem[#REC,
    // from] (memory is constrained to match the 'from' type), and returns a a
    // TypeMem[#REC,to].  The input is asserted to be sharper than a plain #REC
    // alias, in both iter() and opto() phases, and can never be nil.
    return new ConvertPtrTypeName(from,to,badargs);
  }
  static class ConvertPtrTypeName extends LibCallNode {
    private final Parse _badargs; // Only for converts
    private final HashMap<String,Type> _lex; // Unique lexical scope
    final TypeObj _from;
    final TypeName _to;
    ConvertPtrTypeName(TypeObj from, TypeName to, Parse badargs) {
      super(to._name,PrimNode.ARGS1,TypeTuple.make(argmem(from),TypeMemPtr.STRUCT),ret(BitsAlias.REC,to), BitsAlias.REC);
      _lex = to._lex;
      _badargs = badargs;
      _from = from;
      _to = to;
    }
    // Take in any struct alias or subclass thereof, with the given 'from'
    // type.  Most structs will NOT have this type.  The pointer passed in must
    // have this type to type-check.
    @Override TypeMem argmem() { return argmem(_from); }
    @Override public Type all_type() { return TypeTuple.make(TypeMem.make(BitsAlias.REC,_to),TypeMemPtr.STRUCT); }
    
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
        return TypeTuple.make(TypeMem.make(BitsAlias.REC,_to.dual()),_to.dual());
      }
      TypeName named_object = TypeName.make(_name,_lex,ld);
      TypeMem named_memory = TypeMem.make(tptr.getbit(),named_object);
      TypeMem mem = tmem.merge(named_memory); // Overall memory
      return TypeTuple.make(mem,tptr);
    }
    @Override public TypeTuple apply( Type[] args ) { throw AA.unimpl(); }
    @Override public boolean is_lossy() { return false; }
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
  public static LibCallNode convertTypeNameStruct( TypeStruct from_ts, TypeName to, Parse badargs ) {
    return new ConvertTypeNameStruct(from_ts,to,badargs);
  }
  static class ConvertTypeNameStruct extends LibCallNode {
    private final Parse _badargs; // Only for converts
    private final HashMap<String,Type> _lex; // Unique lexical scope
    final TypeStruct _from;
    ConvertTypeNameStruct(TypeStruct from, TypeName to, Parse badargs) {
      super(to._name,from._flds,make_args(from),ret(BitsAlias.REC,to),BitsAlias.REC);
      _lex=to._lex;
      _badargs=badargs;
      _from=from;
    }
    // Insert memory in front of the other arguments
    private static TypeTuple make_args(TypeStruct from) {
      Type[] ts = new Type[from._ts.length+1];
      System.arraycopy(from._ts,0,ts,1,from._ts.length);
      ts[0] = argmem(from);
      return TypeTuple.make(ts);
    }
    @Override TypeMem argmem() { return argmem(_from); }
    @Override public Node ideal(GVNGCM gvn) {
      Node[] flds = new Node[_args.length+1];
      for( int i=1; i<flds.length; i++ )
        flds[i] = _defs.at(i+1);
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
    @Override public Type apply( Type[] args ) { throw AA.unimpl(); }
  }

  // --------------------------------------------------------------------------
  static class ConvertI64Str extends LibCallNode {
    ConvertI64Str(int alias) {
      super("str",PrimNode.ARGS1,TypeTuple.INT64, ret(alias,TypeStr.STR), alias);
    }
            
    // Library calls update memory.  These calls have the default boot-time
    // memory inputs and outputs.
    @Override TypeMem argmem() { return TypeMem.XMEM; }

    // Conversion to String allocates memory - so the apply() call returns a new
    // pointer aliased to a hidden String allocation site.  The memory returned
    // is read-only (and can be shared).
    @Override public Type value(GVNGCM gvn) {
      // If the meet with _targs.dual stays above center for all inputs, then we
      // return _ret.dual, the highest allowed result; if all inputs are
      // constants we constant fold; else some input is low so we return _ret,
      // the lowest possible result.
      boolean is_con = true;
      for( int i=1; i<_defs._len; i++ ) {
        Type t = _targs.at(i-1).dual().meet(gvn.type(in(i)));
        if( t.above_center() ) is_con = false; // Not a constant
        else if( !t.is_con() ) return _ret;    // Some input is too low
      }
      if( !is_con ) return _ret.dual(); // Some inputs above center and none are low
      
      // Conversion to String allocates memory - so return a new pointer
      // aliased to a hidden String allocation site.  The memory returned is
      // read-only (and can be shared).
      TypeMem mem = (TypeMem)gvn.type(in(1));
      TypeObj obj = mem.at(_alias);  // Prior memory contents at this alias
      Type val = gvn.type(in(2));    // Known constant
      TypeStr str = TypeStr.con(Long.toString(val.getl()));
      TypeObj obj2 = (TypeObj)obj.meet(str);
      TypeMem res = TypeMem.make(_alias,obj2);
      return TypeTuple.make(res,TypeMemPtr.make(_alias));
    }
    @Override public TypeTuple apply( Type[] args ) { throw AA.unimpl(); }
    @Override public boolean is_lossy() { return false; }
  }
  
  static class ConvertF64Str extends LibCallNode {
    ConvertF64Str(int alias) {
      super("str",PrimNode.ARGS1,TypeTuple.FLT64, ret(alias,TypeStr.STR), alias);
    }
            
    // Library calls update memory.  These calls have the default boot-time
    // memory inputs and outputs.
    @Override TypeMem argmem() { return TypeMem.XMEM; }

    // Conversion to String allocates memory - so the apply() call returns a new
    // pointer aliased to a hidden String allocation site.  The memory returned
    // is read-only (and can be shared).
    @Override public Type value(GVNGCM gvn) {
      // If the meet with _targs.dual stays above center for all inputs, then we
      // return _ret.dual, the highest allowed result; if all inputs are
      // constants we constant fold; else some input is low so we return _ret,
      // the lowest possible result.
      Type val = gvn.type(in(2));
      Type t = TypeFlt.FLT64.dual().meet(val);
      if( t.above_center() ) return _ret.dual();
      if( !t.is_con() ) return _ret;    // Some input is too low
      
      // Conversion to String allocates memory - so return a new pointer
      // aliased to a hidden String allocation site.  The memory returned is
      // read-only (and can be shared).
      TypeMem mem = (TypeMem)gvn.type(in(1));
      TypeObj obj = mem.at(_alias);  // Prior memory contents at this alias
      TypeStr str = TypeStr.con(Double.toString(val.getd()));
      TypeObj obj2 = (TypeObj)obj.meet(str);
      TypeMem res = TypeMem.make(_alias,obj2);
      return TypeTuple.make(res,TypeMemPtr.make(_alias));
    }
    @Override public TypeTuple apply( Type[] args ) { throw AA.unimpl(); }
    @Override public boolean is_lossy() { return false; }
  }
}
