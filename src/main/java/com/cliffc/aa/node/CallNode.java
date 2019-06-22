package com.cliffc.aa.node;

import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.Parse;
import com.cliffc.aa.AA;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;

// See FunNode.  Control is not required for an apply but inlining the function
// body will require it; slot 0 is for Control.  Slot 1 is a function value - a
// Node with a TypeFunPtr.  Slots 2+ are for args, with slot 2 for memory arg.
//
// When the function simplifies to a single TypeFunPtr, the Call can inline.
//
// Call-inlining can happen anytime we have a known function pointer, and
// might be several known function pointers - we are inlining the type analysis
// and not the execution code.  For this kind of inlining we replace the
// CallNode with a call-site specific Epilog, move all the CallNode args to
// the ParmNodes just like the Fun/Parm is a Region/Phi.  The call-site index
// is just like a ReturnPC value on a real machine; it dictates which of
// several possible returns apply... and can be merged like a PhiNode

public class CallNode extends Node {
  int _rpc;                     // Call-site return PC
  private boolean _unpacked;    // Call site allows unpacking a tuple (once)
  private boolean _inlined;     // Inlining a call-site is a 2-stage process; function return wired to the call return
  private Type   _cast_ret;     // Return type has been up-casted
          Parse  _badargs;      // Error for e.g. wrong arg counts or incompatible args
  public CallNode( boolean unpacked, Parse badargs, Node... defs ) {
    super(OP_CALL,defs);
    _rpc = BitsRPC.new_rpc(BitsRPC.ALL); // Unique call-site index
    _unpacked=unpacked;         // Arguments are typically packed into a tuple and need unpacking, but not always
    _badargs = badargs;
  }

  String xstr() { return "Call#"+_rpc; } // Self short name
  String  str() { return xstr(); }       // Inline short name

  // Inline the CallNode
  private Node inline( GVNGCM gvn, Node ctrl, Node mem, Node rez ) {
    rez.add_def(rez);
    mem.add_def(mem);
    set_def(0,ctrl,gvn);        // New control is function epilog control; CProj._idx=0
    set_def(1,mem ,gvn);        // New memory  is function epilog memory ; MProj._idx=1
    set_def(2,rez ,gvn);        // New result  is function epilog result ; DProj._idx=2
    rez.pop();  mem.pop();
    _inlined = true;
    return this;
  }
  // Called by projections when folding away the call
  @Override public Node is_copy(GVNGCM gvn, int idx) { return _inlined ? in(idx) : null; }

  // Number of actual arguments
  private int nargs() { return _defs._len-3; }
  // Actual arguments.
  Node arg( int x ) { return _defs.at(x+3); }
  private void set_arg(int idx, Node arg, GVNGCM gvn) { set_def(idx+3,arg,gvn); }

  private Node ctl() { return in(0); }
  public  Node fun() { return in(1); }
  private Node mem() { return in(2); }
  private void set_fun    (Node fun, GVNGCM gvn) {     set_def    (1,fun,gvn); }
  public  void set_fun_reg(Node fun, GVNGCM gvn) { gvn.set_def_reg(this,1,fun); }
  public BitsFun fidxs(GVNGCM gvn) {
    Type tf = gvn.type(fun());
    return tf instanceof TypeFunPtr ? ((TypeFunPtr)tf).fidxs() : null;
  }
  
  // Clones during inlining all become unique new call sites
  @Override CallNode copy(GVNGCM gvn) {
    CallNode call = (CallNode)super.copy(gvn);
    call._rpc = BitsRPC.new_rpc(_rpc); // Children RPC
    return call;
  }
  
  @Override public Node ideal(GVNGCM gvn) {
    // If an inline is in-progress, no other opts and this node will go dead
    if( _inlined ) return null;
    // If an upcast is in-progress, no other opts until it finishes
    if( _cast_ret !=null ) return null;
    // Dead, do nothing
    if( gvn.type(ctl())==Type.XCTRL ) return null;

    // When do i do 'pattern matching'?  For the moment, right here: if not
    // already unpacked a tuple, and can see the NewNode, unpack it right now.
    if( !_unpacked ) { // Not yet unpacked a tuple
      assert nargs()==1;
      Node mem = mem();
      Type tn = gvn.type(arg(0));
      if( tn instanceof TypeMemPtr ) {
        Type tm = gvn.type(mem);
        if( tm instanceof TypeMem ) {
          Type tx = ((TypeMem)tm).ld((TypeMemPtr)tn);
          if( tx instanceof TypeStruct ) {
            TypeStruct tt = (TypeStruct)tx;
            // Either all the edges from a NewNode (for non-constants), or all
            // the constants types from a constant Tuple from a ConNode
            if( tt.is_con() ) {     // Allocation has constant-folded
              int len = tt._ts.length;
              remove(_defs._len-1,gvn);  // Pop off the ConNode tuple
              //gvn.add_work(mem); 
              for( int i=0; i<len; i++ ) // Push the args; unpacks the tuple
                add_def( gvn.con(tt.at(i)) );
            } else {                // Allocation exists, unpack args
              assert mem instanceof MemMergeNode && mem.in(1) instanceof MProjNode && mem.in(1).in(0) instanceof NewNode;
              remove(_defs._len-1,gvn); // Pop off the NewNode tuple
              Node nn = mem.in(1).in(0);
              int len = nn._defs._len;
              for( int i=1; i<len; i++ ) // Push the args; unpacks the tuple
                add_def( nn.in(i));
            }
            _unpacked = true;       // Only do it once
            return this;
          }
        }
      }
    }

    // Type-checking a function; requires 2 steps, one now, one in the
    // following data Proj from the worklist.
    Node unk  = fun();          // Function epilog/function pointer
    if( unk instanceof TypeNode ) {
      TypeNode tn = (TypeNode)unk;
      //TypeFun t_funptr = (TypeFun)tn._t;
      //set_fun(tn.in(1),gvn);
      //TypeFunPtr tf = t_funptr.fun();
      //for( int i=0; i<nargs(); i++ ) // Insert casts for each parm
      //  set_arg(i,gvn.xform(new TypeNode(tf._ts.at(i),arg(i),tn._error_parse)),gvn);
      //_cast_ret = tf._ret;       // Upcast return results
      //_cast_P = tn._error_parse; // Upcast failure message
      //return this;
      throw AA.unimpl();
    }

    // If the function is unresolved, see if we can resolve it now
    if( unk instanceof UnresolvedNode ) {
      Node fun = resolve(gvn);
      if( fun != null ) { set_fun(fun,gvn); return this; }
    }

    // Unknown function(s) being called
    if( !(unk instanceof EpilogNode) )
      return null;
    // From here on down we know the exact function being called
    EpilogNode epi = (EpilogNode)unk;
    Node ctrl = epi.ctl();
    Node mem  = epi.mem();
    Node rez  = epi.val();
    // Function is single-caller (me) and collapsing
    if( epi.is_copy(gvn,4) != null )
      return inline(gvn,ctrl,mem,rez);

    // Function is well-formed
    FunNode fun = epi.fun();
    if( fun.is_forward_ref() ) return null;

    // Arg counts must be compatible
    if( fun.nargs() != nargs() )
      return null;

    // Single choice; insert actual conversions as needed
    TypeTuple formals = fun._ts;
    for( int i=0; i<nargs(); i++ ) {
      if( fun.parm(i)==null )   // Argument is dead and can be dropped?
        set_arg(i,gvn.con(Type.XSCALAR),gvn); // Replace with some generic placeholder
      else {
        Type formal = formals.at(i);
        Type actual = gvn.type(arg(i));
        if( actual.isBitShape(formal) == 99 ) return null; // Requires user-specified conversion
      }
    }

    // If this is a forward-ref we have no body to inline
    if( epi.is_forward_ref() )
      return null;

    // Check for several trivial cases that can be fully inlined immediately.
    // Check for zero-op body (id function)
    if( rez instanceof ParmNode && rez.in(0) == fun ) return inline(gvn,ctl(),mem(),arg(((ParmNode)rez)._idx));
    // Check for constant body
    if( gvn.type(rez).is_con() ) return inline(gvn,ctl(),mem(),rez);

    // Check for a 1-op body using only constants or parameters
    boolean can_inline=true;
    for( Node parm : rez._defs )
      if( parm != null && parm != fun &&
          !(parm instanceof ParmNode && parm.in(0) == fun) &&
          !(parm instanceof ConNode) )
        can_inline=false;       // Not trivial
    if( can_inline ) {
      Node irez = rez.copy(gvn);// Copy the entire function body
      for( Node parm : rez._defs )
        irez.add_def((parm instanceof ParmNode && parm.in(0) == fun) ? arg(((ParmNode)parm)._idx) : parm);
      if( irez instanceof PrimNode ) ((PrimNode)irez)._badargs = _badargs;
      return inline(gvn,ctl(),mem(),gvn.xform(irez)); // New exciting replacement for inlined call
    }

    assert fun.in(1)._uid!=0; // Never wire into a primitive, just clone/inline it instead (done just above)
    assert fun.nargs() == nargs();

    // Always wire caller args into known functions
    return wire(gvn,fun,false);
  }

  // Wire the call args to a known function, letting the function have precise
  // knowledge of its callers and arguments.
  // Leaves the Call in the graph - making the graph "a little odd" - double
  // CTRL users - once for the call, and once for the function being called.
  private Node wire( GVNGCM gvn, FunNode fun, boolean is_gcp ) {
    Node ctrl = ctl();
    for( int i=1; i<fun._defs.len(); i++ )
      if( fun.in(i)==ctrl ) // Look for same control
        return null;        // Already wired up

    // Make sure we have enough args before wiring up (makes later life easier
    // to assume correct arg counts).  Note that we cannot, in general,
    // type-check the args during GCP, as they will start out too-high and pass
    // any isa-check.  Later, after wiring up in GCP they might fall to an
    // error state - so we have to support having error args coming in.
    for( Node arg : fun._uses ) {
      if( arg.in(0) == fun && arg instanceof ParmNode ) {
        int idx = ((ParmNode)arg)._idx; // Argument number, or -1 for rpc
        if( idx >= nargs() ) return null; // Wrong arg-count
        if( is_gcp ) {
          Type formal = fun.targ(idx);
          Type actual = idx==-1 ? TypeRPC.make(_rpc) : gvn.type(arg(idx));
          if( !actual.isa(formal) )
            return null;     // Even if actual falls more, will never be formal
        }
      }
    }
    
    // Add an input path to all incoming arg ParmNodes from the Call.  Cannot
    // assert finding all args, because dead args may already be removed - and
    // so there's no Parm/Phi to attach the incoming arg to.
    for( Node arg : fun._uses ) {
      if( arg.in(0) == fun && arg instanceof ParmNode ) {
        int idx = ((ParmNode)arg)._idx; // Argument number, or -1 for rpc
        assert idx<nargs();
        Node actual = idx==-1 ? gvn.con(TypeRPC.make(_rpc)) : (idx==-2 ? mem() : arg(idx));
        gvn.add_def(arg,actual);
      }
    }
    // Add Control for this path.  Sometimes called from fun.Ideal() (because
    // inlining), sometimes called by Epilog when it discovers all callers
    // known.
    assert gvn.touched(fun);
    gvn.add_def(fun,ctrl);
    return this;
  }

  // Make real call edges from virtual call edges
  private void wire(GVNGCM gvn) {
    BitsFun fidxs = fidxs(gvn);     // Get all the propagated reaching functions
    if( fidxs.above_center() ) return;
    for( int fidx : fidxs ) {   // For all functions
      if( fidx >= FunNode.PRIM_CNT ) { // Do not wire up primitives, but forever take their default inputs and outputs
        // Can be wiring up the '#[ALL]' list.  Stop after seeing all existing functions
        if( fidx >= FunNode.FUNS._len ) return;
        FunNode fun = FunNode.find_fidx(fidx);
        if( !fun.is_dead() && !fun.is_forward_ref() ) wire(gvn,fun,true);
      }
    }
  }
  
  @Override public TypeTuple value(GVNGCM gvn) {
    Type tc = gvn.type(ctl());  // Control type
    if( _inlined )              // Inlined functions just pass thru & disappear
      return TypeTuple.make(tc,gvn.type(in(1)),gvn.type(in(2)));
    Node fp = fun();            // If inlined, its the result, if not inlined, its the function being called
    Type t = gvn.type(fp);
    if( tc == Type.XCTRL || tc == Type.ANY ) // Call is dead?
      return TypeTuple.XCALL;
    if( !(fp instanceof UnresolvedNode || fp instanceof EpilogNode) )
      return TypeTuple.XCALL;
    if( fp.is_forward_ref() )
      return TypeTuple.CALL;
    if( Type.SCALAR.isa(t) ) // Calling something that MIGHT be a function, no idea what the result is
      return TypeTuple.CALL;
    if( !t.isa(TypeFunPtr.GENERIC_FUNPTR) ) // Calling something that MIGHT be a function, no idea what the result is
      return TypeTuple.CALL;

    if( gvn._opt ) // Manifesting optimistic virtual edges between caller and callee
      wire(gvn);   // Make real edges from virtual edges
    
    if( fp instanceof EpilogNode )
      // Return {control,mem,value} tuple.
      return value1(gvn,(EpilogNode)fp); // Return type or SCALAR if invalid args
      
    if( gvn._opt ) {
      TypeTuple trez = TypeTuple.CALL; // Base for JOIN
      // For unresolved, we can take the BEST choice; i.e. the JOIN of every
      // choice.  Typically one choice works and the others report type
      // errors on arguments.
      for( Node epi : fp._defs )
        trez = (TypeTuple)trez.join(value1(gvn,(EpilogNode)epi)); // JOIN of choices
      return trez;              // Return {control,mem,value} tuple.
    } else {
      TypeTuple trez = TypeTuple.XCALL; // Base for MEET
      // For unresolved, we can take the BEST choice; i.e. the JOIN of every
      // choice.  Typically one choice works and the others report type
      // errors on arguments.
      for( Node epi : fp._defs )
        trez = (TypeTuple)trez.meet(value1(gvn,(EpilogNode)epi)); // JOIN of choices
      return trez;              // Return {control,mem,value} tuple.
    }
  }

  // See if the arguments are valid.  If valid, return the function's return
  // type.  If not valid return SCALAR - as an indicator that the function
  // cannot be called, so the JOIN of valid returns is not lowered.
  private TypeTuple value1( GVNGCM gvn, EpilogNode epi ) {
    Type t = gvn.type(epi);
    if( !(t instanceof TypeFunPtr) ) // Might be any function, returning anything
      return t.above_center() ? TypeTuple.XCALL : TypeTuple.CALL;
    Type    tctrl=gvn.type(epi.ctl());
    Type    tmem =gvn.type(epi.mem());
    Type    tval =gvn.type(epi.val());
    if( tctrl == Type.XCTRL ) return TypeTuple.XCALL; // Function will never return
    assert tctrl==Type.CTRL;      // Function will never return?
    FunNode fun = epi.fun();
    if( fun.is_forward_ref() ) return TypeTuple.make(tctrl,tmem,tval); // Forward refs do no argument checking

    if( fun.nargs() != nargs() ) return TypeTuple.CALL; // Function not called, nothing to JOIN
    // Now do an arg-check
    TypeTuple formals = fun._ts; // Type of each argument
    for( int j=0; j<nargs(); j++ ) {
      Type actual = gvn.type(arg(j));
      Type formal = formals.at(j);
      if( !actual.isa(formal) ) // Actual is not a formal; call will not go thru
        return TypeTuple.CALL;  // Argument not valid, nothing to JOIN
    }
    return TypeTuple.make(tctrl,tmem,tval);
  }
  
  // Given a list of actuals, apply them to each function choice.  If any
  // (!actual-isa-formal), then that function does not work and supplies an
  // ALL to the JOIN.  This is common for non-inlined calls where the unknown
  // arguments are approximated as SCALAR.  Lossless conversions are allowed as
  // part of a valid isa test.  As soon as some function returns something
  // other than ALL (because args apply), it supersedes other choices- which
  // can be dropped.

  // If more than one choice applies, then the choice with fewest costly
  // conversions are kept; if there is more than one then the join of them is
  // kept - and the program is not-yet type correct (ambiguous choices).
  public Node resolve( GVNGCM gvn ) {
    BitsFun fidxs = fidxs(gvn);
    if( fidxs == null ) return null; // Might be e.g. ~Scalar
    if( !fidxs.above_center() ) return null; // Sane as-is

    // Set of possible choices with fewest conversions
    class Data {
      private final int _xcvt, _fidx;
      private final boolean _unk;
      private final TypeTuple _formals;
      private Data( int x, boolean u, int f, TypeTuple ts ) { _xcvt = x; _unk=u; _fidx=f; _formals=ts; }
    }
    Ary<Data> ds = new Ary<>(new Data[0]);

    // For each function, see if the actual args isa the formal args.  If not,
    // toss it out.  Also count conversions, and keep the minimal conversion
    // function with all arguments known.
    outerloop:
    for( int fidx : fidxs ) {
      FunNode fun = FunNode.find_fidx(fidx);
      if( fun.nargs() != nargs() ) continue; // Wrong arg count, toss out
      TypeTuple formals = fun._ts;   // Type of each argument
      
      // Now check if the arguments are compatible at all, keeping lowest cost
      int xcvts = 0;             // Count of conversions required
      boolean unk = false;       // Unknown arg might be incompatible or free to convert
      for( int j=0; j<nargs(); j++ ) {
        Type actual = gvn.type(arg(j));
        if( actual==Type.XSCALAR && arg(j) instanceof ConNode )
          continue; // Forced super-high arg is always compatible before formal is dead
        Type tx = actual.join(formals.at(j));
        if( tx != actual && tx.above_center() ) // Actual and formal have values in common?
          continue outerloop;   // No, this function will never work; e.g. cannot cast 1.2 as any integer
        byte cvt = actual.isBitShape(formals.at(j)); // +1 needs convert, 0 no-cost convert, -1 unknown, 99 never
        if( cvt == 99 )         // Happens if actual is e.g. TypeErr
          continue outerloop;   // No, this function will never work
        if( cvt == -1 ) unk = true; // Unknown yet
        else xcvts += cvt;          // Count conversions
      }

      Data d = new Data(xcvts,unk,fidx,formals);
      ds.push(d);
    }
    
    // Toss out choices with strictly more conversions than the minimal
    int min = 999;              // Required conversions
    for( Data d : ds )          // Find minimal conversions
      if( !d._unk && d._xcvt < min ) // If unknown, might need more converts
        min = d._xcvt;
    for( int i=0; i<ds._len; i++ ) // Toss out more expensive options
      if( ds.at(i)._xcvt > min )   // Including unknown... which might need more converts
        ds.del(i--);

    // If this set of formals is strictly less than a prior acceptable set,
    // replace the prior set.  Similarly, if strictly greater than a prior set,
    // toss this one out.
    for( int i=0; i<ds._len; i++ ) {
      if( ds.at(i)._unk ) continue; 
      TypeTuple ifs = ds.at(i)._formals;
      for( int j=i+1; j<ds._len; j++ ) {
        if( ds.at(j)._unk ) continue; 
        TypeTuple jfs = ds.at(j)._formals;
        if( ifs.isa(jfs) ) ds.del(j--); // Toss more expansive option j
        else if( jfs.isa(ifs) ) { ds.del(i--); break; } // Toss option i
      }
    }

    if( ds._len==0 ) return null;   // No choices apply?  No changes.
    if( ds._len==1 )                // Return the one choice
      return FunNode.find_fidx(ds.pop()._fidx).epi();
    if( ds._len==fun()._defs._len ) return null; // No improvement
    // TODO: return shrunk list
    //return gvn.xform(new UnresolvedNode(ns.asAry())); // return shrunk choice list
    return null;
  }
  
  @Override public String err(GVNGCM gvn) {
    assert !_inlined;           // Should have already cleaned out
    
    // Error#1: fail for passed-in unknown references
    for( int j=0; j<nargs(); j++ ) 
      if( arg(j).is_forward_ref() )
        return _badargs.forward_ref_err(((EpilogNode)arg(j)).fun());
    
    Node fp = fun();      // Either function pointer, or unresolved list of them
    Node xfp = fp instanceof UnresolvedNode ? fp.in(0) : fp;
    Type txfp = gvn.type(xfp);
    if( !(txfp instanceof TypeFunPtr) )
      return _badargs.errMsg("A function is being called, but "+txfp+" is not a function type");

    EpilogNode epi = (EpilogNode)xfp;
    if( fp.is_forward_ref() ) // Forward ref on incoming function
      return _badargs.forward_ref_err(epi.fun());

    // Error#2: bad-arg-count
    FunNode fun = epi.fun();
    if( fun.nargs() != nargs() )
      return _badargs.errMsg("Passing "+nargs()+" arguments to "+(fun.xstr())+" which takes "+fun.nargs()+" arguments");

    // Error#3: Now do an arg-check
    TypeTuple formals = fun._ts; // Type of each argument
    for( int j=0; j<nargs(); j++ ) {
      Type actual = gvn.type(arg(j));
      Type formal = formals.at(j);
      if( !actual.isa(formal) ) // Actual is not a formal
        return _badargs.typerr(actual,formal);
    }
    
    return null;
  }
  
  // Called from the data proj.  Return a TypeNode with proper casting on return result.
  TypeNode upcast_return(GVNGCM gvn) {
    Type t = _cast_ret;
    if( t==null ) return null;  // No cast-in-progress
    _cast_ret = null;           // Gonna upcast the return result now
    gvn.add_work(this);         // Revisit after the data-proj cleans out
    return new TypeNode(t,null,null);
  }

  @Override public Type all_type() { return TypeTuple.make(Type.CTRL,TypeMem.MEM,Type.SCALAR); }
  @Override public int hashCode() { return super.hashCode()+_rpc; }
  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( !super.equals(o) ) return false;
    if( !(o instanceof CallNode) ) return false;
    CallNode call = (CallNode)o;
    return _rpc==call._rpc;
  }

}

