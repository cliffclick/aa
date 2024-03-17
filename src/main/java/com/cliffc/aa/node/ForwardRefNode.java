package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.ErrMsg;
import com.cliffc.aa.Parse;
import com.cliffc.aa.tvar.TVErr;
import com.cliffc.aa.type.*;
import com.cliffc.aa.util.Ary;

import static com.cliffc.aa.AA.TODO;

// A forward ref in the parser.
public class ForwardRefNode extends Node {
  public final String _name;   // Name of forward ref
  Parse _bad;                  // Where it first appears
  // Forward Ref moves through 4 states:
  // - 0 forward-ref; scope is not known; FRef might promote to outer scopes
  // - 1 scoped; scope is known, but FRef is not yet defined
  // - 2 self defined; FRef has a local def, but it might depend on other FRefs
  // - 3 closed def; FRef has a local def, and a SCC of mutual let-rec defs.
  private byte _fref;

  // Input 0 is the self-definition; null if not known yet.
  // Inputs 1+ are other forward refs this one depends on.  They might form
  // mutually recursive definitions, e.g. is_even depends on is_dd, or might
  // not in a classic simple forward reference.
  public ForwardRefNode( String name, Parse bad ) {
    super((Node)null);
    _name = name;
    _bad=bad;
    _val = TypeFunPtr.GENERIC_FUNPTR;
  }

  @Override public String label() {
    if( isDead() ) return "DEAD"+_name;
    String s = switch( _fref ) {
    case 0 -> "notScoped";
    case 1 -> "scoped";
    case 2 -> "self";
    case 3 -> "closed";
    default -> "?";
    };
    return s+":"+_name;
  }

  @Override public Type value() {
    Node c = isCopy(0);
    if( c==null )
      return TypeFunPtr.make(false,BitsFun.NALL,1,TypeMemPtr.ISUSED,Type.ALL);
    return c._val;
  }

  @Override public Node ideal_reduce() { return isCopy(1); }

  @Override public boolean has_tvar() { return true; }
  @Override public TVErr _set_tvar() {
    TVErr e = new TVErr();
    e.err("Unknown ref '"+_name+"'",null,_bad,false);
    return e;
  }

  // One-time flip _fref, no longer a forward ref
  public ForwardRefNode scope() { assert _fref==0; _fref=1; return this; }
  public ForwardRefNode self () { assert _fref==1; _fref=2; return this; }
  public ForwardRefNode close() { assert _fref==2; _fref=3; return this; }
  public boolean isNotScoped() { return _fref==0; }
  public boolean isScoped() { return _fref==1; }
  public boolean isSelf  () { return _fref==2; }
  public boolean isClosed() { return _fref==3; }

  // A forward-ref was assigned in the parser; self-defines it here and look
  // for a closed mutual let-rec.
  public Node assign(Node def, Env e) {
    self();                        // Set forward-ref defined
    setDef(0,def);                 // What its defined too
    Env.GVN.add_flow_reduce(this); // On worklist
    if( def._val instanceof TypeFunPtr tfp )
      RetNode.get(tfp.fidxs()).funptr()._name = _name;
    // See if we discover a closed set of mutual defs
    MUTUAL.clear();
    MUTUAL.push(this);
    for( int i=0; i<MUTUAL._len; i++ ) {
      ForwardRefNode fref = MUTUAL.at(i);
      if( fref._fref < 2 ) return def; // Not a closed set
      for( int j=1; j<fref.len(); j++ )
        if( fref.in(j) instanceof ForwardRefNode fref2 && MUTUAL.find(fref2) == -1 )
          MUTUAL.push(fref2);
    }

    // Insert a FreshNode, with proper nongen set, into each ForwardRef in the cycle
    for( ForwardRefNode fref : MUTUAL ) {
      fref.close();
      // Fresh, normal nongen set from the environment (includes Lambda args)
      FreshNode frsh = new FreshNode(fref.in(0),e);
      // Also include everything in the mutual self-recursive set
      for( Node fref2 : MUTUAL )
        frsh.addDef(fref2);
      // This is what the ForwardRef defines - this Fresh node
      fref.setDef(0,frsh);
      // Remove
      while( fref.len()>1 ) fref.pop();
    }
    for( ForwardRefNode fref : MUTUAL ) {
      // fref.subsume(fref.in(0));
      throw TODO();
    }
    return def;
  }

  //
  private static final Ary<ForwardRefNode> MUTUAL = new Ary<>(ForwardRefNode.class);

  //@Override public Node isCopy(int idx) { return isClosed() ? in(0) : null; }
  @Override int hash() { return _fref; }
  @Override public boolean equals(Object o) { return this==o; }

  // Assigning the forward-ref removes the error
  @Override public ErrMsg err( boolean fast ) {  return ErrMsg.forward_ref(_bad,_name);  }

}
