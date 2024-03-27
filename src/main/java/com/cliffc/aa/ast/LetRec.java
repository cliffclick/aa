package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.*;
import com.cliffc.aa.type.TypeFld.Access;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;

import java.util.Arrays;

import static com.cliffc.aa.AA.TODO;


public class LetRec extends ASTVars {

  private LetRec() { super(new Ary<>(String.class));  }
  public  LetRec(String var, AST def, AST body) {
    this();
    _vars.push(var);
    _kids.push(def);
    if( body instanceof LetRec let ) {
      _vars.addAll(let._vars);
      _kids.addAll(let._kids);
      assert !(body() instanceof LetRec); // Only 1 round of rollups needed?
    } else
      _kids.push(body);

  }
  AST body() { return _kids._len > _vars._len ? _kids.last() : null; }


  // name = name = def; ....
  @Override public SB str(SB sb) {
    for( int i=0; i<_vars._len; i++ ) {
      sb.p(_vars.at(i)).p(" = ");
      _kids.at(i).str(sb);
      sb.p(";").nl().i();
    }
    return body()==null ? sb : body().str(sb);
  }


  // When given a collection of ASTs, sort them into groups with mutually Ident
  // references, then break them up into split LetRecs, where each LetRec is a
  // mutually recursive set, and does not define anything else.

  // Classic SCC/cycle finder, except supports multi-edges.  Tracks "edges"
  // between defs in this LetRec (and not any other, although they may
  // recursively maintain their own).  An edge is an Ident in one def referring
  // to a var in another def.

  // Maintains a stack and a cycle leader, which doubles as a visit bit.
  // Cycle leaders use U-F notion and can roll-up.

  // First, find a notion of edges - we use a stupid/small/tight/fast version;
  // a node is the *byte* index into the kids array; an edge collection is a
  // set of bytes in a long; a 255 byte means "no edge".

  private long[] _edges;
  private int _idx;
  private long _stack;          // A stack of max 8
  private byte[] _leaders;

  int addEdge(int to) {
    // Found a Let reference in the body; the def has already been walked
    if( _idx >= _edges.length ) return 0;
    // Found a Let reference in the def; body not seen yet
    assert (_edges[_idx] >>> (64-8))==0xFF; // No edge
    assert 0 <= to && to < _vars._len;
    // Add an edge
    _edges[_idx] = (_edges[_idx]<<8) | to;
    return 0;
  }

  @Override public int mutLetRec() {
    _edges = new long[_vars._len];
    Arrays.fill(_edges,-1);
    _leaders = new byte[_vars._len];
    Arrays.fill(_leaders,(byte)-1);
    _stack = -1;
    // Set parent field.  Walk the children, building def/use edges
    for( _idx=0; _idx<_vars._len; _idx++ ) {
      _kids.at(_idx)._par = this;
      _kids.at(_idx).mutLetRec();
    }
    body()._par = this;
    body().mutLetRec();

    // As the root of a forest, walk all the trees, finding cycles.
    for( int i=0; i<_vars._len; i++ )
      walk((byte)i);

    // topo sort the dag (lumping all members of a cycle together)
    _stack = 0;
    for( int i=0; i<_vars._len; i++ )
      rebuild((byte)i, (byte)-1, null);
    // Drop self, been replaces by a tower of sorted MutLetRec
    _par._kids.replace(this,body());
    body()._par = _par;
    return 0;
  }


  // Walk
  void walk(byte idx) {
    if( _leaders[idx] != -1 ) return; // Already visited
    _leaders[idx] = idx;              // Make self leader
    _stack = (_stack << 8) | idx;     // Push on stack
    for( long edges = _edges[idx]; edges != -1; edges >>= 8 )
      edge2((byte)(edges&0xFF)); // Edge walk
    _stack = _stack>>8;          // Pop stack
  }

  //
  void edge2( byte idx ) {
    byte leader = leader(idx);
    if( leader == -1 )  {       // No leader?
      walk(idx);                // Walk it, checking for cycles
      return;
    }
    // Found a cycle
    long stk = _stack, i=0;
    while( stk != -1 && ((byte)(stk&0xFF)) != idx && leader((byte)(stk&0xFF)) != leader )
      { stk >>= 8; i++; }
    if( stk== -1 ) // Due to multi-edges, we might not find if dupped, so just ignore
      return;
    // Set the cycle leader to all members
    stk = _stack;
    while( i>0 ) {
      _leaders[(byte)stk&0xFF] = leader;
      stk >>= 8;
      i--;
    }
  }

  // Find leader, with UF rollup
  private byte leader(byte idx) {
    byte leader = _leaders[idx];
    if( leader==-1 ) return -1; // No leader
    int idx2 = _leaders[leader];
    if( idx2 == leader ) return leader;
    // Classic UF rollup here
    throw TODO();
  }

  //
  void rebuild( byte idx, byte leader, LetRec let ) {
    if( (_stack & (1L<<idx)) != 0 )
      return;                   // Been there, done that
    _stack |= (1L<<idx);        // Marked been there
    // Check for changing leaders; if so install a new LetRec
    int old = leader;
    if( leader(idx) != leader ) {
      leader = leader(idx);
      let = new LetRec();       // Changing leaders
    }
    // Add vars to the LetRec
    let._vars.push(_vars.at(idx));
    let._kids.push(_kids.at(idx));
    _kids.at(idx)._par = let;
    for( long edges = _edges[idx]; edges != -1; edges >>= 8 )
      rebuild((byte)(edges&0xFF), leader, let); // Edge walk
    // Finished new leader?
    if( old != leader ) {
      // Install in the whole AST
      _par._kids.replace(this,let);
      let._par = _par;
      _par = let;
      let._kids.setX(let._vars._len, this);
    }
  }


  StructNode _stk;
  int _oldx;
  @Override public void nodes( Env e ) {
    // Build a stack frame and populate with the mutually-recursive vars, all at once.
    _stk = e._scope.stk();
    _oldx = _stk.len();
    for( String var : _vars ) {
      ForwardRefNode fref = new ForwardRefNode(var,null).init();
      fref.scope();
      _stk.add_fld(var,Access.Final,fref,null);
    }
    for( int i=0; i<_vars._len; i++ ) {
      // Make nodes for all the defs
      _kids.at(i).nodes(e);
      Node def = e._scope.rez();
      ForwardRefNode fref = (ForwardRefNode)_stk.in(_oldx+i);
      // Assign def to name
      _stk.set_fld(_vars.at(i),Access.Final,def,true);
      if( !fref.isDead() ) {
        fref.self();
        fref.close();
        fref.subsume(def);
      }
    }
    _oldx = _stk.len();
    // Now the body
    body().nodes(e);
  }

  @Override void addNonGen(FreshNode frsh) {
    for( int i=_oldx; i<_stk.len(); i++ )
      frsh.addDef(_stk.in(i));
  }

}
