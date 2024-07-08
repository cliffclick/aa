package com.cliffc.aa.ast;

import com.cliffc.aa.Env;
import com.cliffc.aa.node.*;
import com.cliffc.aa.type.TypeFld.Access;
import com.cliffc.aa.util.Ary;
import com.cliffc.aa.util.SB;

import java.util.Arrays;

import static com.cliffc.aa.AA.TODO;


public class LetRec extends ASTVars {
  private final Ary<Access> _accs;
  // Cyclic ref; needs the full ForwardRef treatment during expansion
  private boolean _cyclic;

  private LetRec() { super(new Ary<>(String.class));  _accs = new Ary<>(Access.class); }
  public  LetRec(String var, boolean rw, AST def, AST body) {
    this();
    _vars.push(var);
    _accs.push(rw ? Access.RW : Access.Final);
    _kids.push(def);
    if( body instanceof LetRec let ) {
      _kids.addAll(let._kids);
      _vars.addAll(let._vars);
      _accs.addAll(let._accs);
      assert !(body() instanceof LetRec); // Only 1 round of rollups needed?
    } else
      _kids.push(body);

  }
  AST body() { return _kids._len > _vars._len ? _kids.last() : null; }


  // name = name = def; ....
  @Override public SB str(SB sb) {
    for( int i=0; i<_vars._len; i++ ) {
      sb.p(_vars.at(i));
      sb.p(_accs.at(i)==Access.RW ? " := " : " = ");
      _kids.at(i).str(sb).p(";").nl().i();
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
  private boolean[] _cyclics; // Is leader cyclic?

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
    _cyclics = new boolean[_vars._len];
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
    // Found an edge to a prior leader
    long stk = _stack, i=0;
    while( stk != -1 && ((byte)(stk&0xFF)) != idx && leader((byte)(stk&0xFF)) != leader )
      { stk >>= 8; i++; }
    if( stk== -1 ) // Due to multi-edges, we might not find if dupped, so just ignore
      return;      // No cycle
    _cyclics[leader]=true;
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
      let._cyclic = _cyclics[leader];
    }
    // Add vars to the LetRec
    let._accs.push(_accs.at(idx));
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
  Node[] _frefs;
  @Override public void nodes( Env e ) {
    ScopeNode scope = e._scope;
    StructNode stk = _stk = scope.stk();
    // Single variables can be re-definitions or StoreNodes
    if( !_cyclic ) {
      assert _vars._len==1 && _kids._len==2;
      _kids.at(0).nodes(e);     // Go ahead and get the one kid def
      Node rez = scope.rez();
      String var = _vars.at(0);
      // If assignment is new, add field
      if( stk.find(var)== -1 )
        stk.add_fld(var,Access.RW,Env.ANY,null);
      scope.mem(new StoreNode(scope.mem(), scope.ptr(), rez, var, Access.RW, null ).peep());
      body().nodes(e);
      return;
    }

    // Mutual-Let-Recursive variables.
    // Start with forward-refs for all.
    _frefs = new Node[_vars._len];
    _oldx = stk.len();
    for( int i=0; i<_vars._len; i++ ) {
      String var = _vars.at(i);
      // If assignment is new, add field
      if( stk.find(var)== -1 )
        stk.add_fld(var,Access.RW,Env.ANY,null);
      ForwardRefNode fref = new ForwardRefNode(var,null).init().keep();
      fref.scope();
      _frefs[i] = fref;
      scope.mem(new StoreNode(scope.mem(), scope.ptr(), fref, var, Access.Final, null ).peep());
    }

    // Make nodes for all the defs; stitching them to the ForwardRefs
    for( int i=0; i<_vars._len; i++ ) {
      _kids.at(i).nodes(e);
      Node def = scope.rez();
      ForwardRefNode fref = _frefs[i].unkeep();
      _frefs[i] = def;
      // Assign def to name
      //stk.set_fld(_vars.at(i), Access.Final,def,true);
      // Close the fref cycle, and remove.
      if( !fref.isDead() ) {
        fref.self();
        fref.close();
        fref.subsume(def);
      }
    }
    _oldx = stk.len();
    // Now the body
    body().nodes(e);
  }

  @Override LetRec redef( String var ) {
    return find(var) != -1 ? this : super.redef(var);
  }

  // Called during AST->node expansion, only mid-definition nodes are non-
  // generative.  Post definition extra defs act like the body and are all
  // let-polymorphic.
  @Override void addNonGen(FreshNode frsh) {
    if( _stk != null )          // If null, nothing is mid-def, so its all fresh
      for( int i=_oldx; i<_stk.len(); i++ )
        if( !_stk.val(i).above_center() )
          frsh.addDef(_stk.in(i));
  }

}
