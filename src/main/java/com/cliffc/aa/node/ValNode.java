 package com.cliffc.aa.node;

 import com.cliffc.aa.tvar.TV2;
 import com.cliffc.aa.type.*;
 import com.cliffc.aa.util.Ary;

 import java.util.Collection;

 import static com.cliffc.aa.AA.*;


// Values.  Values mimic a NewObj for a "class" wrapper around some primitives.
// All fields are final, so no Stores and no need to track memory.  Values have
// no identity (e.g. a "3" is a "3" is a "3").  Named types can be passed to
// Loads directly; Loads against fields are honored "as if" the named type is
// both a pointer and a memory.  Loads against fields not in the core ValNode
// use the Type name to get the class via a global flat lookup table; then the
// Load repeats against those fields.
public class ValNode extends ValFunNode {
  final String _tname;          // Type name
  final int _alias;             // Alias as a prototype object
  String[] _flds;  // Map from node inputs to local field names; slot 0 is null for the prototype
  int _fidx;       // FIDX as a constructor function
  TypeFunPtr _tfp; // Type as a constructor function

  private ValNode(String tname, int alias) {
    super(OP_VAL);
    _tname= tname;
    _alias= alias;
    _flds = null;
    _fidx = 0;
    _tfp  = null;
  }

  @Override public String xstr() { return _defs._len==0 ? "fref_default_"+_tname : proto()._ts._name; }
  @Override int nargs() { return _flds==null ? -1 : _flds.length-1+ARG_IDX; }
  NewNode proto() { return (NewNode)in(0); }
  @Override int fidx() { return _fidx; }
  @Override Type formal(int idx) {
    Node formal = in(idx-DSP_IDX);
    assert formal instanceof ConNode && !((ConNode)formal)._t.is_con();
    return ((ConNode)formal)._t;
  }
  @Override String name() { throw unimpl(); }

  @Override public boolean equals(Object o) {
    if( this==o ) return true;
    if( _flds==null ) return false; // Forward-ref defaults never CSE
    return super.equals(o);
  }

  @Override public Type value() {
    if( _flds==null ) return TypeMemPtr.make(_alias,TypeStruct.ISUSED.set_name(_tname));
    TypeStruct ts = TypeStruct.malloc(proto()._ts._name,false);
    for( int i=1; i<_flds.length; i++ )
      ts.add_fld( TypeFld.make(_flds[i],val(i),TypeFld.Access.Final,i-1+ARG_IDX) );
    ts = ts.hashcons_free();
    return TypeMemPtr.make(_alias,ts);
  }
  @Override public TypeMem all_live() { return TypeMem.ALIVE; }

  @Override public boolean unify( boolean test ) {
    TV2 self = tvar();
    TV2 proto = proto().tvar();
    if( proto.is_leaf() ) return false; // Wait for proto to advance
    if( self.is_leaf() ) {              // Become a copy of proto
      if( test ) return true;
      TV2 tv2 = TV2.make_struct(proto(),"ValNode_unify");
      for( int i=1; i<_flds.length; i++ )
        tv2._args.put(_flds[i],tvar(i));
      return self.unify(tv2,test);
    }

    // Unify existing fields.  Ignore extras on either side.
    boolean progress=false;
    for( int i=1; i<_flds.length; i++ ) {
      TV2 tvfld = self.arg(_flds[i]);
      if( tvfld != null ) progress |= tvfld.unify(tvar(i),test);
      if( test && progress ) return true; // Fast cutout if testing
    }
    return progress;
  }

  // Make a 'blank' forward-ref ValNode.  This will eventually become a default
  // ValNode for this entire class of ValNodes.
  public static ValNode make_default(String tok, int alias) {
    return new ValNode((tok+":").intern(),alias);
  }
  // Build a ValNode default constructor from the NewNode.  Walk all fields.
  // If the field is ANY (dead f-ref), ignore it.
  // If the field is MUTABLE, it was a default set; make it immutable and a
  // required constructor arg.
  // If the final field  is_con, leave it in the prototype object.
  // If the final field !is_con, need a normal function constructor NOT a ValNode.

  // With the default constructor in hand, walk all the final function fields
  // and reset their displays from the prototype (with full type info) to the
  // default ValNode (which is ALSO the default constructor) (with a limited
  // set of type info).  Goal: remove O(n^2) pattern of extra type info.
  public void fill_default(NewNode proto) {
    assert _flds==null && _fidx==0 && _tfp==null; // One-time fill in
    Ary<String> flds = new Ary<>(new String[1],0);
    flds.push(null);            // Prototype in slot 0
    // Walk fields looking for RW; these require a constructor argument.
    Collection<TypeFld> oflds = proto._ts.osorted_flds();
    for( TypeFld fld : oflds ) {
      Type pt = proto.val(fld._order);
      if( fld._access==TypeFld.Access.RW ) {
        if( !(proto.in(fld._order) instanceof ConNode) )
          throw unimpl();   // Not a default constructed; "fld := init" mutable not allowed in Val
        flds.push(fld._fld);
        continue;
      }
      // Final field set by a constant value
      if( (pt==Type.ANY ||            // Dead
           pt.is_con() ||             // Find class constants in the prototype
           pt instanceof TypeFunPtr ) )// Includes e.g. instance methods
        continue;                    // Leave in prototype
      throw unimpl();      // Non-constant field, needs a full constructor function to compute
    }

    // Fill in the constructor shortcut.  Just sets the non-constant fields.
    add_def(proto);         // Prototype in slot 0
    for( TypeFld fld : oflds )  // Gather remaining RW fields for constructor
      if( fld._access==TypeFld.Access.RW )
        add_def(con(fld._t));
    proto._nargs = flds._len-1+ARG_IDX;
    // Fill in a constructor function type
    _flds = flds.asAry();   //
    _fidx = BitsFun.new_fidx(BitsFun.ALL);
    _tfp = TypeFunPtr.make(BitsFun.make0(_fidx),nargs(),TypeMemPtr.NO_DISP,proto._ts);
    FUNS.setX(_fidx,this);
  }

}
