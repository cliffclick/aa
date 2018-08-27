package com.cliffc.aa.type;

import com.cliffc.aa.node.FunNode;
import com.cliffc.aa.util.Ary;

import java.util.Arrays;

/** Error data type.  If the program result is of this type, the program is not well formed. */
public class TypeErr extends Type<TypeErr> {
  Type _t;                      // Above or below centerline/dual
  private String[] _msgs;       // Collection of errors
  private TypeErr ( Type t, String[] msgs ) { super(TERROR); init(t,msgs); }
  private void init(Type t, String[] msgs ) { _t=t; _msgs=msgs; }
  @Override public int hashCode( ) { return TERROR+_t.hashCode()+Arrays.hashCode(_msgs); }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeErr) ) return false;
    TypeErr t2 = (TypeErr)o;
    return _t==t2._t && Arrays.equals(_msgs,t2._msgs);
  }
  @Override public String toString() { return _t+Arrays.toString(_msgs); }
  private static TypeErr FREE=null;
  @Override protected TypeErr free( TypeErr f ) { FREE=f; return this; }
  public  static Type    make( String msg, Type a, Type b ) { return a==Type.ALL ? a : make(a,String.format(msg,a.toString(),b.toString())); }
  public  static TypeErr make( String msg) { return make(Type.SCALAR,new String[]{msg.intern()}); }
  public  static TypeErr make( Type t, String msg) { return make(t,new String[]{msg.intern()}); }
  private static TypeErr make( Type t, String[] msgs ) {
    assert sorted(msgs);
    assert t!= Type.ALL && t!=Type.ANY; // The limits just fall to the limits
    TypeErr t1 = FREE;
    if( t1 == null ) t1 = new TypeErr(t,msgs);
    else { FREE = null; t1.init(t,msgs); }
    TypeErr t2 = (TypeErr)t1.hashcons();
    return t1==t2 ? t1 : t2.free(t1);
  }

  private static boolean sorted( String[] msgs ) {
    if( msgs.length==0 ) return true;
    String a = msgs[0];
    for( int i=1; i<msgs.length; i++ )
      if( a.compareTo(msgs[i]) >= 0 ) {
        System.out.println("Not sorted: "+Arrays.toString(msgs));
        return false;
      }
    return true;
  }
  
  private static final TypeErr E0 = make(Type. REAL ,"test_err0");
  private static final TypeErr E1 = make(Type.XREAL ,new String[]{"test_err1"});
  private static final TypeErr E2 = make(Type.SCALAR,new String[]{"test_err0","test_err1"});
  
  static final TypeErr[] TYPES = new TypeErr[]{E0,E1,E2};
  @Override protected TypeErr xdual() { return new TypeErr(_t.dual(),_msgs); }
  @Override protected Type xmeet( Type t ) {
    assert t != this;
    if( t._type != TERROR ) {
      Type mt = _t.meet(t);
      if( mt==Type.ALL ) return mt;
      return above_center() ? mt : make(mt,_msgs); // Errors win over non-errors
    }
    TypeErr te = (TypeErr)t;
    Type mt = _t.meet(te._t);
    if( mt==Type.ALL ) return mt;
    
    if( !_t.above_center() && !te._t.above_center() ) { // both low; Union
      String[] ss = Arrays.copyOf(_msgs,_msgs.length+te._msgs.length);
      System.arraycopy(te._msgs,0,ss,_msgs.length,te._msgs.length);
      Arrays.sort(ss);
      int i,j;
      for( i=1,j=0; i<ss.length; i++ )
        if( ss[i]!=ss[j] ) ss[++j]=ss[i];
      if( j+1<i ) ss = Arrays.copyOf(ss,j+1);
      return make(mt,ss);
    } if( mt.above_center() ) { // both high, Intersect
      Ary<String> as = new Ary<>(new String[0]);
      for( int i=0,j=0; i<_msgs.length && j<te._msgs.length; ) {
        if( _msgs[i]==te._msgs[j] ) { as.add(_msgs[i]); i++; j++; }
        else if( _msgs[i].compareTo(te._msgs[j]) < 0 ) i++;
        else j++;
      }
      if( as.isEmpty() ) return make(mt,new String[]{_msgs[0],te._msgs[0]});
      return make(mt,as.asAry());
    } else {
      return above_center() ? te : this; // Return the one low
    }
  }

  @Override public boolean above_center() { return _t.above_center(); }
  @Override public boolean may_be_con() { return above_center(); }
  @Override public byte isBitShape(Type t) { return !above_center() && this!=ALL ? (byte)99 : -1; }
  @Override public String errMsg() {
    if( above_center() ) return null;
    if( _t.is_forward_ref() ) { // Forward/unknown refs as args to a call report their own error
      // If _t, then expect "file:line:(typetuple) is not a type\nsource_text\n    ^"
      // Replace "(typetuple) is not a type\n" with "Unknown ref 'xxx'"
      String s = _msgs[0];
      int idx0 = s.indexOf('(');
      int idx1 = s.indexOf('\n',1);
      String s0 = s.substring(0,idx0);
      String s2 = s.substring(idx1,s.length());
      return s0+"Unknown ref '"+ FunNode.name(((TypeTuple)_t).get_fun().fidx())+"'"+s2;
    }
    if( _msgs.length==1 ) return _msgs[0];
    return _msgs[0];            // Just the first error
    //return Arrays.toString(_msgs);
  }
}
