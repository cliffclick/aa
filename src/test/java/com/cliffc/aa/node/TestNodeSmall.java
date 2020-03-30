package com.cliffc.aa.node;

import com.cliffc.aa.Env;
import com.cliffc.aa.GVNGCM;
import com.cliffc.aa.type.*;
import org.junit.Test;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertEquals;

public class TestNodeSmall {

  private Type[] _testMonotonicChain(Node[] ins, Node n, TypeTuple[] argss) {
    GVNGCM gvn = Env.GVN;
    Type   [] tns= new Type   [argss.length];
    boolean[] bs = new boolean[argss.length];
    for( int i=0; i<argss.length; i++ ) {
      TypeTuple args = argss[i];
      for( int j=0; j<ins.length; j++ )
        gvn.setype(ins[j], args.at(j));
      Type tn = n.value(gvn);
      tns[i] = tn;
      if( i > 0 ) {
        assertTrue(args.isa(argss[i-1])); // Bad test if this fails, argss has to be monotonic
        bs[i] = tn.isa(tns[i-1]);
      }
    }
    for( int i=1; i<argss.length; i++ )
      assertTrue(bs[i]);
    return tns;
  }


  @SuppressWarnings("unchecked")
  @Test public void testCallNode() {
    GVNGCM gvn = Env.GVN;

    // Make a Unknown/CallNode/CallEpi combo.
    // Unwired.  Validate the resolve process and monotonicity.
    gvn._opt_mode=0;
    ConNode ctrl = (ConNode) gvn.xform(new ConNode<>(Type.CTRL));
    UnresolvedNode fp_mul = (UnresolvedNode)Env.top().lookup("*"); // {int int -> int} and {flt flt -> flt}
    UnresolvedNode fp_add = (UnresolvedNode)Env.top().lookup("+"); // {int int -> int} and {flt flt -> flt} and {str str -> str}
    ConNode mem  = gvn.init(new ConNode<>(TypeMem.FULL));
    ConNode arg1 = gvn.init(new ConNode<>(Type.SCALAR));
    ConNode arg2 = gvn.init(new ConNode<>(Type.SCALAR));
    CallNode call = (CallNode)gvn.xform(new CallNode(true, null, ctrl, mem, fp_mul, arg1, arg2));
    CallEpiNode cepi = (CallEpiNode)gvn.xform(new CallEpiNode(call)); // Unwired

    gvn.unreg(call);            // Will be hacking edges
    Node[] ins = new Node[]{ctrl,mem,fp_mul,arg1,arg2};

    TypeFunPtr tfp_mul1 = (TypeFunPtr)fp_mul.value(gvn);
    TypeFunPtr tfp_add1 = (TypeFunPtr)fp_add.value(gvn);
    Type tctl = Type.CTRL, txctl = Type.XCTRL;
    Type tscl = Type.SCALAR, txscl = Type.XSCALAR;
    TypeMem tfull = TypeMem.FULL;
    Type t2 = TypeInt.con(2);
    Type t3 = TypeInt.con(3);
    TypeFunPtr tfp_add_flt = (TypeFunPtr)gvn.type(fp_add.in(0));
    TypeFunPtr tfp_add_int = (TypeFunPtr)gvn.type(fp_add.in(1));
    TypeFunPtr tfp_add_flt_int = (TypeFunPtr)tfp_add_flt.meet(tfp_add_int);

    // iter(), not gcp().  Types always rise.  Very low types might lift to be
    // valid, but e.g. a 2:int will never lift to a str.

    gvn._opt_mode=1;

    // Test this chain of types is monotonic
    call.set_fun(ins[2]=fp_mul,gvn);
    TypeTuple[] argss_mul1 = new TypeTuple[] {
      TypeTuple.make( tctl, tfull, tfp_mul1, tscl , tscl ), // No resolve {int,flt}
      TypeTuple.make( tctl, tfull, tfp_mul1, t2   , tscl ), // No resolve {int,flt}
      TypeTuple.make( tctl, tfull, tfp_mul1, t2   , t3   ), // Both work, but int is cheaper {int}
      TypeTuple.make( tctl, tfull, tfp_mul1, t2   , txscl), // Both work, but int is cheaper {int}
      TypeTuple.make( tctl, tfull, tfp_mul1, txscl, txscl), // Both work, ambiguous, choose neither. {int+flt}
    };
    Type[] tns_mul_iter = _testMonotonicChain(ins,call,argss_mul1);
    BitsFun fidxs_mul_iter0 = ((TypeFunPtr)((TypeTuple)tns_mul_iter[0]).at(2)).fidxs();
    BitsFun fidxs_mul_iter4 = ((TypeFunPtr)((TypeTuple)tns_mul_iter[4]).at(2)).fidxs();
    assertEquals(tfp_mul1.fidxs(),fidxs_mul_iter0); // [13,22] - must handle both
    // TODO: Get picky during iter(); {2,3} resolves to int not flt
    assertEquals(tfp_mul1.fidxs().dual(),fidxs_mul_iter4); // [~13+22] - can choose

    TypeTuple[] argss_mul1x = new TypeTuple[] {
      TypeTuple.make( txctl, tfull, tfp_mul1, tscl , tscl ),
      TypeTuple.make( txctl, tfull, tfp_mul1, t2   , tscl ),
      TypeTuple.make( txctl, tfull, tfp_mul1, t2   , t3   ),
      TypeTuple.make( txctl, tfull, tfp_mul1, t2   , txscl),
      TypeTuple.make( txctl, tfull, tfp_mul1, txscl, txscl),
    };
    _testMonotonicChain(ins,call,argss_mul1x);

    // Test this chain of types is monotonic
    call.set_fun(ins[2]=fp_add,gvn);
    TypeTuple[] argss_add1 = new TypeTuple[] {
      TypeTuple.make( tctl, tfull, tfp_add1, tscl , tscl ), // {int,flt,str}
      TypeTuple.make( tctl, tfull, tfp_add1, t2   , tscl ), // {int,flt} string is excluded
      TypeTuple.make( tctl, tfull, tfp_add1, t2   , t3   ), // {int} flt works, but int is cheaper
      TypeTuple.make( tctl, tfull, tfp_add1, t2   , txscl), // {int} flt works, but int is cheaper
      TypeTuple.make( tctl, tfull, tfp_add1, txscl, txscl), // {int+flt+str}
    };
    Type[] tns_add_iter = _testMonotonicChain(ins,call,argss_add1);
    BitsFun fidxs_add_iter0 = ((TypeFunPtr)((TypeTuple)tns_add_iter[0]).at(2)).fidxs();
    BitsFun fidxs_add_iter1 = ((TypeFunPtr)((TypeTuple)tns_add_iter[1]).at(2)).fidxs();
    BitsFun fidxs_add_iter4 = ((TypeFunPtr)((TypeTuple)tns_add_iter[4]).at(2)).fidxs();
    assertEquals(tfp_add1.fidxs(),fidxs_add_iter0); // [int,flt,str] - must handle all three
    assertEquals(tfp_add_flt_int.fidxs(),fidxs_add_iter1); // [int,flt] - must handle both
    // TODO: Get picky during iter(); {2,3} resolves to int not flt
    assertEquals(tfp_add1.fidxs().dual(),fidxs_add_iter4); // [int+flt+str] - can choose

    TypeTuple[] argss_add1x = new TypeTuple[] {
      TypeTuple.make( txctl, tfull, tfp_add1, tscl , tscl ),
      TypeTuple.make( txctl, tfull, tfp_add1, t2   , tscl ),
      TypeTuple.make( txctl, tfull, tfp_add1, t2   , t3   ),
      TypeTuple.make( txctl, tfull, tfp_add1, t2   , txscl),
      TypeTuple.make( txctl, tfull, tfp_add1, txscl, txscl),
    };
    _testMonotonicChain(ins,call,argss_add1x);


    // Again, now from GCP.  Current design does not vary between GCP or not,
    // but this has changed so often, test both.
    gvn._opt_mode=2;
    TypeFunPtr tfp_mul2 = (TypeFunPtr)fp_mul.value(gvn);
    TypeFunPtr tfp_add2 = (TypeFunPtr)fp_add.value(gvn);

    // Test this chain of types is monotonic
    call.set_fun(ins[2]=fp_mul,gvn);
    TypeTuple[] argss_mul2 = new TypeTuple[] {
      TypeTuple.make( tctl, tfull, tfp_mul2, tscl , tscl ), // Neither work, pick empty[]
      TypeTuple.make( tctl, tfull, tfp_mul2, t2   , tscl ), // Neither work, pick empty[]
      TypeTuple.make( tctl, tfull, tfp_mul2, t2   , t3   ), // Both work, but int is cheaper {int}
      TypeTuple.make( tctl, tfull, tfp_mul2, t2   , txscl), // Both work, can fall to either, no resolve
      TypeTuple.make( tctl, tfull, tfp_mul2, txscl, txscl), // Both work, ambiguous, choose neither. {int+flt}
    };
    Type[] tns_mul_gcp = _testMonotonicChain(ins,call,argss_mul2);
    BitsFun fidxs_mul_gcp0 = ((TypeFunPtr)((TypeTuple)tns_mul_gcp[0]).at(2)).fidxs();
    BitsFun fidxs_mul_gcp4 = ((TypeFunPtr)((TypeTuple)tns_mul_gcp[4]).at(2)).fidxs();
    assertEquals(tfp_mul2.fidxs().dual(),fidxs_mul_gcp0); // [13,22] - must handle both
    // TODO: Get picky during gcp()
    assertEquals(tfp_mul2.fidxs(),fidxs_mul_gcp4); // [~13+22] - can choose

    TypeTuple[] argss_mul2x = new TypeTuple[] {
      TypeTuple.make( txctl, tfull, tfp_mul2, tscl , tscl ), // Neither work, pick empty[]
      TypeTuple.make( txctl, tfull, tfp_mul2, t2   , tscl ), // Neither work, pick empty[]
      TypeTuple.make( txctl, tfull, tfp_mul2, t2   , t3   ), // Both work, but int is cheaper {int}
      TypeTuple.make( txctl, tfull, tfp_mul2, t2   , txscl), // Both work, can fall to either, no resolve
      TypeTuple.make( txctl, tfull, tfp_mul2, txscl, txscl), // Both work, ambiguous, choose neither. {int+flt}
    };
    _testMonotonicChain(ins,call,argss_mul2x);

    // Test this chain of types is monotonic
    call.set_fun(ins[2]=fp_add,gvn);
    TypeTuple[] argss_add2 = new TypeTuple[] {
      TypeTuple.make( tctl, tfull, tfp_add2, tscl , tscl ), // {int,flt,str}
      TypeTuple.make( tctl, tfull, tfp_add2, t2   , tscl ), // {int,flt} string is excluded
      TypeTuple.make( tctl, tfull, tfp_add2, t2   , t3   ), // {int} flt works, but int is cheaper
      TypeTuple.make( tctl, tfull, tfp_add2, t2   , txscl), // {int} flt works, but int is cheaper
      TypeTuple.make( tctl, tfull, tfp_add2, txscl, txscl), // {int+flt+str}
    };
    Type[] tns_add_gcp = _testMonotonicChain(ins,call,argss_add2);
    BitsFun fidxs_add_gcp0 = ((TypeFunPtr)((TypeTuple)tns_add_gcp[0]).at(2)).fidxs();
    BitsFun fidxs_add_gcp1 = ((TypeFunPtr)((TypeTuple)tns_add_gcp[1]).at(2)).fidxs();
    BitsFun fidxs_add_gcp4 = ((TypeFunPtr)((TypeTuple)tns_add_gcp[4]).at(2)).fidxs();
    assertEquals(tfp_add2.fidxs().dual(),fidxs_add_gcp0); // [int,flt,str] - must handle all three
    assertEquals(tfp_add_flt_int.fidxs(),fidxs_add_gcp1); // [int,flt] - must handle both
    // TODO: Get picky during gcp(); {2,3} resolves to int not flt
    assertEquals(tfp_add2.fidxs(),fidxs_add_gcp4); // [int+flt+str] - can choose

    TypeTuple[] argss_add2x = new TypeTuple[] {
      TypeTuple.make( txctl, tfull, tfp_add2, tscl , tscl ),
      TypeTuple.make( txctl, tfull, tfp_add2, t2   , tscl ),
      TypeTuple.make( txctl, tfull, tfp_add2, t2   , t3   ),
      TypeTuple.make( txctl, tfull, tfp_add2, t2   , txscl),
      TypeTuple.make( txctl, tfull, tfp_add2, txscl, txscl),
    };
    _testMonotonicChain(ins,call,argss_add2x);

  }
}

