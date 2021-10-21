package com.cliffc.aa.HM;
//unordered_fields

import com.cliffc.aa.HM.HM.*;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class TestHMMarco {

  @Before public void reset() { HM.reset(); }

  String stripIndent(String s){
    return s.replace("\n","").replace(" ","");
    }
  void fails(String code,String msg) {
    try{HM.hm(code,0,true,false);}
    catch(Throwable t) {
      if(!t.getMessage().startsWith(msg)){
        assertEquals(msg,t.getMessage());
        }
      }
  }
  void ok(String code,String type) {
    Root syn = HM.hm(code,0,true,false);
    assertEquals(stripIndent(type),stripIndent(syn._hmt.p()));
  }

  @Test public void testId() {ok("""
    all={a->a};
    all
    ""","""
    {A->A}
    """);}
  @Test public void testScratch() {ok("""
      all=@{
        id1={a->a}
        id2={a->a}
        };
      all
      ""","""
      @{id1={A->A};id2={B->B}}
      """);}

  @Test public void test51() {ok("""
    total_size = { a as ->
      (if as
        (+ a.size (total_size as .val  as .next))
        a .size
      )};
    total_size
""","""
    { A:@{ size = int64;...} B:@{ next = B; val = A;...}? -> int64 }
""");
    }
  //still need to test some stuff around here
  @Test public void test52() {ok("""
    recF = { a as ->
      (if as
        x = (+ a.size (recF as.val as.next));
        y = (+ a.size (recF as as.next));
        xy = (+ x y);
        (+ xy as.size)
        a.size
      )};
    recF
""","""
    {
    A:@{
      next=B:@{
        next=B;
        size=int64;
        val=A;
        ...
        }?;
      size=int64;
      val=A;
      ...
      }
    B
    ->
    int64
    }
""");
    }
  @Test public void testMyBoolsBase() {ok("""
    void = @{};
    true = @{
      and      = {b -> b}
      or       = {b -> true}
      thenElse = {then else->(then void) }
      };
    false = @{
      and      = {b -> false}
      or       = {b -> b}
      thenElse = {then else->(else void) }
      };
    boolSub ={b ->(if b true false)};
    @{true=(boolSub 1) false=(boolSub 0)}
""","""
    @{
      false = A:@{
        and      = { A -> A };
        or       = { A -> A };
        thenElse = { { () -> B } { () -> B } -> B }
        };
      true = C:@{
        and      = { C -> C };
        or       = { C -> C };
        thenElse = { { () -> D } { () -> D } -> D }
        }
      }
""");}
  @Test public void testMyBoolsRepeatedType() {ok("""
    void = @{};
    true = @{
      and      = {b -> b}
      or       = {b -> true}
      not      = {unused ->true}
      thenElse = {then else->(then void) }
      };
    false = @{
      and      = {b -> false}
      or       = {b -> b}
      not      = {unused ->true}
      thenElse = {then else->(else void) }
      };
    boolSub ={b ->(if b true false)};
    @{true=(boolSub 1) false=(boolSub 0)}
""","""
    @{
      false=A:@{
        and={A->A};
        not={B->A};
        or={A->A};
        thenElse={ {()->C} {()->C}  -> C  }
        };
      true=D:@{
        and={D->D};
        not={E->D};
        or={D->D};
        thenElse={ {()->F} {()->F}  -> F  }
        }
      }
""");}
  @Test public void testMyBoolsNotFalseUndefined() {fails("""
    void = @{};
    true = @{
      and      = {b -> b}
      or       = {b -> true}
      not      = {unused ->false}
      thenElse = {then else->(then void) }
      };
    false = @{
      and      = {b -> false}
      or       = {b -> b}
      not      = {unused ->true}
      thenElse = {then else->(else void) }
      };
    boolSub ={b ->(if b true false)};
    @{true=(boolSub 1) false=(boolSub 0)}
""","Parse error, false is undefined in");}

  //This changed and becomed less precise. Is this what we want?
  @Test public void testMyBoolsSmallType() {ok("""
    all=
      true = @{
        not      = {unused ->all.false}
        thenElse = {then else->(then 5) }
        };
      false = @{
        not      = {unused ->all.true}
        thenElse = {then else->(else 5) }
        };
      boolSub = {b ->(if b all.true all.false)};
      @{true=true false=false boolSub=boolSub};
    all
""","""
    @{
      boolSub={ A?  ->  B:@{
        not={C->B};
        thenElse={  {int64->D} {int64->D}  ->  D }
        }};
      false=B;
      true=B
      }
""");}
  @Test public void testMyBoolsNestedEncoding() {ok("""
    void = @{};
    true =
      false = @{
        and      = {b -> false}
        or       = {b -> b}
        not      = {unused ->true}
        thenElse = {then else->(else void) }
        };
      @{
        and      = {b -> b}
        or       = {b -> true}
        not      = {unused ->false}
        thenElse = {then else->(then void) }
        };
    boolSub ={b ->(if b true (true.not void))};
    @{true=(boolSub 1) false=(boolSub 0)}
""","""
    @{
      false=A:@{
        and={A->A};
        not={
          B ->
          C:@{
            and={C->C};
            not={()->A};
            or={C->C};
            thenElse={ {()->D} {()->D}  ->  D }
            }
          };
        or={A->A};
        thenElse={ {()->E} {()->E} -> E }
        };
      true=F:@{
        and={F->F};
        not={
          G ->
          H:@{
            and={H->H};
            not={()->F};
            or={H->H};
            thenElse={ {()->I} {()->I} -> I }
            }
          };
        or={F->F};
        thenElse={ {()->J} {()->J} -> J }
        }
      }
""");}

  //What is the difference between local variable decs and record field declartions?
  //is there something I can do in one way but not the other?
  @Test public void testBoolsAndNatsFails() {fails("""
    void = @{};
    err  = {unused->(err unused)};
    _true = @{
      and      = {b -> b}
      or       = {b -> true}
      thenElse = {then else->(then void) }
      };
    _false = @{
      and      = {b -> false}
      or       = {b -> b}
      thenElse = {then else->(else void) }
      };
    boolSub ={b ->(if b true false)};
    true=(boolSub 1);
    false=(boolSub 0);
    z = @{
      isZero = {unused ->true}
      pred = err
      succ = {n -> (s n)}
      add = {n-> n}
      };
    orZero = {n ->(true.thenElse n z)};
    s = {pred ->
      self=@{
        isZero = {unused ->false}
        pred = {unused->pred}
        succ = {unused -> (s self)}
        add ={m -> (self.succ (pred.add m))}
        };
      (orZero self)
      };
    @{true=true false=false z=z s=s}
""","Parse error, s is undefined in (s n)");}
//  -So, now we must use master
//  -try the 'one' outside of all. those it still causes unifications?
  @Test public void testBoolsAndNatsTopRecordBrokenSucc() {ok("""
    all=
      void = @{};
      err  = {unused->(err unused)};
      true = @{
        and      = {b -> b}
        or       = {b -> all.true}
        thenElse = {then else->(then void) }
        };
      false = @{
        and      = {b -> all.false}
        or       = {b -> b}
        thenElse = {then else->(else void) }
        };
      boolSub ={b ->(if b true false)};
      z = @{
        isZero = {unused ->all.true}
        pred = err
        succ = {n -> (all.s n)}
        add = {n-> n}
        };
      orZero = {n ->(true.thenElse {unused ->n} {unused ->z})};
      s = {pred ->
        self=@{
          isZero = {unused ->all.false}
          pred = {unused->pred}
          succ = {unused -> (all.s self)}
          add ={m -> (self.succ (pred.add m))}
          };
        (orZero self)
        };
      one =(s z);
      @{true=(boolSub 1) false=(boolSub 0) z=z s=s};
    all
    ""","""
    @{
      false=A:@{
        and={A->A};
        or={A->A};
        thenElse={{()->B}{()->B}->B}
        };
      s={
        C:@{
          add={C->C};
          isZero={D->A};
          pred={E->C};
          succ={C->C}
          }
        ->C
        };
      true=A;
      z=@{
        add={F->F};
        isZero={G->A};
        pred={H->I};
        succ={C->C}
        }
      }
    """/*
    @{
      false=A:@{
        and={A->A};
        or={
          B:@{
            and={A->A};
            or={B->B};
            thenElse={{()->C}{()->C}->C}
            }
          ->B
          };
        thenElse={{()->D}{()->D}->D}
        };
      s={
        E:@{
          add={F->E};
          isZero={G->A};//here is zero will only return a false (also for the input of the succ function)
          pred={H->E};//here predecessor of successor must still be a successor
          succ={E->E}
          }
        ->E
        };
      true=B;
      z=@{//zero.add is correctly typed in a more flexible way then successor:
        add={I->I};//anything into anything
        isZero={J->B};//must be true by the type system
        pred={K->L};
        succ={E->E}//indeed, successor was broken in zero (defined as binary method)
        }
      }
    """*/);}

  static final String goodBaseBool="""
    void = @{};
    err  = {unused->(err unused)};
    true = @{
      and      = {b -> b}
      or       = {b -> all.true}
      thenElse = {then else->(then void) }
      };
   false = @{
      and      = {b -> all.false}
      or       = {b -> b}
      thenElse = {then else->(else void) }
      };
""";
  static final String goodBaseNat="""
    z = @{
      isZero = {unused ->all.true}
      pred = err
      succ = {unused -> (all.s all.z)}
      add = {n-> n}
      };
    s = {pred ->
      self=@{
        isZero = {unused ->all.false}
        pred = {unused->pred}
        succ = {unused -> (all.s self)}
        add    = {m -> ((pred.add m).succ void)}
        };
      self
      };
    one = (s z);
    two = (one.add one);
    three = (s two);
""";
  //        add ={m -> (self.succ (pred.add m))}//old wrong add
  @Test public void testBoolsAndNatsTopRecord() {ok("""
    all=
"""
    +goodBaseBool
    +goodBaseNat+"""
      @{true=true false=false z=z s=s};
    all
""","""
    @{
      false=A:@{
        and={A->A};
        or={A->A};
        thenElse={{()->B}{()->B}->B}
        };
      s={
        C:@{
          add={C->C};
          isZero={D->A};
          pred={E->C};
          succ={()->C}
          }
        ->C
        };
      true=A;
      z=C
      }
""");}
  @Test public void testBoolsBase() {ok("""
    all=
"""
      +goodBaseBool+"""
      @{true=true false=false};
    all
""","""
    @{
      false=A:@{
        and     = {B->A};
        or      = {C->C};
        thenElse= {D {()->E} ->E}
        };
      true=F:@{
        and     = {G->G};
        or      = {H->F};
        thenElse= {{()->I} J ->I}
        }
      }
""");}

  @Ignore
  @Test public void testMiniNat() {ok("""
      void = @{};
      err  = {unused->(err unused)};
      n=
        z = @{
          pred   = err
          succ   = {unused -> (n.s n.z)}
          add    = {o-> o}
          };
        s = {pred ->
          self=@{
            pred   = {unused->pred}
            succ   = {unused -> (n.s self)}
            add    = {m -> ((pred.add m).succ void)}
            };
          self
          };
        @{s=s z=z};
      notZero =@{
          pred   = err
          succ   = {unused -> (n.s n.z)}
          add    = {o-> o}
          nope   = void
          };
      one = (n.s n.z);
      notOne = (one.add notZero);
      notNope = (one.add notZero).nope;
      @{n=n one=one notOne=notOne notNope=notNope}
""",
      """
      @{//strange type for add below
        n=@{//promised to propagate extra fields on the result
          s={//but the runtime does not keep them.
            A:@{//so I tried to make a 'notZero' with an extra 'nope' field.
              add={ B:@{succ={()->B};...} -> B };
              pred={C->A};
              succ={D->A}
              }
            ->A
            };
          z=A
          };//accessing the field fails
        notNope=MissingfieldnopeinA:@{
          add={B:@{succ={()->B};...}->B};
          pred={C->A};
          succ={()->A}
          };//but if you comment the output in the record, again we get no visible type error out :-(
        notOne=E:@{//the computed type of notOne does not respect the promises of the add method.
          add={ F:@{succ={()->F};...}->F };
          pred={G->E};
          succ={()->E}
          };
        one=H:@{//one.add should keep extra fields of the I parameter, but it does not.
          add={I:@{succ={()->I};...}->I};
          pred={J->H};
          succ={K->H}
          }
        }
""");}
  @Test public void testBoolsBaseNatOut() {ok("""
    void = @{};
    err  = {unused->(err unused)};
    b=
      true = @{
        and      = {o -> o}
        or       = {o -> b.true}
        thenElse = {then else->(then void) }
        };
      false = @{
        and      = {o -> b.false}
        or       = {o -> o}
        thenElse = {then else->(else void) }
        };
      @{true=true false=false};
    n=
      z = @{
        isZero = {unused ->b.true}
        pred   = err
        succ   = {unused -> (n.s n.z)}
        add    = {o-> o}
        };
      s = {pred ->
        self=@{
          isZero = {unused ->b.false}
          pred   = {unused->pred}
          succ   = {unused -> (n.s self)}
          add    = {m -> ((pred.add m).succ void)}
          };
        self
        };
      @{s=s z=z};
    notOne = (n.s @{
        isZero = {unused ->b.true}
        pred   = err
        succ   = {unused -> (n.s n.z)}
        add    = {o-> o}
        nope   = void
        });
    one = (n.s n.z);
    two = (one.add one);
    three =(n.s two);
    @{b=b n=n one=one two=two three=three notOne=notOne}
""",
    """
    @{
      b=@{
        false=A:@{
          and={B->A};
          or={C->C};
          thenElse={ D  {()->E}->E }
          };
        true=F:@{
          and={G->G};
          or={H->F};
          thenElse={ {()->I} J ->I}
          }
        };
      n=@{
        s={
          K:@{
            add={
              L:@{ succ={()->L}; ...}
              -> L
              };
            isZero={
              M ->
              N:@{
                and={N->N};
                or={N->N};
                thenElse={ {()->O} {()->O} ->O }
                }
              };
            pred={P->K};
            succ={Q->K}
            }
          ->K
          };
        z=K
        };
      notOne=R:@{
        add={ S:@{succ={()->S};...} -> S};
        isZero={
          T->
          U:@{
            and={U->U};
            or={U->U};
            thenElse={{()->V22} {()->V22}->V22}
            }
          };
        pred={V23->R};
        succ={V24->R}
        };
      one=V25:@{
        add={V26:@{succ={()->V26};...}->V26};
        isZero={
          V27->
          V28:@{
            and={V28->V28};
            or={V28->V28};
            thenElse={{()->V29}{()->V29}->V29}
            }
          };
        pred={V30->V25};
        succ={V31->V25}
        };
      three=V32:@{
        add={V33:@{succ={()->V33};...}->V33};
        isZero={
          V34->
          V35:@{
            and={V35->V35};
            or={V35->V35};
            thenElse={{()->V36}{()->V36}->V36}
            }
          };
        pred={V37->V32};
        succ={()->V32}
        };
      two=V38:@{
        add={V39:@{succ={()->V39};...}->V39};
        isZero={
          V40->
          V41:@{
            and={V41->V41};
            or={V41->V41};
            thenElse={{()->V42}{()->V42}->V42}
            }
          };
        pred={V43->V38};
        succ={()->V38}
        }
      }
"""
    /*"""
    @{
      b=@{
        false=A:@{
          and={B->A};
          or={C->C};
          thenElse={D{()->E}->E}};
        true=F:@{
          and={G->G};
          or={H->F};
          thenElse={{()->I}J->I}
          }
        };
      n=@{
        s={
          K:@{
            add={  L:@{succ={()->L};...}->L  };
            isZero={
              M->
              N:@{
                and={N->N};
                or={N->N};
                thenElse={{()->O}{()->O}->O}
                }
              };
            pred={P->K};
            succ={Q->K}
            }
          ->K
          };
        z=K
        };
      notOne=R:@{
        add={  S:@{succ={()->S};...}->S  };
        isZero={
          T->
          U:@{
            and={U->U};
            or={U->U};
            thenElse={ {()->V21}{()->V21}->V21}
            }
          };
        nope=Missing field nope in A:@{
          add={  B:@{succ={()->B}}->B  };
          isZero={
            C->
            D:@{
              and={D->D};
              or={D->D};
              thenElse={{()->E}{()->E}->E}
              }
            };
          pred={F->A};
          succ={G->A}
          };
        pred={V22->R};
        succ={V23->R}
        };
      one=V24:@{
        add={V25:@{succ={()->V25}}->V25};
        isZero={
          V26->
          V27:@{and={V27->V27};or={V27->V27};thenElse={{()->V28}{()->V28}->V28}}
          };
        pred={V29->V24};
        succ={V30->V24}
        };
      three=V31:@{
        add={V32:@{succ={()->V32}}->V32};
        isZero={
          V33->
          V34:@{and={V34->V34};or={V34->V34};thenElse={{()->V35}{()->V35}->V35}}
          };
        pred={V36->V31};
        succ={()->V31}
        };
      two=V37:@{
        add={V38:@{succ={()->V38}}->V38};
        isZero={
          V39->
          V40:@{and={V40->V40};or={V40->V40};thenElse={{()->V41}{()->V41}->V41}}
          };
        pred={V42->V37};
        succ={()->V37}
        }
      }
      """*/);}

  @Test public void testLists() {ok("""
    all=
"""
    +goodBaseBool//TODO: the concat method looks ill typed
    +goodBaseNat+"""
    empty = @{
      isEmpty = {unused ->all.true}
      pop     = err
      top     = err
      push    = {elem -> (all.cons elem all.empty)}
      concat  = {n-> n}
      size    = {unused ->all.z}
      };
    cons = {elem tail ->
      self=@{
        isEmpty = {unused ->all.false}
        pop     = {unused->tail}
        top     = {unused->elem}
        push    = {elem -> (all.cons elem self)}
        concat  = {m ->
          (((self.pop void).concat m).push (self.top void))
          }
        size    = {unused ->(all.s (tail.size void))}
        };
      self
      };
      @{true=true false=false z=z s=s empty=empty cons=cons};
    all
""","""
    @{
      cons={
        A
        B:@{
          concat={
            C:@{push={A->C};...}
            ->C
            };
          isEmpty={
            D
            ->E:@{
              and     ={E->E};
              or      ={E->E};
              thenElse={{()->F}{()->F}->F}}
            };
          pop={()->B};
          push={A->B};
          size={()->
            G:@{
              add={G->G};
              isZero={H->E};
              pred={I->G};
              succ={()->G}
              }
            };
          top={()->A}
        }
      ->B
      };
    empty=B;
    false=E;
    s={G->G};
    true=E;
    z=G
    }
""");}

  @Test public void testMyBools() {ok("""
    void = @{};
    true = @{
      and = {b -> b}
      or = {b -> true}
      thenElse = {then else->(then void) }
      };
    false = @{
      and = {b -> false}
      or = {b -> b}
      thenElse = {then else->(else void) }
      };
    forceSubtyping ={b ->(if b true false)};
    bool=@{true=(forceSubtyping 1) false=(forceSubtyping 0) force=forceSubtyping};
    a=(bool.false.thenElse {unused->3} {unused->4});
    b=(bool.false.thenElse {unused->@{}} {unused->@{}});
    @{a=a b=b bool=bool}
""","""
    @{
      a=nint8;
      b=();
      bool=@{
        false=A:@{
          and={A->A};
          or={A->A};
          thenElse={ {()->B} {()->B}  ->  B }
          };
        force={C? -> D:@{
          and={D->D};
          or={D->D};
          thenElse={ {()->E} {()->E}  ->  E }
          }};
        true=F:@{
          and={F->F};
          or={F->F};
          thenElse={ {()->G} {()->G}  ->  G }
          }
        }
      }
""");
    }
  }

/*
  data={a:int b:B}->{a:int c:C}->{a:int b:B}->..
  can I pass data to a function expecting
    f ({a:int}->{a:int}..)

    Test T->T? and then apply to A?
    Test linked list loops of different length
    Test numbers
*/
