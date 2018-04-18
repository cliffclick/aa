
Notes
=====

[Want H-M type inference](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system)

TypeVars are a type, whose constant is not yet known.  Need a ptr-to-Type that
gets filled in lazily.  Might need Tarjan U-F?.  2 TypeVars are distinct from
each other.

Type constants include TypeInt (& size variations; theory only deals with
Bottom and not e.g. constants or Top), TypeFlt (32 & 64), tuple types
(eventually named field tuples also, e.g. records), and function types (tuple
for args, a type value for return).  For now:

  * TypeInt32
  * TypeInt64
  * TypeFlt32
  * TypeFlt64
  * TypeTuple: [Type*]
  * TypeFun: TypeTuple -> Type
  
Skipping TypeInt1, TypeInt8, TypeInt16; String;

PolyType: 'forall TypeVar_A ...'.  In my case, I think this is an unbound
TypeVar A, same as Haskell.  In general, there can be lots of unbound TypeVars.
Example:

    bar:A->{B->A} =
      {x -> foo:{B->A} = {y -> x};
            foo};
    bar

In example, `foo` is a function from `y` to `x`, but `y` is ignored.  `x` is
bound outside of `foo`.  Thus `foo` takes any argument, but returns something
of the same type as `x`.  Calling `bar(1)` binds typevar `A` to `Int1` and
returns `foo` typed as `{B->Int1}`; since `B` is unbound, function `foo` takes
any argument and returns an `Int1`.

Contexts: list of pairs from normal variables `x` to types `A`; using Cliffs
normal s-extension for collections, a context is `[xs : As]`.  Contexts in the
wiki are done with *gamma* operator, using the standard List-like notation
`gamma = e (empty) | (gamma, x:A)`, and a Type Judgement is a context with an
expression: `[xs : As] |- e : A` ; with the context `[xs : As]` we can type
expression `e` as `A`.

In our example `foo` is then typed:

    x : A |- {y -> x} : B->A

Where `B` is unbound but `A` is bound to the type of `x`.

Algo W:
-------

if `x` is polytyped `A` in the contexts, replace `A` with a private version to
allow maximal freedom.  The shape of `A` is retained but the leaf variables are
cloned.

if `{x -> e}` then unify the types of `x` and `e`

if `{x -> e}` then give `x` a new typevar `A` and extend the context in `e`,
with `e` being typed as `B` (not new but derived), returning type `{A->B}`

And there's a shortcut for `let` expressions that gives a better typing?

Cliff Notes:
------------

Land of C2, Sea-of-Nodes.  Give all Nodes a Type or a TypeVar, as needed.
Apply constraints/unification, as needed.

So: `x=3; fun={y -> x+y}; fun(2)`

`[A=Int(3)] |- x:A`

`{+}:{Int64,Int64->Int64}`  # {+} is overloaded
`{+}:{Flt64,Flt64->Flt64}`  #
`[B={Int64,Flt64}] |- {+}:{B,B->B}`

    # Abstraction rule
`[A=Int(3),B={Int64,Flt64},C=] |- fun:{y:C -> x:A+y:C}`
`[A=Int(3),B={Int64,Flt64},C=] |- fun:{C -> {B,B->B}(Int(3),C)}`

    # Application of C unifies with B
`[A=Int(3),B={Int64,Flt64}=C] |- {C -> fun:{B,_->B}(Int(3),_)}`
    
    # Application of Int(3) unifies with B
`[A=Int(3),B={Int(3)<=Int64,Flt64}=C] |- fun:{C -> {_,_->B}(_,_)}`

    # Application, just the return
`[A=Int(3),B=C={Int64,Flt64}] |- fun:{B -> B}`


Some C2?
--------

    A = Int_3
    
    x = Con : A
    
    B = {Int64,Flt64}
    
    {+} = Prim+ : {B,B->B}  # Single primnode for both types of +?
    
    C = unbound
    D = unbound
    
    foo = Fun : { C -> D }
            y=Parm : C
              {+}(x,y) : ([A,B],[C,B]) -> B
                Ret : [D,B]
    # Unify args
    [A,B] = [[Int_3,Int64], [Int_3,Flt64]] = [Int_3<=Int64,Int_3 convertsto Flt64]
          = [Int64,Flt64]
    [C,B] = B
    [D,B] = B
    B/C/D all unified
          
    foo = Fun : { B -> B }
            y=Parm : B
              {+}(3,y) : (B,B) -> B
                Ret : B

    foo = Fun : { C -> D }
            y=Parm : C/Any
              {+}(x,y) : ([A,B],[C,B]) -> B
                Ret : [D,B]

Conclusion:
Overloading requires code cloning until the overload resolves
Independent of H-M.

Call({A:Int,B:Flt,C:Str},{A:Int,B:Flt,C:Str} -> {A,B,C}, arg1, arg2)

   TypeSplit(arg1,arg2)
  IntSplit  FltSplit  StrSsplit
x = Call(A:Int->A,arg1,arg2)
y = Call(B:Flt->B,arg1,arg2)
z = Call(C:Str->C,arg1,arg2)
Merge_Overload({x,y,z}{A:Int,B:Flt,C:Str},{A:Int,B:Flt,C:Str} -> {A,B,C})

Users of Merge_Overload pick the overload variant and push-thru going up.
Scalar-users can keep the overload_call directly, act as a merge point

So {+} expands to:
    Fun
      ParmX : A:SCALAR
      ParmY : A:SCALAR
      RPC   : merge of RPCs
      TypeSplit(x,y)
      Int,Int  Flt,Flt  Other,Other
      +:Int    +:Flt    Error
      Region
      Phi(+:Int,+:Flt)
    Ret

And

    x=3; foo={y -> x+y}

Becomes:

    ParmX extends with Int3
    ParmY extends with ParmYY
    RPC extends with e.g. 95
    Call_95 uses Ret with args Int3 and ParmYY : SCALAR

TypeSplit must push up to clone thru Fun merge points as long as incoming types
are superset of outgoing.  Otherwise constant-folds away.
Classic if/splitting: parm/phi merges 2 unrelated values, and TypeSplit if-splits apart

Which comes down to:
do not do int/flt determination lazily, any more, until we have If, and if-splits,
and then type-based if-splits.

And function calls as a version of a merge point to be if-split.

