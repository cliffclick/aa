# aa

Cliff Click Language Hacking
============================

**To-the-metal performance:** every abstraction used can be peeled away,
yielding code that you would expect from a tightly written low-level program.
This is a primary driver for me, the guy who's been writing compilers for high
performance computing (including Java) all my life.  Ease-of-programming is a
close second, but only after you've declared that performance is not your main
goal.  Hence I support syntactic sugar on expensive operations (e.g.
accidental auto-boxing in a hot loop can cost you 10x in speed) but only if the
type-system cannot remove it and you've not declared that you are programming
for speed.

**Modern:** Statically typed.  Functional programming with full-strength type
inference - types are everywhere optional.  Minimal syntax.  REPL
(i.e. incremental static typing) and seperate compilation.  Typed C-style
macros: most syntax errors in dead code are typed.

My intent is a modern language that can be used where C or C++ is used: low-level
high-performance work and a systems implementation language (e.g. OS's, device
drivers, GC's), but bring in all the goodness of the last 20 years of language
improvements.

The language is intended to "look like" C or Java, but with all types optional
and all keywords removed.  The whole no-keywords thing is an experiment I may
back away from; a primary goal is to be *readable* - sometimes keywords feel
like clutter and sometimes they are an code-anchor for your scanning eye.

I specifically intend to look at real-time constraints and the notion of Time
in a language.

Part of modern coding is the use Garbage Collection and the structured use of
malloc/free - so I intend to add Rust-style memory management.

Part of modern coding is the use of multiple cores, so I intend to explore a
couple of different concurrency models.  A notion of a true 'final' field, made
with a final-store (as opposed to declared as a final type) - you can make
cyclic final structures, and once final all future reads will see the final
value.  No odd exceptions for "early publishing" a pointer.

And of course, this is a Work-In-Progress!!!!



GRAMMAR
-------

BNF                           | Comment
---                           | -------
`prog = stmts END`            |
`stmts= [tstmt or stmt][; stmts]*[;]?` | multiple statments; final ';' is optional
`tstmt= tvar = :type`         | type variable assignment
`stmt = [id[:type] [:]=]* ifex` | ids are (re-)assigned, and are available in later statements.  
`stmt = ^ifex`                | Early function exit
`ifex = apply [? stmt [: stmt]]` | trinary logic; the else-clause will default to 0
`apply= expr  | expr expr*`   | Lisp-like application-as-adjacent
`expr = term [binop term]*`   | gather all the binops and sort by prec
`term = uniop term`           | Any number of uniops
`term = id++ | id--`          |   post-inc/dec operators
`term = tfact post`           |   A term is a tfact and some more stuff...
`post = empty`                | A term can be just a plain 'tfact'
`post = (tuple) post`         | Application argument list
`post = .field post`          | Field and tuple lookup
`post = .field [:]= stmt`     | Field (re)assignment.  Plain '=' is a final assignment
`post = .field++ OR .field--` | Field reassignment.
`tfact= fact[:type]`          | Optionally typed fact
`fact = id`                   | variable lookup
`fact = num`                  | number
`fact = "string"`             | string
`fact = (stmts)`              | General statements parsed recursively
`fact = tuple`                | Tuple builder
`fact = func`                 | Anonymous function declaration
`fact = @{ stmts }`           | Anonymous struct declaration; assignments declare fields
`fact = {binop}`              | Special syntactic form of binop; no spaces allowed; returns function constant
`fact = {uniop}`              | Special syntactic form of uniop; no spaces allowed; returns function constant
`tuple= (stmts,[stmts,])`     | Tuple; final comma is optional
`binop= +-*%&/<>!= [] ]=`     | etc; primitive lookup; can determine infix binop at parse-time, also pipe but GFM screws up
`uniop= -!~ []`               | etc; primitive lookup; can determine infix uniop at parse-time
`func = { [id[:type]* ->]? stmts}` | Anonymous function declaration, if no args then the -> is optional
`str  = [.\%]*`               | String contents; \t\n\r\% standard escapes
`str  = %[num]?[.num]?fact`   | Percent escape embeds a 'fact' in a string; "name=%name\n"
`type = tcon OR tvar OR tfun[?] OR tstruct[?] OR ttuple[?]` | // Types are a tcon or a tfun or a tstruct or a type variable.  A trailing ? means 'nilable'
`tcon = int, int[1,8,16,32,64], flt, flt[32,64], real, str[?]` | Primitive types
`tfun = {[[type]* ->]? type }` | Function types mirror func decls
`ttuple = ([[type],]* )`      | Tuple types are just a list of optional types; the count of commas dictates the length, zero commas is zero length.  Tuples are always final.
`tmod = := | = | ==`          | ':=' or '' is r/w, '=' is final, '==' is r/w
`tstruct = @{ [id [tmod [type?]],]*}` | Struct types are field names with optional access and optional types.  Spaces not allowed
`tvar = id`                   | Type variable lookup 

SIMPLE EXAMPLES
---------------

Code            | Comment
----            | -------
`1`             | ` 1:int`
Prefix unary operator | ---
`-1`            | ` -1:int` application of unary minus to a positive 1
`!1`            | `  0:int` convert 'truthy' to false
Infix binary operator | ---
`1+2`           | `  3:int`
`1-2`           | ` -1:int`
`1<=2`          | `1:int` Truth === 1
`1>=2`          | `0:int` False === 0
Binary operators have precedence | ---
`1+2*3`         | `  7:int` standard precedence
` 1+2 * 3+4 *5` | ` 27:int`
`(1+2)*(3+4)*5` | `105:int` parens overrides precedence
`1// some comment`<br>`+2`  | `3:int` with bad comment
`1 < 2`         | `1:int` true  is 1, 1 is true
`1 > 2`         | `0:int` false is 0, 0 is false
Float           | ---
`1.2+3.4`       | `4.6:flt`
`1+2.3`         | `3.3:flt` standard auto-widening of int to flt
`1.0==1`        | `1:int` True; int widened to float
Simple strings  | ---
`"Hello, world"`| `"Hello, world":str`
`str(3.14)`     | `"3.14":str` Overloaded `str(:flt)`
`str(3)`        | `"3":str`    Overloaded `str(:int)`
`str("abc")`    | `"abc":str`  Overloaded `str(:str)`
Variable lookup | ---
`math_pi`       | `3.141592653589793:flt` Should be `math.pi` but name spaces not implemented
primitive function lookup | ---
`+`             | `"Syntax error; trailing junk"` unadorned primitive not allowed
`{+}`           | `{{+:{int int -> int}, +:{flt flt -> flt}}` returns a union of '+' functions
`{!}`           | `!:{int -> int1}` function taking an `int` and returning a `bool`
Function application, traditional paren/comma args | ---
`{+}(1,2)`      | `3:int`
`{-}(1,2)`      | `-1:int` binary version
`{-}(1)`        | `-1:int` unary version
Errors; mismatch arg count | ---
`!()`           | `Call to unary function '!', but missing the one required argument`
`math_pi(1)`    | `A function is being called, but 3.141592653589793 is not a function type`
`{+}(1,2,3)`    | `Passing 3 arguments to +{flt64 flt64 -> flt64} which takes 2 arguments`
Arguments separated by commas and are full statements | ---
`{+}(1, 2 * 3)` | `7:int`
`{+}(1 + 2 * 3, 4 * 5 + 6)` | `33:int`
`(1;2 )`        | `2:int` just parens around two statements
`(1;2;)`        | `2:int` final semicolon is optional
`{+}(1;2 ,3)`   | `5:int` full statements in arguments
Syntax for variable assignment | ---
`x=1`           | `1:int` assignments have values
`x:=1`          | `1:int` Same thing, not final
`x=y=1`         | `1:int` stacked assignments ok
`x=y=`          | `Missing ifex after assignment of 'y'`
`x=1+y`         | `Unknown ref 'y'`
`x=2; y=x+1; x*y` | `6:int`
`1+(x=2*3)+x*x` | `43:int` Re-use ref immediately after def; parses as: `x=(2*3); 1+x+x*x`
`x=(1+(x=2)+x)` | `Cannot re-assign ref 'x'`
`x=(1+(x:=2)+x)` | `5:int` RHS executes first, so parses as: `x:=2; x=1+x+x`
`x++`           | `0:int` Define new variable as 0, and return it before the addition
`x:=0; x++; x`  | `1:int` Define new variable as 0, then add 1 to it, then return it
`x++ + x--`     | `1:int` Can be used in expressions
Conditionals    | ---
`0 ?    2  : 3` | `3:int` Zero is false
`2 ?    2  : 3` | `2:int` Any non-zero is true; "truthy"
`math_rand(1)?(x=4):(x=3);x` | `:int8` x defined on both arms, so available after but range bound
`math_rand(1)?(x=2):   3 ;4` | `4:int` x-defined on 1 side only, but not used thereafter
`math_rand(1)?(y=2;x=y*y):(x=3);x` | `:int8` x defined on both arms, so available after, while y is not
`math_rand(1)?(x=2):   3 ;x` | `'x' not defined on false arm of trinary` No partial-defs
`math_rand(1)?(x=2):   3 ;y=x+2;y` | `'x' not defined on false arm of trinary` More complicated partial-def
`math_rand(1)?1` | `:int1` Can skip last arm, will default to 0
`x:=0; math_rand(1) ? x++; x` | `:int1` Side effects in the one arm
`0 ? (x=2) : 3;x` | `'x' not defined on false arm of trinary`
`2 ? (x=2) : 3;x` | `2:int` Off-side is constant-dead, so missing x-assign is ignored
`2 ? (x=2) : y  ` | `2:int` Off-side is constant-dead, so `"Unknown ref 'y'"` is ignored
`x=1;2?(x=2):(x=3);x` | `Cannot re-assign ref 'x'` Re-assignment not allowed
`x=1;2?   2 :(x=3);x` | `1:int` Re-assign allowed & ignored in dead branch
`math_rand(1)?1:int:2:int` | `:int8` no ambiguity between conditionals and type annotations
`math_rand(1)?1::2:int` | `missing expr after ':'`
`math_rand(1)?1:"a"` | `Cannot mix GC and non-GC types`
`math_rand(1)?(x:=4):(x:=3);x` | `:int8` x mutably defined on both arms, so available after
`math_rand(1)?(x:=4):(x:=3);x:=x+1`| `:int64` x mutably defined on both arms, so mutable after
`x:=0; math_rand(1) ? (x:=4):3; x:=x+1` | `:int8`  x partially updated, remains mutable after
`x:=0; 1 ? (x =4):; x` | `4:int8` x final on 1 arm, dead on other arm, so final after
`x:=0; math_rand(1) ? (x =4):3; x` | `'x' not final on false arm of trinary` Must be fully final after trinary
Anonymous function definition | ---
`{x y -> x+y}`    | Types as a 2-arg function { int int -> int } or { flt flt -> flt }
`{5}()`           | `5:int` No args nor `->` required; this is simply a no-arg function returning 5, being executed
Identity mimics having type-vars via inlining during typing | ---
`id`              | `{A->A}` No type-vars yet
`id(1)`           | `1:int`
`id(3.14)`        | `3.14:flt`
`id({+})`         | `{{+:{int int -> int}, +:{flt flt -> flt}}`
`id({+})(id(1),id(math_pi))` | `4.141592653589793:flt`
Function execution and result typing | ---
`x=3; andx={y -> x & y}; andx(2)` | `2:int` capture external variable
`x=3; and2={x -> x & 2}; and2(x)` | `2:int` shadow  external variable
`plus2={x -> x+2}; x` | `Unknown ref 'x'` Scope exit ends lifetime
`fun={x -> }`     | `Missing function body`
`mul3={x -> y=3; x*y}; mul3(2)` | `6:int` // multiple statements in func body
`x=3; addx={y -> x+y}; addx(2)` | `5:int` Overloaded `+` resolves to `:int`
`x=3; mul2={x -> x*2}; mul2(2.1)` | `4.2:flt` Overloaded `{+}:flt` resolves with I->F conversion
`x=3; mul2={x -> x*2}; mul2(2.1)+mul2(x)` | `10.2:flt` Overloaded `mul2` specialized into int and flt variants
`sq={x -> x*x}; sq 2.1` | `4.41:flt` No `()` required for single args
Type annotations  | ---
`-1:int`          | `-1:int`
`(1+2.3):flt`     | `3.3:flt`  Any expression can have a type annotation
`x:int = 1`       | `1:int`  Variable assignment can also have one
`x:flt = 1`       | `1:int` Casts for free to a float
`x:flt32 = 123456789` | `123456789 is not a flt32` Failed to convert int64 to a flt32
`1:`              | `Syntax error; trailing junk` Missing type
`-1:int1`         | `-1 is not a int1` int1 is only {0,1}
`"abc":int`       | `"abc" is not a int64`
`x=3; fun:{int -> int} = {x -> x*2}; fun(2.1)+fun(x)` | `2.1 is not a int64`
`x=3; fun:{real -> real} = {x -> x*2}; fun(2.1)+fun(x)` | `10.4:flt` real covers both int and flt
`fun:{real->flt32} = {x -> x}; fun(123 )` | `123:int` Casts for free to real and flt32
`fun:{real->flt32} = {x -> x}; fun(123456789)` | `123456789 is not a flt32`
`{x:int -> x*2}(1)` | `2:int` types on parmeters too
`{x:str -> x}(1)`   | `1 is not a str`
Recursive and co-recursive functions | ---
`fact = { x -> x <= 1 ? x : x*fact(x-1) }; fact(3)` | `6:int` fully evaluates at typing time
`fib = { x -> x <= 1 ? 1 : fib(x-1)+fib(x-2) }; fib(4)` | `:int` does not collapse at typing time
`is_even = { n -> n ? is_odd(n-1) : 1}; is_odd = {n -> n ? is_even(n-1) : 0}; is_even(4)` | `1:int`
`is_even = { n -> n ? is_odd(n-1) : 1}; is_odd = {n -> n ? is_even(n-1) : 0}; is_even(5)` | `0:int`
Simple anonymous tuples | ---
`(1,\"abc\").0` | `1:int`  .n loads from the nth field; only parse-time constants are supported
`(1,\"abc\").1` | `"abc"`
Simple anonymous structures | ---
`  @{x;y}`        | `@{x,y}` Simple anon struct decl
`a=@{x=1.2;y}; x` | `Unknown ref 'x'` Field name does not escape structure
`a=@{x=1;x=2}`    | `Cannot define field '.x' twice`
`a=@{x=1.2;y;}; a.x` | `1.2:flt` Standard "." field name lookups; trailing semicolon optional
`(a=@{x;y}; a.)`  | `Missing field name after '.'`
`a=@{x;y}; a.x=1` | `Cannot re-assign field '.x'` No reassignment yet
`a=@{x=0;y=1}; b=@{x=2}; c=math_rand(1)?a:b; c.x` | `:int8` Either 0 or 2; structs can be partially merged and used
`a=@{x=0;y=1}; b=@{x=2}; c=math_rand(1)?a:b; c.y` | `Unknown field '.y'` Used fields must be fully available
`dist={p->p.x*p.x+p.y*p.y}; dist(@{x=1})` | `Unknown field '.y'`  Field not available inside of function
`dist={p->p.x*p.x+p.y*p.y}; dist(@{x=1;y=2})` | `5:int` Passing an anonymous struct OK
`dist={p->p.x*p.x+p.y*p.y}; dist(@{x=1;y=2;z=3})` | `5:int` Extra fields OK
`dist={p:@{x,y} -> p.x*p.x+p.y*p.y}; dist(@{x=1;y=2})` | `5:int` Structure type annotations on function args
`a=@{x=(b=1.2)*b;y=b}; a.y` | `1.2:flt`  Temps allowed in struct def
`a=@{x=(b=1.2)*b;y=x}; a.y` | `1.44:flt` Ok to use early fields in later defs
`a=@{x=(b=1.2)*b;y=b}; b` | `Unknown ref 'b'`  Structure def has a lexical scope
`dist={p->p//qqq`<br>`.//qqq`<br>`x*p.x+p.y*p.y}; dist(//qqq`<br>`@{x//qqq`<br>`=1;y=2})` | `5:int`  Some rather horrible comments
Named type variables | Named types are simple subtypes
`gal=:flt`        | `gal{flt -> gal:flt}` Returns a simple type constructor function
`gal=:flt; {gal}` | `gal{flt -> gal:flt}` Operator syntax for the function
`gal=:flt; 3==gal(2)+1` | `1:int` Auto-cast-away `gal` to get a `flt`
`gal=:flt; tank:gal = gal(2)` | `2:gal` 
`gal=:flt; tank:gal = gal(2)+1` | `3.0 is not a gal:flt` No-auto-cast into a `gal`
`Point=:@{x,y}; dist={p:Point -> p.x*p.x+p.y*p.y}; dist(Point(1,2))` | `5:int` type variables can be used anywhere a type can, including function arguments
`Point=:@{x,y}; dist={p       -> p.x*p.x+p.y*p.y}; dist(Point(1,2))` | `5:int` this `dist` takes any argument with fields `@{x;y}`, `Point` included
`Point=:@{x,y}; dist={p:Point -> p.x*p.x+p.y*p.y}; dist(@{x=1;y=2})` | `@{x:1,y:2} is not a Point:@{x,y}` this `dist` only takes a `Point` argument
Nilable and not-nil modeled after Kotlin | ---
`x:str? = 0`      | `nil`  question-type allows nil or not; zero digit is nil
`x:str? = "abc"`  | `"abc":str` question-type allows nil or not
`x:str  = 0`      | `"nil is not a str"`
`math_rand(1)?0:"abc"` | `"abc"?` Nil-or-string "abc"
`(math_rand(1)?0 : @{x=1}).x` | `Struct might be nil when reading field '.x'` Must be provable not-nil
`p=math_rand(1)?0:@{x=1}; p ? p.x : 0` | `:int1` not-nil-ness after a nil-check, so field de-ref is OK
`x:int = y:str? = z:flt = 0` | `0:int` nil/0 freely recasts
`"abc"==0`        | `0:int` Compare vs nil
`"abc"!=0`        | `1:int` Compare vs nil
`nil=0; "abc"!=nil` | `1:int` Another name for 0/nil
`a = math_rand(1) ? 0 : @{x=1}; b = math_rand(1) ? 0 : @{c=a}; b ? (b.c ? b.c.x : 0) : 0` | `int1` Nested nilable structs
Recursive types   | ---
`A= :(A?, int); A((0,2))`|`A:(nil,2)` Simple recursive tuple
`A= :(A?, int); A(0,2)`|`A:(nil,2)` Same thing using explicit args
`A= :(A?, int); A(A(0,2),3)`|`A:(A:(nil,2),3)` Simple recursive tuple
`A= :@{n:A?, v:flt}; A(@{n=0;v=1.2}).v` | `1.2:flt` Named recursive structure
`A= :@{n:A?, v:flt}; A(0,1.2).v` | `1.2:flt` Same thing using explicit args
`A= :@{n:B?, v:int}; a = A(0,2); a.n` | `nil` Unknown type B is never assigned, so no type error
`A= :@{n:B, v:int}; B= :@{n:A, v:flt}` | `B(@{n:A:@{n:B, v:int},v:flt} -> B)`  Types A and B are mutually recursive
`List=:@{next:List?,val}` | `List` Linked-list type
`List(List(0,1.2),2.3)` | `List:@{next:List:@{next:nil;val:1.2};val:2.3}` Sample linked-list, with all types shown
`map_sq={x -> x ? (map_sq(x.0),x.1*x.1) : 0}; map_sq((0,1.2))` | `(nil,1.44)` Strongly typed `map_sq` with a simple tuple
`map={tree fun -> tree ? @{l=map(tree.l,fun);r=map(tree.r,fun);v=fun(tree.v)} : 0}` | Map a function over a tree in postfix order
Final fields are made with a final store not a final declaration | ---
`x=1`             | `1:int` Final local variable
`x:=1`            | `1:int` Non-final local variable
`x:=0; a=x; x:=1; (a,x)` | `(0,1)` Reassign local variable
`x=1; x:=2`       | `Cannot re-assignal final val 'x'`
`math_rand(1)?(x:=4):(x:=3);x:=x+1` | `int`  x mutable on both arms, so mutable after
`x:=0; 1?(x=4):; x` | `4` x final on 1 arm, dead on other arm
`x:=0; math_rand(1) ? (x =4):3; x` | `'x' not final on false arm of trinary` Must be marked final on both arms, or dead on one.
`x=@{n:=1;v:=2}`  | `@{n:=1;v:=2` Mutable field declaration and initial writes
`x=@{n =1;v:=2}; x.n=3` | `Cannot re-assign read-only field '.n'` Field initialized as final/read-only, cannot be changed
`ptr0=@{p:=0;v:=1}; ptr1=@{p=ptr0;v:=2}; ptr0.p=ptr1; ptr0.p.v+ptr1.p.v` | `3:int` final pointer-cycle is ok
`ptr2rw = @{f:=1}; ptr2final:@{f=} = ptr2rw; ptr2final` |  `*@{f:=1} is not a *{f=}`  Cannot cast-to-final, can only make finals with a store


LARGER EXAMPLES:
----------------

Build a list from tuples; first element is payload and second element is the rest of the list, with nil terminating the list:
```C
  lst = (1,(2,(3,0)))
```

Find and return the first element of a list passing a predicate:
```C
find = { list pred ->     // find is a 2-arg function
  !list ? ^0;             // if list is nil, return nil
  pred(list.0) ? ^list.0; // if the 0-element passes the predicate, return it
  find(list.1,pred);      // otherwise, recursively find on the rest of the list
}
```

Find the first odd element:
```C
find(lst,{e -> e&1})
```
...which returns `1`.


Here is a simple `map` call, mapping `fun` over the list elements:
```C
map = { list fun ->                // map is a 2-arg function
  list                             // list is nil-checked
  ? (map(fun,list.1),fun(list.0))  // return a list (tuple) composed of apply map to the 1-element and fun to the 0-element
  : 0                              // return a nil
}
```

Double the list elements:
```C
map(lst,{x -> x+x})
```
Returns `(2,(4,(6,0)))`.

Both `map` and `+` calls are generic, so a list of strings work as well:
```C
map( ("abc", ("def", 0)), {x -> x+x} )
```
Returns `("abcabc", ("defdef", 0))`.


Done Stuff
----------

* Static typing; types optional & fully inferred at every place.
* Nil-ptr distinguished; nil/notnil types (e.g. Kotlin)
* Duck-typing.  Interfaces.
* Anonymous (and named) structure types.
* Functional; 1st class functions.  All functions are anonymous.
* REPL
* Dynamic code-gen; no seperate compilation step.  Load Source & Go.
* Limited overloads.
* Overloading ops.  No ambiguity / easy-to-read rules.
* By default multi-arg ops are overloaded.
* Direct SSA style code writing; no 'let' keyword.
* default "x=1" makes a "val" until scope runs out (cannot re-assign)
* Reassignment "x:=1" for mutable variables
* Primitive values; int overflow OK;
* Sub-byte ranges.  Julia-like math typing.
* Can type-name primitives, but no e.g. physical-unit-type math


Ideas, Desirables
-----------------

* H-M style typing.
* JIT'ing.
* {GC,Ref-Counting}: Ponder both vs requiring e.g. lifetime management (easy by just raising scope).
* No exceptions?!!?  Same as Elm: allow tagged union returns with an error return
  vs a non-error return.  Force user to handle errors up&down the stack.
* Lexical scope destructors.
* Can ask for Int for BigInteger; unboxed arrays.
* Pattern-matching too handy looking, need to have it
* Parallel (and distributed) but also deterministic
* "eval"
* Monads?  i/o, side-effect monads.

lifetime:

* Distributed ref-cnting?  (or Dist-GC?)
* Ref-Counting does NOT given "immediate" destructor execution, but "soon".
* Guaranteed to count down & release before the next instance of exact same constructor constructs?
* Guaranteed to count down & release before the next loop backedge?  Before base of containing loop?
* Built-in "pools" for bulk-remove?  Same as ref-counting.
* Rust-style memory lifetime management; linear logic owner; borrowing; guaranteed death

concurrency:

* Pony-style concurrency management
* CAS built-in lang primitive: 'res := atomic(old,new)'; JMM
* CPS for threads/concurrency;
* not really actors but spawn/fork worker threads, run until they 'join' with parent.
* Transactions-for-shared-memory-always (Clojure style)

types and name spaces and nils:

* OOP namespaces (distinguished "this"; classes; single-inheritance vs interfaces)
* Modules: independent shipping of code.
* Elm-style union types
* Single inheritance (or none; composition also works).
* physical-unit-types, esp for arrays; e.g. "fueltank_size:gallon", and "speed:mile/hour", with auto-conversions

performance types:

* performance types: "no autoboxing, no big-int, no dynamic dispatch, no serial loops?"
* also: No GC allocations (only ref-counting & rust-style lifetime management).
* Runs in "O(1) time"?  Runs in "O(N) time"?
* associated affine-value types: "this int is equal to that int, plus or minus a constant".

>     `fun copyInt2Dbl( src:[]int32, dst:[src.len+0]d64 )...`
> 
> OR
> 
>     `fun copyInt2Dbl( len:int32, src:[len]int32, dst:[len]d64 )...`
> 
> OR
> 
>     `fun slide( len:int32, off:int32, src:[>=len]a, dst[>=len+off]a )...`

maps & parallel loops:

* maps-over-collections; default to parallel
* parallel/distributed collections; deterministic
* maps-with-folds require a associative fold op (and will run log-tree style)
* maps-without-assoc-folds are serial loops: code it as a loop
* user-spec'd iter types; for-loop syntax-sugar

serial loops:

* For-loops with early-exit and Python else-clause

```python
for( foo in foos )
  if( isAcceptable(foo) )
    break;
  else return DidNotFindItError()
```
        
* To detect never-ran vs ran-but-not-exited:
          
```python
    if( foos.empty() ) return foos_was_empty
    else
      for( foo in foos )
        if( isAcceptable(foo) )
          break;
      else return no_acceptable_in_foos()
```

misc:

* embed 'fact' in string: "milage=%(dist/gals) mph".  The expression (dist/gals) is
a standard paren-wrapped 'fact' from the grammar.
* multi-value-returns OK, sugar over returning a temp-tuple
* Extra "," in static struct makers OK: `"{'hello','world',}"`
* Tail-recursion optimization.
* "var" can be reassigned but requires type keyword: "x:= 1"

Getting started
---------------

Download dependencies:

    make lib

Build:

    make

Run checks:

    make check

Launch the REPL:

    java -jar build/aa.jar
