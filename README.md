# aa

Cliff Click Language Hacking

Not really a language, as much as a stream of consciousness puking of language desires.



Functional; 1st class functions.
Dynamic code-gen; no seperate compilation step.  Load Source & Go.
REPL
"eval"
JIT'ing.  {GC,Ref-Counting}: Ponder both vs requiring e.g. lifetime management (easy by just raising scope).
No exceptions!!!   
Lexical scope destructors.
Primitive values; int overflow OK; can ask for Int for BigInteger; unboxed arrays.
Pattern-matching too handy looking, need to have it
Parallel (and distributed) but also deterministic

maps-over-collections; default to parallel
parallel/distributed collections; deterministic
maps-with-folds require a associative fold op (and will run log-tree style)
maps-without-assoc-folds are serial loops: code it as a loop

Pony-style concurrency management
CAS built-in lang primitive: 'res := atomic(old,new)'; JMM
CPS for threads/concurrency;
not really actors but spawn/fork worker threads, run until they 'join' with parent.
Transactions-for-shared-memory-always (Closure style)

Monads?  i/o, side-effect monads.

Static typing; types optional at every place.
H-M style typing.  Limited overloads.
Null-ptr distinguished; null/notnull types (e.g. Kotlin)
OOP namespaces (distinguished "this"; classes; single-inheritence vs interfaces)
Duck-typing?  Interfaces.  Single inheritance (or none; composition also works).
Overloading ops.  No ambiguity / easy-to-read rules.  By default multi-arg ops are overloaded.
physical-unit-types, esp for arrays; e.g. "fueltank_size:gallon", and "speed:mile/hour", with auto-conversions
Sub-byte ranges?  Julia???

Modules: independent shipping of code.

Elm-style union types

No exceptions?!!?  Same as Elm: allow tagged union returns with an error return
vs a non-error return.  Force user to handle errors up&down the stack.

performance types: "no autoboxing, no big-int, no dynamic dispatch, no serial loops?"
also: No GC allocations (only ref-counting & rust-style lifetime management).
Runs in "O(1) time"?  Runs in "O(N) time"?
associated affine-value types: "this int is equal to that int, plus or minus a constant".
  'fun copyInt2Dbl( src:[]int32, dst:[src.len+0]d64 )...'
OR
  'fun copyInt2Dbl( len:int32, src:[len]int32, dst:[len]d64 )...'
OR
  'fun slide( len:int32, off:int32, src:[>=len]a, dst[>=len+off]a )...'

Distributed ref-cnting?  (or Dist-GC?)
Ref-Counting does NOT given "immediate" destructor execution, but "soon".
Guarenteed to count down & release before the next instance of exact same constructor constructs?
Guarenteed to count down & release before the next loop backedge?  Before base of containing loop?
Built-in "pools" for bulk-remove?  Same as ref-counting.
Rust-style memory lifetime management; linear logic owner; borrowing; guarenteed death

Tail-recursion optimization.

Direct SSA style code writing; no 'let' keyword.
default "x := 1" makes a "val" until scope runs out (cannot re-assign)
"ref" can be reassigned but requires type keyword: "x:ref := 1"

multi-value-returns OK, sugar over returning a temp-tuple
Extra "," in static struct makers OK: "{'hello','world',}"
For-loops with early-exit and Python else-clause
  for( foo in foos )
    if( isAcceptable(foo) )
      break;
  else return DidNotFindItError()
To detect never-ran vs ran-but-not-exited:
  if( foos.empty() ) return foos_was_empty
  else 
    for( foo in foos )
      if( isAcceptable(foo) )
        break;
    else return no_acceptable_in_foos()
