# aa

Covariance and Contravariance with Hindley-Milner
=================================================

Confusions
----------
sub-classing via adding extra fields
compile-time checking class type via using extra field
taking a generic collection and reading out an element
taking a generic collection and putting in  an element



Naming
------

I use Lists as a stand-in for any collection.  You may freely substitute Array
or Dict.  I use leading Uppercase for Types, and lower case for variables and
values: '`List` vs `list`; `Int` vs `int`; `Str` vs `str`.

I use `<angle brackets>` for generic types: `List<Int>` vs `Ary<Str>`.

There are interfaces, e.g. static structural typing (not duck typing, which is
the weakly typed runtime-only equivalent), and there are classes with
inheritence.  Interface type names will start with an I, `IReader` and
`IWriter`.  The root class is `Obj` with unrelated siblings `Int` and `Str`.


H-M types
---------

H-M side steps the co/contra-variance issue by soundly typing without
annotations, or at least I'm gonna try to show it.  A well typed program does
not need upcasts, nor will it be able to put an `Int` into a `List<Str>`.
The hard part is telling H-M you have a `List<Str>` and not a `List<Obj>`.

To do this in the context of H-M, I am going to use a normal "pure" H-M
extended for structures with labeled fields.  This is an extremely well worked
out extension, and is commonly used in many papers often with the words "and we
extend this to structures in the _obvious_ way".

Here is a simple BNF for H-M types:

    e = number             |
        string             |
        prims              | // Built-in names such as '+' or 'equals'
        (e0 e1*)           | // Application; multiple arguments allowed
        { e0* -> e1 }      | // Lambda; 
        id                 | // Some type-variable, either free or bound
        id = e0;e1         | // Let 'id' be type 'e0' in expression 'e1'
        @{ (label = e)*; } | // A structure (e.g. class or struct in Java or C) with any count of labels with type expressions
        e.label              // A label from structure-typed 'e'

I use single letter uppercase names for anonymous type variables, `T` or `V`,
but will stick with `List` when it makes sense.



List
----

```Java
class List<T> {
    List next;
    T value;
    T get() { return value; }
    void put(T e) { value = e; }
}

List<T> = : @{     // aa, but syntax changed to angle brackets
    next:List<T>;
    value:T;
    get = { value };
    put = { e -> value = e; }
}
```

The H-M type for the List class is:
```
List = @{
    next = List;
    value = T;
    get = { List -> T };
    put = { List T -> List };
}
```

Notice that `T` is free in this expression.  It will be unified 




And a sample function to read from the list head (and NPE if null).

```Java
Int reader(List<Int> list) { return list.value; }  // Java
reader = { list:List<Int> -> list.value:Int }      // aa with annotations
reader = { list           -> list.value     }      // aa without
```









Type variance issues are fairly tame in the absence of generic types, so let's
focus on those. Continuing the variance example, imagine four functions:


void doObjectLogging(Logger   <Object> logger ) { logger.add(new Object());     }
void doStringLogging(Logger   <String> logger ) { logger.add("hello"     );     }
void doObjectExtract(Extractor<Object> extract) { Object o = extractor.first(); }
void doStringExtract(Extractor<String> extract) { String s = extractor.first(); }


Basically, it's a 2x2 matrix with one axis being consumer vs. producer (Logger vs. Extractor) and the other being base vs. derived (Object vs. String) for the type parameter of the generic type.

Now let's create an implementation class that implements the example List type, which is both a Logger and Extractor:

class ListImpl<T> implements List<T> {...} 


And instantiate two of those:

List<Object> objList = new ListImpl<Object>(); 
List<String> strList = new ListImpl<String>();


So, the question is, which of the following should be legal (and why):

doObjectLogging(objList);
doObjectLogging(strList);
doStringLogging(objList);
doStringLogging(strList);
doObjectExtracting(objList);
doObjectExtracting(strList);
doStringExtracting(objList);
doStringExtracting(strList);
Cameron - Yesterday at 10:25 AM
Let's start by eliminating the obviously correct ones, for which there is no debate, since they follow the type invariant model (which is always assumed to be correct):

doObjectLogging(objList);
doStringLogging(strList);
doObjectExtracting(objList);
doStringExtracting(strList);


Next let's eliminate the obviously incorrect one (outside of Javascript and Perl at any rate):

// obvious compile time error (narrowing cast required)
doStringExtracting(objList);    


That leaves only three variance cases to examine in detail. Let's explain the easy one first:

doStringLogging(objList);


Here we have a function that logs strings to a logger, and a logger instance that takes any object. A strictly type invariant language (a type system without allowance for type variance) would disallow this, but it seems fairly self-evident (and type safe) that a Logger<Object> can be used anywhere that a Logger<String> is called for, and List<Object> is a Logger<Object>.

Almost identical is the ability to extract "any object" from a list of strings. The same logic applies here: Since a string is an object, it makes sense (and is type safe) to be able to extract objects from a list of strings: 

doObjectExtracting(strList);


That leaves just one problem case:

doObjectLogging(strList);


Common sense says that we cannot log objects to a logger that only takes strings, so at a surface level, common sense says that this type of variance should be disallowed.
 
But there's a hidden gotcha in the example, and here it is: If a String is an Object, then can we also say that a List<String> is a List<Object>? And here we can see why some languages say "no!" -- because List both consumes and produces T, so a List<String> cannot be passed to a function as a List<Object> because the function may call the add method -- passing any Object and not just a String! -- on the underlying List<String>.




I'd suggest that there is no "figuring out" to do here. It's not a right
vs. wrong question; rather, it is a decision made to either allow or disallow a
certain form of type variance, based on some fundamental principles. This is,
for example, the difference between Java arrays (a String[] "is a" Object[])
and Java collections (a List<String> is not a List<Object>) We call this "the
fourth quadrant problem". Here's an early design note on the topic:

//                   widening                narrowing
// C<T1> -> C<T2>    T1=String -> T2=Object  T1=Object -> T2=String
// ----------------  ----------------------  -------------------------
// !(C consumes T1)  1. Implicit conversion  2. Illegal (Compile Time Error)
// !(C produces T1)  3. Implicit conversion  4. Implicit conversion
//                      (but possible RTE)


Tying the numbers from the numbered quadrants to our example:

1. doObjectExtracting(strList)
2. doStringExtracting(objList)
3. doObjectLogging(strList) <- this is the controversial case!
4. doStringLogging(objList)

If number 3 is disallowed, then List<String> is not and cannot be a List<Object>.

If number 3 is allowed, then List<String> can be a List<Object>.
For the record, we were determined to make number 3 work, yet still with as much compile-time type safely and as few explicit casts as possible. And at this point, I think I can say that we achieved that.
(What I'm writing up here is the distillation of four different engineers working on this one problem for hundreds of -- and maybe even a thousand -- hours, so don't be surprised if it feels overwhelmingly complex. Among other things, I'm writing it down here and trying to explain it in a followable sequence as another way of trying to re-digest it myself.)
