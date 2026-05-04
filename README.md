# LCTICT

**L**ocal **C**ontextual **T**ype **I**nference **C**ontextual **T**yping.

## An informal introduction

Please refer to Xu Xue's, Chen Cui's, Shengyi Jiang's and Bruno Oliveira's paper Local Contextual Type Inference \[2026\].

The other branches of this repository are different implementations of contextual typing.

This was made for a university project under the guidance of **Professor Mário Florido**.

## Actually running LCTICT

This should suffice:

```cabal build```

```cabal run```

## Using LCTICT

LCTICT is a REPL. So, in order to use it, you may either write into a file inside the ```programs``` directory, or directly use the REPL's mid-execution features.

## Understanding LCTICT's Language

Check the referenced article, the example inputs from ```programs/default_tests.txt``` and try using the REPL for a little while.

## Syntax and Semantics

| Terms | Meaning |
| :----: | :------ |
| i | The integer, a number, of type Int |
| u | The float, a floating point number, of type Float |
| True | The boolean true value, of type Bool |
| False | The boolean false value, of type Bool |
| () | The unit, an empty value, of type Unit |
| c | The character, a letter a digit or a space, of type Char |
| x | The term variable, of type<br>depending on the environment,<br>and requires a term abstraction to abstract it |
| \x.t1 | The term abstraction, of type<br>T -> T1, where T is the<br>type given to x and T1 of t1,<br>and x, the name of the term variable<br>must not be capitalized, for otherwise it<br>becomes a type variable abstraction |
| \x: T.t1 | The annotated term abstraction, of type<br>T -> T1, where T is the T from<br>the annotated T of \x: T.t1,<br>and x, the name of the term variable<br>must not be capitalized, for otherwise it<br>becomes invalid syntax |
| t1 t2 | The term application, of type<br>T1, where T2 -> T1 is the<br>type of t1 and T2 of t2 |
| \X.t1 | The type abstraction, of type<br>∀X.T, where T is the type of t1,<br>and X, the name of the abstracted type<br>variable must be capitalized, for otherwise it<br>becomes a term variable abstraction |
| t1@T | The type application, of type<br>\[X\ -> T]T1, where ∀X.T1 is the type of t1<br>and T is the T from @T |
| t1 : T | The annotation of type<br>T, should t1's type T1 match it |
| opI | An operator for integers<br>of type Int -> Int -> Int |
| opF | An operator for floats<br>of type Float -> Float -> Float |
| op | An operator for booleans<br>of type Bool -> Bool -> Bool |
| opⁱ\<i\> | A partially applied operator for integers<br>of type Int -> Int, which is unachievable<br>without first evaluating, and the i within<br>the angled brackets stands for the first<br>received integer argument |
| opᶠ\<u\> | A partially applied operator for floats<br>of type Float -> Float, which is unachievable<br>without first evaluating, and the u within<br>the angled brackets stands for the first<br>received float argument |
| opᵇ\<b\> | A partially applied plus operator for booleans<br>of type Bool -> Bool, which is unachievable<br>without first evaluating, and the b within<br>the angled brackets stands for the first<br>received boolean argument |
| opᶜ\<c\> | A partially applied plus operator for characters<br>of type Char -> Char, which is unachievable<br>without first evaluating, and the c within<br>the angled brackets stands for the first<br>received boolean argument |
| opᵘ\<u\> | A partially applied plus operator for units<br>of type Unit -> Unit, which is unachievable<br>without first evaluating, and the u within<br>the angled brackets stands for the first<br>received boolean argument |
| not | The negation operator for booleans<br>of type Bool->Bool |
| if t1 then t2 else t3 | The if-then-else statement, where t1 must be<br>of type Bool and the types of t2 and t3,<br>T2 and T3, must be the same |
| (t1, ..., tn) | The pair, of type (T1, ..., Tn), the tuple type |
| t.n | The projection, of type Tn, where t must be<br>of the type (T1, ..., Tn, ...) |
| \(x1, ..., xn).t | Function pattern matching for tuple arguments, of<br>type (T1, ..., Tn) -> T where T is the type of t |
| \(x1: T1, ..., xn: Tn).t | Annotated function pattern matching for tuple arguments,<br>of type (T1, ..., Tn) -> T where T is the type of t |
| fix t | The fix operator for recursion, of type T where T->T is the type of t |
| let x = t2 in t1 | The let-binding, which in this case is<br>syntactic sugar for ((\x.t1) t2) |
| let x: T = t2 in t1 | The annotated let-binding, which in this case is<br>syntactic sugar for ((\x: T.t1) t2) |
| let f x1 ... \X1 ... \Xm ... xn = t2 in t1 | The let-binding with additional syntactic sugar for outermost abstractions<br>which can either be type abstractions or term abstractions,<br>the terms can be annotated and f can't be mentioned inside its own (t1) definition |
| letrec f = t2 in t1 | The letrec-binding, which in this case is<br>syntactic sugar for (\f.t1) (fix (\f.t2)) |
| letrec f: T = t2 in t1 | The annotated let-binding, which in this case is<br>syntactic sugar for (\f: Int.t1) ((fix (\f: Int.t2)) : Int) |
| letrec f x1 ... \X1 ... \Xm ... xn = t2 in t1 | The letrec-binding with additional syntactic sugar for outermost abstractions<br>which can either be type abstractions or term abstractions,<br>the terms can be annotated and f can be mentioned<br>inside its own (t1) definition,<br>also note how the type abstractions are the only ones<br>which must have a lambda to their left |
| \[\] | The empty list, of type forall X.\[X\] |
| h :: t | The list constructor, where t must be of list type \[T\]<br>and h of type T, which is right associative |
| \[t1, ..., tn\] | Syntactix sugar for t1 :: ... :: tn :: \[\]<br>which is, therefore, of type List\[T\], where T is<br>the type of t1, ..., tn simultaneously |
| "c1...cn" | Syntactix sugar for c1 :: ... :: cn :: \[\]<br>such that the c's are of type Char, which is,<br>therefore, of type List\[Char\] |
| head | The head function, of type forall X.\[X\] -> X<br>which retrieves the head of a given list |
| tail | The tail function, of type forall X.\[X\] -> \[X\]<br>which retrieves the tail of a given list |
| empty | The empty function, of type forall X.\[X\] -> Bool which<br> returns True if a given list is empty and False otherwise |


The operators are always prefix.

The operators for numeric types (ints and floats) are +, -, * and /. (plus, minus, mult, div)

The division for ints is floor division. There is no operator overloading, so in order to distinguish between int operators and float operators, a suffix letter must be added as shown in the table: a letter I in front of the operator for making it for integers, and an F letter for making it for floats.

There are comparison operators <, >, <=, >=, ==, /= for ints, floats, chars.

The operators for boolean types (bools) are ==, /=, && and ||. (and, or)

The operators for unit types are ==, /=.


| Types | Meaning |
| :---: | :------ |
| Int | The integer type, which is for integers i |
| Float | The float type, which is for floats u |
| Bool | The boolean type, which is for booleans b |
| Unit | The unit type, which is for units () |
| Char | The character type, which is for characters c |
| Top | The least general type, for any term |
| Bot | The most general type, for no terms |
| X | The type variable, which requires a<br>type abstraction to abstract it |
| T1 -> T2 | The arrow type, which is for<br>term abstractions/functions |
| ∀X.T1 | The for-all type, which is for<br>type abstractions |
| (T1, T2) | The product type, which is for pairs<br>and is right associative |
| \[T\] | The list type, which is for lists of any shared type |


Evaluation may not work even if the term is well-typed, since the evaluator is not complex and tries to remove as little type annotations as possible, so that subject reduction is preserved. I might create an erasure function so that full evaluation may occur on-demand. Another reason is that inference allows sometimes for type applications to be omitted, which means there's a syntactic hole.

Annotations are always recommended for the fix operator/letrec. The rules for the fix-operator are in dire need of improvement.

## REPL's Commands

Most of the commands are simple and related in purpose. The table is dense because there are multiple configurations for the same thing. It was not well thought out, but serves its purpose. I hope this was not too much of a hurdle.

| Command(s) | Usage | Description |
|------------|-------|------------|
| *(All commands)* | — | Command names (the first token of the command) are not case sensitive. |
| :var, :v, :assign, :a | :v \<var_name\> | Assign a written term to <var_name>. |
| :type, :ty, :t | :t \<var_name\> | Show the type of the term assigned to <var_name>. |
| :help, :h, :? | :h | Display information regarding the commands. |
| :show, :sh, :s | :s \<var_name\> | Show the term assigned to <var_name>. |
| :var, :v, :assign, :a | :v <var_name1> | Evaluate from the current environment (given <var_name2>) and store into <var_name1>. |
| :var, :v, :assign, :a | :v <var_name1> | Evaluate n-steps from the current environment and store into <var_name1>. |
| :load, :l | :l \<file_path\> | Load terms from file at <file_path>, assigned as `<var_name> := <expression>`, and load into the environment. |
| :v?, :vars | :v? | Show the first page (10 environment variables) if a number is not specified. |
| :v?, :vars | :v? \<number\> | Show the <number>'th page (containing 10 environment variables' names). |
| :m, :mv, :move | :mv \<var_name1\> \<var_name2\> | Store the contents of <var_name2> into <var_name1>. |
| :q, :quit | :q | Close the REPL. |
| :te, :tenv, :typeenv | :typeenv | Attempt to type all variables in the environment. |
| :c, :ce, :cenv, :clear, :clearenv | :c | Clear the environment (no variables accessible until new ones are added). |
| :av?, :allvars | :av? | Show all variables in the environment. |
| :showenv, :showe, :senv, :se | :se | Show the environment. |
| :showenv, :showe, :senv, :se | :se \<page_number\> | Show a specific environment page. |
| :te, :tenv, :typeenv | :te \<page_number\> | Type a specific environment page. |
| \<program\> | \<program\> | Shows, then Types and then Evaluates the given program/term. |
| *(Environment pages)* | — | Page numbers start at 1. |

In contrast to YALCI's REPL, this one does not include any form of desugaring.

## Report any bugs

Do not forget to report any bugs. I'll be very glad to listen to any complaints.
