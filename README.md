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
| u | The float, a floating point number, of type Float|
| x | The term variable, of type<br>depending on the environment,<br>and requires a term abstraction to abstract it |
| \x.t1 | The term abstraction, of type<br>T -> T1, where T is the<br>type given to x and T1 of t1,<br>and x, the name of the term variable<br>must not be capitalized, for otherwise it<br>becomes a type variable abstraction |
| \x: T.t1 | The annotated term abstraction, of type<br>T -> T1, where T is the T from<br>the annotated T of \x: T.t1,<br>and x, the name of the term variable<br>must not be capitalized, for otherwise it<br>becomes invalid syntax |
| t1 t2 | The term application, of type<br>T1, where T2 -> T1 is the<br>type of t1 and T2 of t2 |
| \X.t1 | The type abstraction, of type<br>∀X.T, where T is the type of t1,<br>and X, the name of the abstracted type<br>variable must be capitalized, for otherwise it<br>becomes a term variable abstraction |
| t1@T | The type application, of type<br>\[X\ -> T]T1, where ∀X.T1 is the type of t1<br>and T is the T from @T |
| t1 : T | The annotation of type<br>T, should t1's type T1 match it |
| let x = t2 in t1 | The let-binding, which in this case is<br>syntactic sugar for ((\x.t1) t2) |
| let x: T = t2 in t1 | The let-binding, which in this case is<br>syntactic sugar for ((\x: T.t1) t2) |
| +I | The plus operator for integers<br>of type Int -> Int -> Int |
| +F | The plus operator for floats<br>of type Float -> Float -> Float |
| +ⁱ\<i\> | The partially applied plus operator for integers<br>of type Int -> Int, which is unachievable<br>without first evaluating, and the i within<br>the angled brackets stands for the first<br>received integer argument |
| +ᶠ\<u\> | The partially applied plus operator for floats<br>of type Float -> Float, which is unachievable<br>without first evaluating, and the u within<br>the angled brackets stands for the first<br>received float argument |

| Types | Meaning |
| :---: | :------ |
| Int | The integer type, which is for integers i |
| Float | The float type, which is for floats u |
| X | The type variable, which requires a<br>type abstraction to abstract it |
| T1 -> T2 | The arrow type, which is for<br>term abstractions/functions |
| ∀X.T1 | The for-all type, which is for<br>type abstractions |

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
