# CICCT

**C**ontextual **I**ntersection **C**alculus **C**ontextual **T**yping.

## An informal introduction

Please refer to Xu Xue's and Bruno Oliveira's paper Contextual Typing [2024].

The other branches of this repository are different implementations of contextual typing.

This was made for a university project under the guidance of **Professor Mário Florido**.

## Actually running CICCT

This should suffice:

```cabal build```

```cabal run```

## Using CICCT

CICCT is a REPL. So, in order to use it, you may either write into a file inside the ```programs``` directory, or directly use the REPL's mid-execution features.

## Understanding CICCT's Language

Check the referenced article, the example inputs from ```programs/default_tests.txt``` and try using the REPL for a little while.

## Syntax and Semantics

Regarding the Typing for each syntax construct, I might add it later on. This system is far more complex than that of VSBDT, which means I can't simply describe the typing of each contruct using a small table. I will have to think this through first.

| Syntax | Meaning |
| :----: | :------ |
| i | Integer, a number, of type Int |
| u | Float, a number, of type Float |
| {} | An empty record, of type Top |
| x | A term variable, of type<br>depending on the environment |
| \x.t1 | A term abstraction, of type<br>T -> T1, where T is the<br>type given to x and T1 of t1 |
| t1 t2 | A term application, of type<br>T1, where T2 -> T1 is the<br>type of t1 and T2 of t2 |
| + | The plus operator, of type<br>(Int -> Int -> Int) & (Float -> Float -> Float) |
| +ⁱ<i> | A plus operator having received an<br>integer i as its first argument, of<br>type (Int -> Int) and the smaller i<br>is not the same as the big one |
| +ᶠ<u> | A plus operator having received an<br>integer i as its first argument, of<br>type (Float -> Float) |
| t.a | A projection, where a is label, and<br>t a term, and its type is Ta<br>where the type of t is {Tb, ..., Ta, ...} |
| {a1=t1, ..., an=tn} | A record, where an is a label and<br>tn is a term, and its type<br>is {a1 : T1, ..., an : Tn} |
| t : T | An annotation, where its type<br>is T should t's type match it |

| Types | Meaning |
| :---: | :------ |
| Int | For integers i |
| Float | For floats u |
| Top | For empty records {} |
| T1 -> T2 | For abstractions/functions |
| {a1 : T1, ..., an : Tn} | For records |
| T1 & T2 | For intersections |

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
