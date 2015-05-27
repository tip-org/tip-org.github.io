% TIP Format

This document contains the [TIP](index.html) format,
which is an extension of [SMT-LIB](http://smt-lib.org)
for expression inductive problems.
The grammar of the format can also be viewed as [BNF](bnf.html).

### Scope of the benchmark suite

We want the benchmark suite to focus exclusively on problems that need
induction. Functional programs that don't use inductive data types probably
fit better elsewhere. Also, although we support higher-order functions and
quantification over functions, problems that need a lot of higher-order
reasoning (e.g. synthesis of functions) are probably better suited for THF.

### Criteria

When designing our language extensions, we had these criteria in mind:

1. The problem format should not look like an encoding: features such as
   data types and pattern matching should be supported natively rather
   than encoded. We should preserve as much information as possible from
   the input problem in case it's useful to a prover.
2. As far as possible, the syntax should be compatible with SMT-LIB.
   So we do not introduce new features just for the sake of it.
   We are however incompatible with SMT-LIB whenever it's needed to avoid
   breaking the first criterion.
3. The format should be accessible: easy to understand and easy for other
   tools to use. We have written a tool which removes some of the advanced
   features (such as higher-order functions) from problems to help provers
   that don't support those features.

### Example: Datatypes, match-expressions and recursion

This example specifies the commutativity of plus over natural numbers:

```tip-include
nat.smt2
```

The syntax should be familiar to users of SMT-LIB.
Natural numbers are defined with `declare-datatypes`.
This is not in the SMT-LIB standard, but is accepted by
many SMT solvers, including Z3 and CVC4.

The function is declared using `define-funs-rec` as proposed in the SMT-LIB v2.5 draft (@smtlib25).
We define `plus` rather than axiomatising it because,
if the problem is from a functional program, we want to be explicit about
which axioms are function definitions.

The `match` expression is our proposed extension for match-expressions.
The first argument to match is the scrutinee, followed by a list of
branches, all starting with the word `case` (for ease of reading).
The first argument to `case` is the constructor and bound variables
(their types are not indicated, as they are inferrable from the
type of the scrutinee and the data type declarations).

TIP also allows the user to define their functions in a more traditional
SMT-LIB syntax, using if-then-else with discriminator and projector functions
(in this case `is-Nat` and `pred`). The TIP tool is able to translate between
these syntaxes. Here is how the example above looks with
match removed:

```{.tip-include .match-to-if}
nat.smt2
```

Match expressions can also have a default branch which matches all
other pattern than those explicitly listed. This is sometimes useful
when there are many constructors. However, in the example above, either of the patterns `Zero` or
`(Succ n)` can be replaced with `default`. As an example, this is how
it looks with the `Succ` case transformed:


```tip-include
nat-default.smt2
```

Some provers like to distinguish between axioms and conjectures, and in many
inductive problems we have a distinguished conjecture. Following our principle
not to throw away information from the input problem, TIP has a `assert-not`
construct which identifies the goal, akin to `conjecture` in TPTP, or `goal`
in Why3. The declaration `(assert-not p)` means the same as `(assert (not p))`,
except that it marks `p` as a goal. It can easily be removed by the TIP tool:

```{.tip-include .negate-conjecture}
nat.smt2
```

The tool can also translate the example to Why3 syntax.
It then looks like this:

```{.tip-include .why3}
nat.smt2
```

<!--

### Complaints

(Data type declarations are already parametric, but the syntax is a bit broken.
It does not support declaring mutually recursive datatypes that differ in the amount of
type arguments.)

It is a bit broken because you have to first define all the signatures, and then the bodies.

-->


### Example: Polymorphism

TIP also supports polymorphism.
Here is an example showing the right identity of append over polymorphic lists:

```tip-include
list.smt2
```

We allow polymorphic datatypes, declarations and assertions using the syntax
suggested in @smtlam, which is currently waiting to be merged into CVC4
(@cvc4parPR). This syntax uses the syntactic form `(par (A) ...)` to quantify
over the type variable `A`. Only rank-1 polymorphism is supported.

Expressions can be annotated with their type with the `as` keyword.
When the type of a function application is not fully specified
by only looking the types of its arguments, the problem must use `as` to
specify the type.

Polymorphism can be removed by specialising the program at some ground
types, but this is not necessarily complete. Another method is to
encode typing information over monomorphic terms. We plan to add
techniques for this to the TIP toolchain. For now, provers must natively
support polymorphism if they want to solve polymorphic problems.

When translating `assert-not` into `assert`, any polymorphic type variables
are Skolemised:

```{.tip-include .negate-conjecture}
list.smt2
```

Here is the same problem in Why3 syntax:

```{.tip-include .why3}
list.smt2
```

### Example: Higher-order functions

This is an example property about mapping functions over lists:

```{.tip-include}
map.smt2
```

Lambdas are introduced much like lets, with an identifier list with
explicit types. Note that the function spaces are a family of types,
with different arities. Thus, for some types `a`, `b` and `c`, there is a type `(=> a b c)`,
which is different from its curried version `(=> a (=> b c)`. Lambdas for the first
type are constructed with `lambda ((x a) (y b)) ...`, and for the second with
`lambda ((x a)) (lambda ((y b)) ...)`. To apply a lambda, you explicitly
use the `@` function, which also come at a family of types:
`((=> a b) a) b`, `((=> a b c) a b) c`, and so on.

Partial application is not supported, i.e. if you have a function `f`
with type `(=> int int int)`, the application `(f 1)` is invalid, and should
be written with an explicit lambda: `(lambda ((x int)) (f 1 x))`. The reason
why this is important is because SMT LIB supports polyvariadic functions,
like `and`, and `+`. For example, if (implicit) partial application was allowed,
the expression `(+ 1 2)` could mean `3` or `(lambda ((x int)) (+ 1 2 x))`,
or a function with higher arity.

In some cases, higher order functions can be removed with specialisation,
like in the example above. They can always be removed by defunctionalisation,
which is implemented in our tool chain. This pass transforms the above program into this:

```{.tip-include .lambda-lift}
map.smt2
```

Here, `=>` with one argument is replaced with `fun1`, `@` with one argument
is replaced with `apply1`. The lambda in the property has become a new function,
`lam`, which closes over the free variables `f` and `g`.

### TODO

This document does not yet cover mutual recusion (over data types or over functions),
or partial branches and partiality.

### References
