% TIP Format

This document contains the [TIP](index.html) format, which is an
extension of [SMT-LIB](http://smt-lib.org) for expressing inductive
problems. The grammar of the format can also be viewed as
[BNF](bnf.html).

### Scope of the benchmark suite

The benchmark suite focuses exclusively on problems that need induction over
datatypes. Also, although we support higher-order functions and quantification
over functions, problems that need a lot of higher-order reasoning
(e.g. synthesis of functions) are probably better suited for THF.

<!--
### Criteria

When designing our language extensions, we had these criteria in mind:

1.  The problem format should not look like an encoding: features such
    as data types and pattern matching should be supported natively
    rather than encoded. We should preserve as much information as
    possible from the input problem in case it's useful to a prover.
2.  As far as possible, the syntax should be compatible with SMT-LIB. So
    we do not introduce new features just for the sake of it. We are
    however incompatible with SMT-LIB whenever it's needed to avoid
    breaking the first criterion.
3.  The format should be accessible: easy to understand and easy for
    other tools to use. We have written a tool which removes some of the
    advanced features (such as higher-order functions) from problems to
    help provers that don't support those features.
-->

### Differences between TIP and SMT-LIB 2.6
Our ambition is to keep TIP as close to SMT-LIB as possible.
However, there are still a few incompatibilities:

- TIP allows polymorphism and type variables in function definitions. SMT-LIB
  only allows polymorphism in datatype definitions.
- TIP allows higher-order functions, while SMT-LIB does not.
- TIP allows partial functions. SMT-LIB does not.
- For convenience, TIP has a special command `prove` for stating a goal to prove.
  This allows us to state several subgoals to be proved
  as separate proof attempts, in one file.
- TIP uses a different syntax for annotations than SMT-LIB.

The [TIP tools](http://github.com/tip-org/tools) can convert TIP files not
compatible with SMT-LIB 2.6 to valid SMT-LIB syntax (use the command `tip
--smtlib myTIPfile.smt2`). This includes monomorphisation to remove type
variables, removal of lambdas, completion of partial functions, removal of
annotations and a translation pass which remove the `prove` statement and
replaces them with valid SMT-LIB syntax using push/pop.

### Datatypes, match-expressions and recursion

This example specifies the commutativity of plus over natural numbers:

    (declare-datatype Nat ((Zero) (Succ (pred Nat))))
    (define-fun-rec
      plus
      ((x Nat) (y Nat)) Nat
      (match x
        (((Succ n) (Succ (plus n y)))
         (_ y))))
    (prove (forall ((n Nat) (m Nat)) (= (plus n m) (plus m n))))

The syntax should be familiar to users of SMT-LIB. Natural numbers are
defined with `declare-datatype`, and the function is declared using
`define-fun-rec`. Both are part of the
[SMT-LIB v2.6 standard](http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf).
We define `plus` rather than axiomatising it because, if the problem is from a functional program, we
want to be explicit about which axioms are function definitions.

TIP has a `prove` construct which declares the goal, akin to `conjecture` in
TPTP, or `goal` in Why3. It is not part of SMT-LIB. If the problem uses `prove`
only once, then `(prove p)` means the same as `(assert (not p))`. If `prove` is
used several times, it indicates that there are several goals which must all be proved.

* To convert a problem to standard SMT-LIB format, run `tip --smtlib`.
* To replace `match` expressions with selector functions (e.g. `is-plus`), run `tip --remove-match`.
  You can combine this with conversion to SMT-LIB format with `tip --smtlib-no-match`.
* To convert a problem to Why3 format, run `tip --why3`.

### Polymorphism

TIP also supports polymorphism. Here is an example showing the right
identity of append over polymorphic lists:

    (declare-datatype
      list (par (a) ((nil) (cons (head a) (tail (list a))))))
    (define-fun-rec
      append
      (par (a) (((xs (list a)) (ys (list a))) (list a)))
      (match xs
        ((nil (_ nil a))
         ((cons x zs) (cons x (append zs ys))))))
    (prove
      (par (a) (forall ((xs (list a))) (= (append xs (_ nil a)) xs))))

We allow polymorphic datatypes, declarations and assertions using the
syntactic form `(par (A) ...)` to quantify over the type variable `A`. Only rank-1
polymorphism is supported. Note that TIP allows both polymorphic datatypes and
polymorphic functions, unlike SMT-LIB 2.6, which only allows it in datatype definitions.

<!--
suggested in @smtlam, which is currently waiting to be merged
into CVC4 (@cvc4parPR). This syntax uses the syntactic form
`(par (A) ...)` to quantify over the type variable `A`. Only rank-1
polymorphism is supported.
-->

An underscore is used to instantiate a polymorphic function at a given type.
In general, if `f` is a polymorphic function symbol having `n` type arguments,
then `(_ f t1 ... tn)` applies `f` to the type arguments `t1 ... tn`. Explicit
type arguments must be given whenever a function's type cannot be inferred by
looking at the types of its arguments. In the example above, this occurs with
`(_ nil a)`.

<!-- Polymorphism can be removed by specialising the program at some ground -->
<!-- types, but this is not necessarily complete. Another method is to encode -->
<!-- typing information over monomorphic terms. We plan to add techniques for -->
<!-- this to the TIP toolchain. For now, provers must natively support -->
<!-- polymorphism if they want to solve polymorphic problems. -->

* To eliminate polymorphism from a problem, run `tip --monomorphise`.

### Higher-order functions

This is an example property about mapping functions over lists:

    (declare-datatype
      list (par (a) ((nil) (cons (head a) (tail (list a))))))
    (define-fun-rec
      map
      (par (a b) (((f (=> a b)) (xs (list a))) (list b)))
      (match xs
        ((nil (_ nil b))
         ((cons y ys) (cons (@ f y) (map f ys))))))
    (prove
      (par (a b c)
        (forall ((f (=> b c)) (g (=> a b)) (xs (list a)))
          (= (map (lambda ((x a)) (@ f (@ g x))) xs) (map f (map g xs))))))

Lambdas are introduced much like lets in SMT-LIB, with an identifier list with
explicit types. They are applied using '@'. Note that the function spaces are a
family of types, with different arities. Thus, for some types `a`, `b` and `c`,
there is a type `(=> a b c)`, which is different from its curried version `(=> a
(=> b c)`:

* To construct a value of type `(=> a b c)`, write `lambda ((x a) (y b)) ...`.
  To apply it, write `(@ f x y)`.
* To construct a value of type `(=> a (=> b c))`, write ``lambda ((x a)) (lambda ((y b)) ...)`.
  To apply it, write `(@ (@ f x) y)`.

That is, if you want to partially apply a function, you must either write a
lambda, or define it in a curried fashion in the problem.

* To eliminate lambdas from a problem, run `tip --axiomatize-lambdas`.

### TODO

This document does not yet cover partial functions or annotations.
