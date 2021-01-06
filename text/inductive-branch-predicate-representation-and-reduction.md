- Title: Representation of predicate and branches of inductive types in the implementation, and how reduction tactics should treat them
- Driver: Hugo
- Status: Draft

----

## Summary and motivation

Regarding the branches and the return clause of a `match`, there is a discrepancy between the user-level syntax and the internal representation. This has unexpected effects on how some reduction tactics consider a `match`. This CEP is about proposing a canonical internal representation which matches the user view, as well as about clarifying the expected behavior of reduction tactics on `match`.

## Context

The user view at inductive types is that of an `as x in I realargs return P` for the return predicate and of a `C vars => u` for a branch (view 1). This view matches the "pure" (dependent-product independent) proof-theoretic view at inductive types. But the implementation represents the return predicate and the branches as functions (view 2).

The advantage of representing the return predicate and the branches as functions is that there is no special treatment to do in `match` (internally `Case`) to deal with the binders of the return predicate and branches: they reuse the path code of `fun` (internally `Lambda`).

The drawbacks are that:
- no insurance that the predicate and branches have the η-expanded form expected for printing; no insurance to have enough abstracted names and necessity to invent names
- the notion of subterm in the internal representation does not match the notion of subterm in the user representation; a whole branch is itself a subterm; occurrences of a subterm are unstable by invisible internal η-conversion

To be more precise, from one part of the code to another, the treatment of branches and return predicate can be more or less ad hoc, ranging from view 1 to view 2 with variants. For instance, `vm_compute` and `native_compute` considers the branches and return predicate under view 1, but the other reduction machines (`cbn`, `cbv`, `lazy`) consider them under view 2. Tactic `pattern` considers them under view `2`. Also, the code for typing branches in the kernel now assumes view 1 and may fail in interaction with parts of the code which assume view 2 (see #6749, #7068, and probably other reports).

## Conceptual differences in term of typing rules

### 

The typing rule for `match` implicit in the user syntax is:
```
Γ, Δ[params/Ω], x : I params |Δ| ⊢ P : s
Γ, Ξᵢ[params/Ω] ⊢ ui : P[realargsᵢ/Δ][Cᵢ |Ξᵢ|/x]    (for all i < nb constructors)
Γ ⊢ c : I params realargs
---------------------------------------------------------------------
Γ ⊢ match c as x in I |Δ| return P with ... Cᵢ |Ξᵢ| => ui ... end : P[realargs/Δ][c/x]
```
where:
- `Ω` is the context of unconstraining parameters
- `Δ` the context of real/constraining parameters
- `Ξᵢ` is the context of parameters of the i-th constructor `Cᵢ`
- `realargsᵢ` are the real arguments of the i-th constructor `Cᵢ`
- the substitution `[params/Ω]` and `[realargs/Δ]` instantiate the assumptions of `Ω` or `Δ` with the given arguments `params` or `realargs` and the local definitions of the contexts by their body
- `|Δ|` extracts from `Δ` the name of variables which are assumptions

###

However, the code hesitates between the above rule and the historical typing rule (used in the syntax before Coq 8.0 and still shown in Chapter 4 of the reference manual):

```
Γ ⊢ P : B  if [I params|B]
Γ ⊢ ui : {Cᵢ realargs}P   (for all i < nb constructors)
Γ ⊢ c : I params realargs
---------------------------------------------------------------------
Γ ⊢ case (c,P,ui) : P[realargs/Δ][c/x]
```
where:
- `[I params|B]` is a condition telling when the return predicate has the right form for a given `I`
- `{Cᵢ realargs}P` is a condition telling when a branch has the right form for constructor `Cᵢ` in a given `I`

### Remarks

There are situations where it is interesting to have the arity of the inductive type or of the type of constructors not of a canonical form `forall Δ, s` or `forall Δ, I realargs`

In `Ensembles`, we have
```coq
Definition Set := A -> Prop. Inductive union :
Definition In (A:Ensemble) (x:U) : Prop := A x.
Inductive Union (B C:Ensemble) : Ensemble :=
    | Union_introl : forall x:U, In B x -> In (Union B C) x
    | Union_intror : forall x:U, In C x -> In (Union B C) x.
```
It is cool to be able to use the abbreviations `Ensemble` and `In`.

Another example is given in #6749:
```coq
Inductive foo (T : Type) : let T' := Type in T' := .
```

This means that we need at some time a conversion of arity and type of constructors from they are not necessarily in `forall Δ` form. This means also that we need a normalization function which produces such forms `forall Δ, T` keeping `let`s.

## The rôle of `let`s in the definition of inductive types

- `let`s are allowed in the type of constructors; this is used relatively often for abbreviating subterms; in records, this also allows to simulate manifest fields as if a module; this seems required
- `let`s are allowed in the parameters of an inductive type; `let`s are allowed in the arity; the interest is maybe questionable, but it is convenient to reason uniformly in the code with general contexts rather than having sometimes contexts possibly with `let`s and at other time contexts without `let`s.

#### Form of schemes in the presence of `let`s

- In the presence of `let`s in parameters, should these `let`s be kept in the scheme? I would say yes, otherwise, why to use `let`'s if not to share subterms?
- In the presence of `let`s in the "real" arity, should these `let`s be kept in the type of the predicate in the scheme? Should they be available in the `return` clause? For the same reasons, I would say yes, otherwise, why to use `let`'s if not to share subterms?
- In the presence of `let`s in the type of constructors, should these `let`s be available in the pattern? I would again say yes.

### The hybrid status of patterns in the presence of let-ins in the construcor

Currently, if the type of the constructors contains `let`s, the pattern can either mention all variables (including those bound to a `let`), or only those bound to a proper assumption (thus excluding all `let`s). E.g.:
```coq
Inductive I := C : forall n, let p := 0 in let q := 0 in n = p + q -> I.
Check fun x => match x with C n H => H=H end. (* ok *)
Check fun x => match x with C n p q H => (H=H,p+q) end. (* ok *)
```
I believe this should be kept.

## Examples of questionable behaviors at the current time

### Inconsistency between internal matching subterm and the user view

Matching subterms can capture the trailing part of a branch which includes `fun` which is non-intuitive considering how branches are printed:
```coq
Goal forall y, match y with 0 => 0 | S n => 0 end = 0.
intros.
replace (fun x : nat => 0) with S.
(* match y with 0 => 0 | S x => S x end = 0 *)
```
Note that we see a `x` because of the now needed η-expansion which canonically uses `x` for names to invent.

## Related issues: the invisibility of types of pattern variables

Even with view 1, the types of pattern variables are not displayed. One should be able to display them in some `Printing All` mode. The ongoing work on adding `Cast` in patterns should make this available.

## Proposal

I'm proposing in a first step to provide combinators to treat branches and return predicate in an ad hoc way, assuming and preserving a canonical form `fun Δ => u` or `fun Δ (x:I params |Δ|) => T`

  1. in particular, check that this canonical form is there at typing time,
  2. ensure that the canonical form is preserved by the system, in particular by the reduction functions; i.e. that the reduction functions work on each component of the context Δ in isolation.

In a second step, to make the branches and return predicate abstract types so that we can change the internal representation, typically into a pair `(Δ,T)`.

Note: I already have proof-of-concept code which provides 1., part of 2., part of the second step.

## Perspectives

To consider skipping types of pattern variables when comparing for syntactic equality? As soon as the main terms of the `match` match, we know that the parameters of the corresponding instance of the inductive type are the same and that all types of the contexts of the return predicate and branches are convertible. So, we should not have to care about them.
