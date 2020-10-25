- Title: Contravariant subtyping and support for η-reduction

- Drivers: Hugo Herbelin

----

# Summary

We propose to turn subtyping contravariant on the left-hand side of dependent products and to include η-reduction as a standard reduction rule.

# History

Subtyping was introduced in Coq version 4.8 (1988) where it was contravariant on the left-hand side of dependent products. In version 4.9 (1989) it was however moved to equivariance on the left-hand side of dependent products.

The story I recalled is that the set-theoretic model of the Extended Calculus of Constructions which Luo studied in his PhD (defended 1990) was not able to model the contravariance. More precisely, granting a contravariant interpretation of `Πa:A.B` is easy, but, in a setting where the conversion is untyped, there is no way to give the same interpretation to `f` and to an η-expansion `λx:A.fx` restricting its domain.

Since then, Martin-Löf's typed approach to conversion learnt us that we can interpret typed conversion instead, and, by results from Adams, Siles and the author who proved the equivalence of typed and untyped conversion in the setting of Pure Type Systems, there is a strong presumption that untyped conversion can be equipped with types also in the presence of subtyping.

In particular, it is unclear to me that the absence of contravariance is still defendable, even, if, stricto sensu, the exact formulation of the metatheory of Coq is only in progress (see MetaCoq) and, in particular, we have no formal proof that Coq subtyping between well-formed types is equivalent to a typed one.

# Motivations

On the theoretical side, contravariant subtyping and η-reduction are intuitive and convenient. Why do without?

Also, transparently supporting η-reduction allows to manipulate shorter expressions. Users have already suggested we may have it (e.g. coq/coq#2860).

Additionally, in unification, in order to factorize the code between first-order unification and Miller-Pfenning pattern unification, it is convenient to resolve a Miller-Pfenning pattern `x ⊢ ?f x == t` into `?f := λx.t` even though if `t` had been some `g x` with `x`∉FV(`g`), first-order unification would have instead produced the simpler form `?f := g`. So, if we had a way to be certain that η-reducing unification solutions afterwards is safe, we could stop having a distinct unification path for Miller-Pfenning pattern unification and first-order unification.

# Detailed design

_Contravariant subtyping_ is obtained by changing the subtyping rules in a couple of places:

- in `reduction.ml`, where the basic kernel subtyping is implemented
- in `vconv.ml`, where the vm-based subtyping is implemented
- in `nativeconv.ml`, where the native-compute-based subtyping is implemented
- in `evarconv.ml`, where the unification subtyping is implemented
- am I missing something?

Some support for _η-reduction_ already exists (see flag `ETA` in `cClosure.ml` and `shrink_eta` in `reductionops.ml`). Providing support for `eta` in `cbv`, `cbn`, `lazy` can be obtained by working at the level of the following files:

- adding support for an `eta` flag in parsing (`g_tactic.mlg` but ideally in `g_vernac.mlg` so that it is part of the specification language, see coq/coq#11679) and printing.
- in `cClosure.ml`: adding a function to `whd_eta`-normalize `constr` and call it from `norm_head` at the time of reifying
- similarly for `cbv_norm_value` in `cbv.ml`
- for `cbn`, the code is already there and it should work automatically from the moment the `eta` flag is parsed
- similarly for internal reduction strategies in `reductionops.ml`

An open question is whether we should optimize the computation that `x` does not occur in `t` in the rule `λx:A.tx` → `t`, so as to avoid traversing the whole term at each new λ. For instance, we could collect the number of occurrences of each variables in the normal form at reification time so that there is no more traversals of the term than the one done by the reification code.

_In unification_, we may experiment applying `whd_eta` at the end of `solve_simple_eqn` (which itself is used to resolve Miller-Pfenning problems) so that it produces similar solutions as if first-order unification had been used.

# Further directions

- support for η in `rewrite` coq/coq#11719
- MetaCoq-justified subtyping
- ...
