- Title: The structure of the unification algorithm

----

# Summary

Unification is a central component of a proof assistant, used for type inference, inference of implicit information, tactic application.

The unification algorithms in Coq have grown organically by need. The code is currently rather convoluted and somehow fragile, with small changes in some parts of the code having easily side effects on other parts of the code.

Sozeau and Ziliani 2015 and 2016 designed a unification algorithm based on a clear structure. This CEP is about describing the components of the current unification algorithm in the direction of re-articulating it around a similarly well-understood structure like Sozeau and Ziliani did.

A priori the following basic architecture is intended to be preserved:
- a part canonically splitting complex unification problems into atomic ones (e.g. `(0,?f 0) == (?m,(0,0))` into non-ambiguous assignment `?m := 0` and multi-solution `?f 0 == (0,0)`) with linear complexity
- a part applying heuristics when several solutions are possible (e.g. resolving `?f := fun x => (x,x)` rather than `?f := fun x => (0,0)` or `?f := fun x => (0,x)` or `?f := fun x => (x,0)`), possibly using backtracking

# Basic background on unification

## Existential variables

Unification relies on *existential variables* which are defined in a context which is specific to each of them. The declaration of an existential variable takes the form:
```
a₁:A₁,...,aₙ:Aₙ ⊢ ?e : B
```
where:
- `a₁:A₁,...,aₙ:Aₙ` is the defining context of the existential variable (called `evar_hyps` in the implementation, it is made of named declarations, possibly with local definitions too, so, shortly a `named_context`)
- `B` is its type (`evar_concl`)

To be used in a term, existential variables need to be applied to a substitution of its context. So, they take the form `?e@{a₁:=t₁,...,aₙ:tₙ}` where `a₁:=t₁,...,aₙ:=tₙ` is a *substitution* (sometimes called *instance*, often written `args` in the code).

## Existential variables map

A collection of declarations of existential variables is conventionally written `Σ` (an `evar_map` in the code, using either `sigma` or `evd` to refers to it).

## Unification problems

Given an existential variable map, *unification problems* are equations of the form `Γ ⊢ t₁ =?= t₂` or inequations of the form `Γ ⊢ t₁ ≤? t₂` where `t₁` and `t₂` are terms possibly mentioning existential variables with their substitution and both terms living in a context of variables `Γ` (that is the juxtaposition of a `named_context` and of a `rel_context`). An inequation corresponds to a subtyping problem between types (e.g. `Prop ≤ Type`). Note that we assume the existence of a global context of inductive types, definitions and axioms common to the definitions of existential variables and to the unification problems.

A unification algorithm turns a `Σ` and a collection of unification problems into either an impossibility of satisfaction of the equations, or in a collection of (well-typed) definitions for the existential variables such that all problems are satisfied, or a residual set of unification problems that the algorithm is neither able to invalidate nor to satisfy (since unification in general is undecidable in the Calculus of Inductive Constructions).

## Reflexive unification problems

We call *reflexive unification problem* an equation of the form `Γ ⊢ ?e@{subst} =?= ?e@{subst'}`.

## Atomic unification problems

We call *atomic unification problem* an equation of the form `Γ ⊢ ?e@{subst} =?= ?e'@{subst'}` or an inequation of the form `Γ ⊢ ?e@{subst} ≤? ?e'@{subst'}`.

## Simple unification problems

We call *simple unification problem* an equation of the form `Γ ⊢ ?e@{subst} =?= t` or an inequation of the form `Γ ⊢ ?e@{subst} ≤? t`. Unification basically reduces arbitrary complex unification problems to simple ones which in turn may generate new arbitrary complex problems.

## Simplification of reflexive unification problems

A reflexive unification problem induces constraints on the possible definitions of `?e`: once `?e` is defined, it may generate new unification problems between terms of the instances that contain existential variables.

A reflexive unification problem can be simplified as follows:
- Variables of the context whose instances in the substitution are provably incompatible (e.g. because corresponding to distinct head normal forms) can be removed from the context.
- If both instances are free of existential variables, the problem can be dropped since its resolution will eventually only create equations between convertible existential-variables-free terms.

## Simplification of atomic unification problems

An atomic unification problem can be simplified as follows:
- Variables of the context of the existential variables that are bound to terms mentioning variables of the context of the equations in non-erasable position in only one of the two instances can be restricted since there would be no way to make these terms match a subterm of the instance of the other existential variables; otherwise said, both existential variables can be restricted on the (well-typed closure of the) subsets of their context which intersect.
- If the problem is an inequation, it can only be postponed since one variable could be instantiated e.g. with `Prop` and the other with `Type` without them to be equal.
- If one of the instances mention only distinct variables on the subset where there is an intersection, *and* the problem is not an inequation, the corresponding existential variable can be defined with the other one without loss of solutions

## Basic algorithm for resolving simple unification problems

Solving non atomic simple unification problems relies on basically two concepts (see Huet 1975, `MATCH` algorithm):
- *Projection*, that is, solving `Γ ⊢ ?e@{a:=t,b:=t} =?= t` by either setting `Δ ⊢ ?e := a` or `Δ ⊢ ?e := b` so that `?e@{a:=t,b:=t}` indeed evaluates in `Γ` to `t`.

  In the more general case, a projection requires to solve general unification problems, that is, to know if `Γ ⊢ ?e@{a:=t} =?= u` can be solved by projecting `a` requires to find a context `E` such that `Γ ⊢ E[t] =?= u` is resolvable (up to reduction of `E[t]`). This can be done in a systematic way in algebraic-type-free λ-calculus by reasoning on the normal forms of `t` and `u` and using type constraints. It is not clear however that a systematic study of the process and of the form of evaluation ontexts has already been done somewhere in the presence of algebraic types.

  For instance, in the presence of algebraic types, there is a specific incarnation of projection steps involving constructors. For instance, the problem `Γ ⊢ match ?e with S n => t | O => u end =?= v` can be solved (among other resolution strategies) by defining `?e := S ?n` for a new existential variable `?n` and solving `Γ ⊢ t[n:=?n] =?= v` or defining `?e := 0` and solving `Γ ⊢ u =?= v`.

  We call projection of variables the subcase when `u` is a variable and `E` is empty. In practice, Coq implements only projections of variables and projections of terms of the form `C t₁ ... tₙ` for `C` a constructor, with `E` empty (but PR [#14798](https://github.com/coq/coq/pull/14798) extends this to `E` made of nesting of `match` and projections).

- *Imitation*, that is, imitating the structure of `t`, or part of it, and generating subproblems about the subterms of the imitated part of `t`. 

  For instance, if `C` is a constructor, the equation `Γ ⊢ ?e@{subst} =?= C t₁ ... tₙ` reduces to the collection of equations `Γ ⊢ ?eᵢ@{subst} =?= tᵢ` by declaring new existential variables `?eᵢ` of appropriate type in the same context as `?e` and by setting `?e := C ?e₁@{dom(Δ)} ... ?eₙ@{dom(Δ)}`. 

  Similarly, if the head symbol of `t` is a binder, new existential variables are generated for the subterms of the binder in a context extended with the new binder.

## Efficiency non-determinism

The non-determinism comes from the potentially different ways to project and from the ability to also sometimes imitate. For instance, there are 2 possible projections and one possible imitation to resolve `Γ ⊢ ?e@{a:=t,b:=t} =?= t` for `t` variable-free.

There is also a form of non-determinism which comes from reducing unification problems or not in normal form:
- When resolving `Γ ⊢ c t =?= c' t'` with `c` and `c'` distinct unfoldable constants, there is a choice in reducing `c` or `c'` in the hope that the problem is eventually found satisfiable. This choice can lead to arbitrarily long computations so, controlling unfolding is important (there are similar problems when efficiently comparing the convertibility of two terms).
- It is also useful to limit unfolding of constants so as to obtain solutions as close as possible to the original form of the terms involved.

## Higher order pattern unification

*Higher order pattern unification* (see Miller 1991 and Pfenning 1991) is a special case of simple unification problem when the substitution is made only of distinct variables. In this case, there is a single solution obtained by projecting the unique possible variable or imitating if not a variable.

Pattern unification has various refinements (see e.g. Libal and Miller 2016) such as:
- expecting distinct variables only among the variables that actually occur in the term to match
- identifying arguments that are irrefutable patterns over variables at their leaves (e.g. `(x,(y,z))` with those variables (i.e. a form of curryfication) (see PR [#14798](https://github.com/coq/coq/pull/14798))

## Heuristics

Facing the non-determinism between several possible projections and a possible imitation, heuristics can be applied. E.g. to infer the return clause of a `match`, we can give priority to the less dependent solution (see function `Evarconv.choose_less_dependent_instance` for equations of the form `Γ ⊢ ?e@{subst} =?= x` with `x` occurring several times in `subst`).

In addition to the heuristics arbitrating between different projections or between projection and imitation, the following heuristics are used to help to instantiate existential variables about which no particular equations otherwise apply.
- Canonical structures to solve problems of the form `projᵢ t =?= u` by virtual reduction to `projᵢ t =?= projᵢ v`, that is, concretely, to `t =?= v`, where `v` is a canonical equipment of all components of a tuple from only knowing the value of its projection `u` (see functions `Evarconv.check_conv_record` and `Evarconv.check_record`).
- Type class inference to solve existential variables of some type by proof search (function `Typeclasses.resolve_typeclasses`).
- First-order unification: e.g. to resolve `?P ?x =?= Q t` by assuming that the intent is to set `?P := Q` and `?x := t` (see `Evarconv.first_order_unification` and subfunction `first_order` of `Evarconv.evar_conv_x`). 

  It is actually not fully clear to me what are all the ins and outs of first-order unification.
  - In situations like `Q ?x =?= Q t` with `?x` erasable when reducing `Q ?x`, first-order unification gives a hint on how to infer `?x` and this seems to be a useful heuristics.
  - In situations like `?P t =?= Q t`, it tells not to care about possible instances of `t` in `Q` and this is more disputable (e.g., it is a priori unexpected that `?P 0 =?= (0=0)` is solved into `?P := fun x => 0=x` rather than into `?P := fun x => x=x`).

- Second-order unification heuristics: e.g. to resolve `?P t =?= u` by selecting a number of occurrences of subterms unifiable to `t` in `u` (see `Evarconv.second_order_matching`). Such a heuristic is central to any form of reasoning by induction. As far as I can recap, it is currently used in Coq only for tactics.
  - One issue is to recognize subterms: we can assume `t` free of existential variables and reason modulo convertibility, or we can reason using syntactic equality, or syntactic equality discarding non-essential, i.e. reinferable arguments (i.e., morally the implicit arguments).
  - Another issue is that typing constraints induce equivalence classes of subterms that have to be abstracted altogether.

## Basic algorithm for simplifying unification problems

Eta-conversion in the metatheory is convenient to make a unification algorithm more uniform.

It is also convenient to put the terms involved in a non-simple conversion problem in "sequent calculus" form, that is under the canonical form `E[t]` ("unique context lemma", with `E` called an evaluation context, or, in the code, stack) where:
- `E` is empty and `t` is neither an existential variables nor a redex (the *rigid* case)

  When the two terms are in this case, this directly leads to an impossibility or to simpler problems (algorithm `SIMPL` of Huet 1975)

- `t` is an existential variable `?e` in context `Δ` (the *flexible* case)

  When at least one of the two terms is in this case, this may eventually reduce to one or more simple conversion problems:

  - If the surrounding evaluation context is an application and `?e : forall x:T, U`, we can declare `Δ, x:T ⊢ ?e' : U` and refine `?e := fun x => ?e'@{dom(Δ),x:=x}` without losing solutions (this requires eta-conversion of function types); note however that we may lose an opportunity to use a first-order heuristics by doing so.

  - If the surrounding evaluation context is a projection, or case analysis on a finite one-constructor type (with constructors named `Build`), the existential variable can be refined with `?e := Build ?e₁ ... ?eₙ` without losing solutions (this requires eta-conversion on finite one-constructor types).

    Note however that:
    - we may lose an opportunity to use a canonical structure heuristic by doing so
    - we cannot do that if the types is infinite (no eta rule and possibility of an infinite refinement process)

  - If the surrounding evaluation context is a case analysis on an arbitrary inductive type (with constructors `C₁`, ..., `Cₙ`), various actions could be taken under the assumption that eta holds for the given type.

- `t` is a redex (the *maybe-flexible* case)

  When one term is maybe-flexible and the other is rigid, there is no other alternative than reducing the redex.

  When the two terms are maybe-flexible, we need a heuristic to progress, e.g. by reducing one of the side, or by comparing the subterms of the redex. Discarding (crucial) efficiency issues, this should be equivalent except when a subterm is erased by reduction, in which case comparing shapes before reducing gives some hints on how to resolve erasable existential variables.

# Analysis of the current situation

## Data structures

### Candidates

*Candidates* can be attached to existential variables. Candidates are a way to postpone the time to backtrack on different possible solutions when it is known that there are only a finite set of solutions (e.g. only a finite possibility for projecting and imitating).

To support more advanced forms of postponements such as the resolution of equations of the form `match ?e with ... end =?= v` by cases, it would be useful to support attaching unification subproblems to candidates. This remains to be done.

### Postponed problems

*Postponed problems* are problems whose resolution would require making a choice, or problems whose resolution would be algorithmically arbitrarily complex. Postponed problems are typically of these forms:
- evar-evar: `E[?e@{subst}] =?= E'[?e'@{subst'}]` or `E[?e@{subst}] ≤? E'[?e'@{subst'}]`
- evar-term: `E[?e@{subst}] =?= t` or `E[?e@{subst}] ≤? t` or `t ≤? E[?e@{subst}]`

Each time an evar blocking a postponed problem is defined, the corresponding postponed problem can be reconsidered.

### Filters

Atomic unification problems induce constraints on variables allowed to be used in the definition of an existential variables. *Filters* are used to indicate variables which cannot be used.

It is not safe to simply remove a variable from the typing context of an existential variable as it may break the typability of the context and of the type of the variable.

Even if I'm responsible for the introduction of filters in the code, I find the current implementation dubious. In practice, filters are closed by dependency so as to preserve typing, so, I don't understand why `Evd.restrict` uses a filter on the original context rather than directly restricting the context of the new existential variable. Filters should be used only in the resolution of simple unification problem to control the variables which are allowed to occur.

### Status of local definitions

Instances of existential variables include terms for the local definitions. These terms are convertible to the actual local definitions in the context of the existential variables. For instance, if `a:A, b:=u:B ⊢ ?e : T`, then, an instantiation `?e@{a:=t;b:=u'}` in context `Γ` satisfies `Γ ⊢ u[a:=t] ≡ u'`.

The presence of local definitions in the instances of existential variables allows to be able to refer to the name of local definitions when projecting. That is, at the time of solving equations of the form `Γ ⊢ ?e@{a:=a;b:=b} =?= b`, where `b` is a local definition, the name `b` is used to define the existential variables rather than the body of `b`. A more formal study of their use would not hurt though.

## Algorithmic components

### Resolution of reflexive unification problems

There is a function `Evarsolve.solve_refl` which seems to reasonably do what it has to do.

### Resolution of atomic unification problems

There is a function `Evarsolve.solve_evar_evar` which applies a few heuristics:
- resolving the problem in case of pattern unification
- restricting otherwise the context on variables occurring on both sides of the equation

### Resolution of simple unification problems

A. There is a function `Evarsolve.solve_simple_eqn` to solve simple unification problems but:
1. It may apply heuristics too early:
   1. when trying to solve `?e@{subst} := t`, it ignores the terms of the substitution which are neither a variable nor an applied constructor; e.g. when trying to solve `?e@{a:=Prop} := Prop`, it assumes that imitation is the only possibility but that's wrong

   On the other side, projecting terms which are not in head normal form may be arbitrarily costly:
   - so, we may consider projecting ...
   - as a heuristic, we may still rely on syntactic equality so as, e.g., to use a projection in `?e@{ack 4 4} := ack 4 4`

2. It may fail to find possible solutions:
   1. there are valid circular instances that it is not able to accept (see ongoing PR [#14746](https://github.com/coq/coq/pull/14746))
   2. it is not able to detect that if a variable of the term to match is not in the scope of the existential variable it could still be erasable by reduction

### Reduction of unification problems to simpler unification problems

B. The current function `Evarconv.evar_conv_x` roughly implements the decomposition of complex problems into elementary bricks but:
1. It may apply heuristics too early:
   1. in the `?e u₁...uₙ =?= ?e' u'₁...u'ₘ` case, it may prefer a first-order heuristic even if other solutions are possible
   2. when the evaluation context is not purely applicative, it may prefer component-wise unification of the evaluation context (function `consume` in the code)
   3. it inherits the too early application of heuristics of `solve_simple_eqn`

2. It may fail to apply progresses that it could make:
   1. when trying to solve `?e@{subst} u₁...uₙ := t` with `t` rigid, it postpones the problem as soon as `subst` is not made of only variables  while it could refine `?e` with the rigid subpart of `t`

3. It is not always properly structured:
   1. non-primitive projections should be classified as destructors rather than constants so that `E[proj ?e]` is seen as flexible rather than maybe-flexible and so that canonical equipment has to be considered only in the flexible case
   2. it tries `solve_simple_eqn` before splitting the problem according to the unique context lemma while this call could morally be integrated to the flexible-something cases
   3. it inherits the weaknesses in the ability of `solve_simple_eqn` to progress
      - it postpones back failures of `solve_simple_eqn` to resolve superficially cyclic problems while it should be the job of `solve_simple_eqn` to decide when to postpone
      - it reorient back failures of `solve_simple_eqn` on problems with erasable occurrences of variables not in scope while it should be the job of `solve_simple_eqn` to ensure that erasable variables are erased before instantiating

4. It is not always well understood:
   - eta rules for `match` could certainly be introduced to improve the treatment of `match` evaluation contexts

C. The current function `Evarconv.solve_unif_constraints_with_heuristics` applies heuristics on postponed problems but:
1. It is not properly able to backtrack and may fail when the heuristically found solution for one problem is not compatible with the heuristically solution of another pending problem.
2. It is lacking basic heuristics (e.g. basic second-order matching) (see the weaker ongoing [#14805](https://github.com/coq/coq/issues/14805)).
3. Interaction with type classes is not clear to me: shouldn't type classes inference be part of the loop trying heuristics so that:
   - it is possible to mutually backtrack on choices made by heuristics and choices made by type classes inference (this lack of interaction happens to be a cause of the current unique failure in [#14805](https://github.com/coq/coq/issues/14805)).

## About typing

The first-order heuristic may produce ill-typed problems. PR [#14733](https://github.com/coq/coq/pull/14733) tries to ensure correct typing.

When defining an existential variable with a term, the term is retyped. Is this really needed?

# Directions for short terms improvements

All the numbered points above are worth being addressed.

My feeling is that the true backtracking ability C.1 of `Evarconv.solve_unif_constraints_with_heuristics` should come first followed by the extensions C.3 then C.2, so that the heuristics are strong enough to absorb/compensate incremental modifications in `evar_conv_x` and `solve_simple_eqn`.

# Miscellaneous further perpectives

**Delaying choices**
- A way should be found to postpone the use of first-order unification heuristics as well as to postpone the decision of using canonical structures.
  - For instance, for a `?P ?e =?= Q t` problem, one can set `?P := fun x => ?P'` with pending equation `?P'@{x:=?e} =?= Q t` and one could declare that `?e` has by default to be instantiated by `t` if no other instances is available.
  - Similarly, for a `projᵢ ?e =?= t` problem, `?e` could be resolved into `Build ?e₁ ... t ... ?eₙ`, for `Build` the constructor of the record type, with some indication that each such subterm `Build ?e₁ ... t ... ?eₙ` with unsolved component should be resolved using a canonical equipment.

**Extensions**
- Extend canonical structures to canonical equipments based on knowing two or more projections?
- Reorganize canonical structures so that it more generally solves equations of the form `proj₁ᵢ₁ (... projₙᵢₙ ?e ...) = u`. On one side, it should a priori give more discriminating solutions. On the other side, it would allow to treat canonical structures only in the flexible case.
- Extend first-order unification to `match` term, e.g. to resolve `if true then t else u =?= if ?e₀ then ?e₁ else ?e₂` by setting `?e₀ := true`, `?e₁ := t` and `?e₂ := u` (see wish [#12780](https://github.com/coq/coq/issues/12780)).
- Existential variables for sorts can sometimes not be instantiated by `Prop` even in situation where it would be legitimate to do so (see PR [#7369](https://github.com/coq/coq/pull/7369)).

**Optimizations**
- Systematically eta-reduce the solutions to existential variables (with all kinds of eta). On one side, this seems to be the natural expectation. On the other side, this would avoid caring about whether it might be dommageable to eta-expand this or that solution in the unification algorithm.
- Give an order between constants which would allow to predict which side to reduce in `E[c] =?= E'[c]`.
- Keep constants unfolding to fixpoints folded so as to concentrate on the essential and reduce the size of expressions, including in evaluation contexts (i.e. stacks).
- Do more aggressive restrictions of contexts (e.g. Sozeau and Ziliani seem to take the downwards well-typed closure of restrictions while Coq takes the upwards well-typed closure - knowing that taking the closure by dependency requires in theory to take care of erasable occurrences)?
- Filters need to be better understood: why not to directly restrict the context more often?
- Better understanding when to backtrack on constant unfolding:
  - See e.g. the case of [#3594](https://github.com/coq/coq/pull/3594) which needs to solve `opp (opp (opp ?R)) =?= opp ?R` for `?R` a relation and `opp` that swaps arguments: should it compute and realize that `opp (opp ?R)` is `?R` and that no instanstantiation is done; should it keep things folded and reduces to `opp (opp ?R) =?= ?R` which `solve_simple_eqn` could recognize to be actually true up to eta-conversion?
  - See e.g. the case of `?e = K 0 x` with `x` not in the scope of `?e`: what should be responsible to realize that reducing `K 0 x` would drop the dependency in `x`? Should it be `solve_simple_eqn` itself or the maybe-flexible heuristic?

**Parameterizations**
- Sometimes, we need a quick and light way to ensure that two terms are incompatible (e.g. when restricting reflexive unification problems or checking compatible candidates). A specific unification function should be explicitly identified for this purpose (or maybe, can it be one of the flags parameterizing unification).
