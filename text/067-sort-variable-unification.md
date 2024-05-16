- Title: Introducing quality variables in sort unification

- Drivers: Pierre-Marie Pédrot

----

# Summary

In addition to variables for universe levels, we generalize the type of sorts to
also contain quality variables, allowing delaying the choice between Prop, Type
and SProp made by unification. This CEP is only concerned about unification,
although the kernel structures need to be modified accordingly, the kernel
treats undefined quality variables as an error, similarly to evars.

The first part of this CEP is implemented in [Coq PR 16903](https://github.com/coq/coq/pull/16903).

# Motivation

There are several underlying motivations for this CEP.

- Immediate fix: alleviate the longstanding issue of having to explicitly
annotate variables with `Prop` to make the unification go through.
- Short term: fix the `SProp` mess in the implementation of kernel and unification.
- Long term: enhance the modularity of Coq by allowing terms to be polymorphic
over sorts like `Prop` / `Type` / `SProp`, a.k.a. stop triplicating everything.

The first point is adressed directly in this CEP, the two other ones are made
possible after the CEP is implemented. We detail the issues below.

As of Coq 8.17, every time one creates a fresh sort, it is implicitly living in the `Type` hierarchy. This has unfortunate consequences, like the fact that `fun A => A /\ A -> A` typechecks but `fun A => A -> A /\ A` does not. Since the arrow is typechecked left-to-right, the first one forces `A : Prop` but the second one forces `A` to be a fresh sort, hence a `Type`. In that latter case you have to explicitly write the Prop annotation for the pretyper to be happy. Similar issues arise from other asymmetrical constructs like equality.

The introduction of `SProp` makes the problem even more salient. Long story short, the historical universe unification algorithm in Coq basically assumes that everything is a `Type`, and the reason `Prop` ⊆ `Type` is not so much about kernel expressivity but rather that otherwise it would be too painful to write code using `Prop`. `SProp` has the same issue, so for easiness of writing `SProp`-based code and not confusing unification, @SkySkimmer introduced a horrible hack where we pretend `SProp` ⊆ `Type`, i.e. the dreaded cumulative `SProp` flag. The problem is that `SProp` also taints the terms in the relevance marks, so in the end one gets nonsense terms in the kernel that needs to fix them on the fly. This is the usual curse of Coq technical debt: you fix issues in the upper layers by introducing workarounds in the kernel. This makes it essentially impossible to use `SProp` at scale.

# Detailed design

This CEP introduces a trivial idea to sort out the mess. Namely, in addition to the well-known universe *levels* one now also has access to sort *qualities*. While levels are basically integers, qualities are the nature of the sort itself, i.e. `Prop`, `Type` or `SProp`. Since we want to have unification on this first-order signature, we also freely add variables. They are just tracked in the evarmap in a way similar to levels. The most generic type is thus `QSort (α, u)` where `α` is a sort quality and `u` an algebraic universe.

Since this affects pervasive data structures, we need to change the kernel definitions. But similarly to evars, the kernel currently does not know anything about undefined sort variables, apart from their relevance which is needed for conversion.

In order for the system to work, we have constraints and quotients going on.
- The type of a sort `QSort (α, u)` is always `Type(u+1)`, i.e. the sort of a sort must have a `Type` quality. This is true in current Coq since `Prop : Type`, `SProp : Type` and `Type : Type`.
- The type of a product `forall x : A, B : QSort(α, u)` is such that `α` is the quality of the sort of `B`, and `u` the max of levels (as usual). This is also true in Coq, and is designed to make impredicativity work.
- Impredicative sorts have a degenerate level structure, i.e. `QSort(Prop, u) ≡ Prop` and similarly for `SProp`. This ensures that we can make unification of sort qualities commute with impredicative typing.

The current unification of sorts is very conservative, but it could easily be enhanced to be more expressive. We just add a union-find state of unification variables to the `UState.t` record and tweak universe unification by eagerly unifiying sorts when the qualities involved in a constraint are not ground. For instance, when asked `QSort(α, u) ≤ QSort(β, v)` we set `α := β`. This is not complete for `≤` constraints, but is simpler to implement.

A longer-term feature (not for this CEP) is to add *sort-polymorphism* in addition to the *level-polymorphism* we currently have. The idea is that you could write definitions and inductive types parameterized by a sort variable, so that you get for free code reusable with `Prop`, `Type` and `SProp` without having to triplicate all the definitions. With some cleverness you can even emulate the template-poly feature that inductive types can fall in `Prop` when the parameters are also in `Prop`.

# Drawbacks

We have to track an additional unification state, so this has a little runtime cost. It does not seem to be much, though.

The current implementation is slightly backwards-incompatible because it makes some unification choices eagerly. A typical bad choice happens with dependent case analysis whose branches do not live in the same sort. The example below works with 8.17 but fails with the CEP.

```coq
Inductive boolε : bool -> Type :=
| trueε : boolε true
| falseε : boolε false.

Definition foo (b : boolε true) :=
match b with
| trueε => I
| falseε => tt
end.
```

Note that this clashes with what seems like a mysterious legacy design pattern using `idProp` for dead branches.

The reason for this is that when unifying `Prop ≤ QSort(α, u)` we set `α := Prop`. We could restore the old behaviour by being less eager and tracking in the unification state whether a quality variable is in the `Prop ⊆ Type` component instead of forcing it to be `Prop` upfront. The fix does not require changing the kernel structures, only the unification state.

# Alternatives

I do not think that there are alternatives to variables, literally the zero level of abstraction.

# Unresolved questions

How do we display this to the user?
