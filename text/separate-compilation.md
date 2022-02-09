- Title: Separate Compilation in Coq

- Drivers: David Swasey, Paolo Giarrusso, Gregory Malecha

# Summary

Coq provides a module system that can be used explicitly through commands such as `Module` and `Module Type`. These can be quite heavyweight in many instances, and have some limitations when it comes to separately compiling files and building generic libraries. The ideas are drawn from OCaml, where .mli files can be used to express the interface of a module separately from its implementation. This enables:
Avoiding dependencies that are only needed for non-exposed definitions, e.g. you do not need to expose the fact that proofs are constructed using particular tactics.
Build parallelism (even without using -vos builds) because clients can be compiled against specification files only.

This CEP proposes several bits of sugar that makes it easier to use modules and achieve separate compilation.

NOTE: In this proposal we use the extension `.vi` to be analog to `.mli` (derived from `.ml`). Similarly, we use `.vio` as what it compiles to. The `.vio` extension is already used for `-quick` build, so we could use `.vix` or anything else here. Or, remove `-quick` builds entirely and re-purpose the name.

## Background

The goal of `.vi` files is to support separate compilation in Cardelli's sense: implementation changes that preserve the interface cannot affect clients. More formally, modules can be typechecked separately, and successful typechecking guarantees successful linking (again, up to universe checking; see below). For clarity, we intend "typechecking" to include all of elaboration, including the execution of proof scripts. If a client `bar.v` of a `foo.vi` interface elaborates correctly to a compiled file (`bar.vo` or `bar.vok`), and if `foo.v` satisfies its interface, 

# Proposal

At the highest level, this proposal introduces the concept of an interface file with a `.vi` extension. An example of a `.vi` and `.v` file for a simple module would be the following:

```
(* lib.vi *)
Parameter value : nat.
Axiom value_is_42 : value = 42.

(* lib.v *)
Definition value : nat := 42.
Definition value_is_42 : value = 42 := ltac:(reflexivity).
```

Conceptually, this pair of files could be compiled to the following single Coq file:

```
(* lib_composed.v: *)
Module Type LIB.
  Parameter value : nat.
  Axiom value_is_42 : value = 42.
End LIB.

Module lib : LIB.
  Definition value : nat := 42.
  Definition value_is_42 : value = 42 := ltac:(reflexivity).
End lib.

Export lib. (* make the declarations from lib available from [Import]ing lib (rather that lib.lib *)
```

With the new file, there are two  additional scenarios for considerations:

1. A `.v` file without a `.vi` file. This *must not* change at all. It is analagous to having a `Module` without an opaque ascription. It is also equivalent to copy-pasting the `.v` file in the corresponding `.vi` file. [^vi-less]
2. A `.vi` file without a `.v` file. In this case, 

[^vi-less]: There is some disagreement here concerning whether the bodies of `Qed`d definitions should be included here.

/// REMOVE
if .vi is missing then
  produce it by dropping the body of Qed definitions

- after you do this, you only need to consider the .v&.vi case
* in the -vos build when you process a [Require] you get the .vio file
* in the vo build when you process the require, you read the .vio file and the .vo file pulling the universes from the later into the former

if the .vi is missing then
  cp x.v x.vi
- after you do this, you only need to consider the .v&.vi case
* you read the information from .vio file, treat .vio as a .vo

vos, .vi
vos, .v
vos, .v{,i}
vo, .vi
vo, .v
vo, .v{,i}


What are the build dependencies to build: client.v that requires lib.

```
# full build with universe checking
lib.vio : lib.vo lib.vi
lib.vo : lib.v

# partial build (build speedup, no universe checking)
lib.vio : lib.vi
lib.vo : lib.vio lib.v

client.v : lib.vio
```
/// END REMOVE

## Semantics

In this section we sketch the semantics informally — ignoring problems due to universe constraints until the relevant subsections.

.vi interfaces are meant to hide implementations and support separate compilation in Cardelli's sense. Hence, a module `consumer.v` that consumes the interface of `producer.vi` shall be compiled without inspecting either `producer.v`, any build product from `producer.v`, or even the existence of `producer.v`. As a consequence, no change to `producer.v` can affect whether `consumer.v` typechecks.

Because Coq modules do not satisfy subsumption, removing `.vi` files can expose implementation details that break clients. This is a feature.

`.vi` interfaces can hide `Require`-bound side effects. Hiding is also an intentional feature, that is supported automatically in the above compilation model. However, this feature is not supported today, either via existing  `vos` builds or via opaque ascription. [One can write a Require in an interactive module, but Coq complains enough we have not explored what happens. If we lift the Require out into the surrounding top-level module, its side effects cannot be hidden.]

### "Link-time" Universe Checking

Cardelli's separate compilation has a further demand: in this example, if `consumer.v` typechecks, and `producer.v` satisfies its interface, the two shall link successfully. In Coq this is true except for universe constraints, like for existing `.vos` builds. To alleviate this problem, we propose
extending `.vok` outputs to include proof terms, or at least universe constraints
so that we can run a "link-time checker" that loads the whole program and checks whether combined universe constraints are satisfiable.
The above assumes that universes and universe constraints for a term can be generated in isolation. However, universe inference is sometimes too greedy: when compiling `consumer.v` without the universe constraints from `producer.v`, Coq will sometimes produce different terms.
for instance, some Ltac can fail with an universe inconsistency and backtrack (as mentioned in https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/vos.2Fvok.20and.20link-time.20universe.20check); we propose that the extra constraints be hidden at this stage
sometimes, Coq also seems to produce stricter universe constraints than strictly needed, as Gaëtan shows in https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/Why.20does.20my.20fix.20for.20a.20universe.20problem.20work.3F/near/264903292. It'd be nice if the constraints were produced modularly, even if this might produce bigger graphs (hopefully in a tolerable way), or might require manual eta-expansion (we'd need Coq to give a warning/error when it must eta-expand, suggesting the user do that by hand).

### "Full compilation" semantics

It might be desirable to use interfaces even when compiling "vo-style" rather than "vos-style". At least, it would be easier to check universes in such a mode.
This means that compiling `consumer.v` would load `producer.vo` despite the existence of `producer.vi`. We propose that in this mode, most side effects of `producer.vo` shall be ignored anyway, including its `Require`-bound side effects.
However, the extra universe constraints from `producer.vo` compared to `producer.vos` are important.

# Implementation

We speculate this can be accomplished by compiling `.vi` files to `.vos` outputs, and compiling `.v` files into `.vok` files.

==



The semantics of a `.vi` file would resemble today's opaque ascription with module types, while reducing boilerplate. Clients would only see the interface declared in the .vi file, but would not see the definitions of the .v file, nor its non-logical side effects such as hints.

Unlike today, `.vi` interfaces would hide not just `Import`-bound side effects, but also `Require`-bound ones. [This might be kind-of possible today by hiding `Require` inside modules with opaque ascriptions, but `Require` is discouraged inside interactive modules.]

A reviewer of our CoqPL paper objected to our proposal, because removing an interface file would reintroduce the hidden side effects and break clients. We consider this not a bug but a feature, essential to separate compilation: any change to the 

### Universes

As some readers will anticipate, universe checks do not admit fully separate compilation; module bodies might add constraints absent from interfaces. This is already an issue with `.vos` builds today, and is a problem inherent to parallel builds, so any solutions to this problem could be shared.

We consider vos builds a special case of this proposal, where interfaces are inferred as the strictest possible ones for the given implementation; `.vi` files enable hiding more implementation details. In both cases, the interface omits universe constraints that are derived from hidden bodies (for vos builds, just Qed bodies). While some universe checks are performed anyway, omitted constraints might make the universe graph unsatisfiable.

To remedy this problem, we propose an additional "global" check. By analogy with separate compilation in other languages, we call this "link-time" universe checking.

Consider files `a.vi`, `a.v` and `b.v`, where `Title: Separate Compilation in Coq
Authors: David Swasey, Paolo Giarrusso, Gregory Malecha`

# Summary

Coq provides a module system that can be used explicitly through commands such as `Module` and `Module Type`. These can be quite heavyweight in many instances, and have some limitations when it comes to separately compiling files and building generic libraries. The ideas are drawn from OCaml, where .mli files can be used to express the interface of a module separately from its implementation. In addition to build parallelism, this also enables:
Avoiding dependencies that are only needed for non-exposed definitions, e.g. you do not need to expose the fact that proofs are constructed using particular tactics.
Build parallelism (even without using -vos builds) because clients can be compiled against specification files only.

This CEP proposes several bits of sugar that makes it easier to use modules and achieve separate compilation.


## Semantics

In this section we sketch the semantics informally — ignoring problems due to universe constraints until the relevant subsections.

.vi interfaces are meant to hide implementations and support separate compilation in Cardelli's sense. Hence, a module `consumer.v` that consumes the interface of `producer.vi` shall be compiled without inspecting either `producer.v`, any build product from `producer.v`, or even the existence of `producer.v`. As a consequence, no change to `producer.v` can affect whether `consumer.v` typechecks.

Because Coq modules do not satisfy subsumption, removing `.vi` files can expose implementation details that break clients. This is a feature.

`.vi` interfaces can hide `Require`-bound side effects. Hiding is also an intentional feature, that is supported automatically in the above compilation model. However, this feature is not supported today, either via existing  `vos` builds or via opaque ascription. [One can write a Require in an interactive module, but Coq complains enough we have not explored what happens. If we lift the Require out into the surrounding top-level module, its side effects cannot be hidden.]

### "Link-time" Universe Checking

Cardelli's separate compilation has a further demand: in this example, if `consumer.v` typechecks, and `producer.v` satisfies its interface, the two shall link successfully. In Coq this is true except for universe constraints, like for existing `.vos` builds. To alleviate this problem, we propose
extending `.vok` outputs to include proof terms, or at least universe constraints
so that we can run a "link-time checker" that loads the whole program and checks whether combined universe constraints are satisfiable.
The above assumes that universes and universe constraints for a term can be generated in isolation. However, universe inference is sometimes too greedy: when compiling `consumer.v` without the universe constraints from `producer.v`, Coq will sometimes produce different terms.
for instance, some Ltac can fail with an universe inconsistency and backtrack (as mentioned in https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/vos.2Fvok.20and.20link-time.20universe.20check); we propose that the extra constraints be hidden at this stage
sometimes, Coq also seems to produce stricter universe constraints than strictly needed, as Gaëtan shows in https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/Why.20does.20my.20fix.20for.20a.20universe.20problem.20work.3F/near/264903292. It'd be nice if the constraints were produced modularly, even if this might produce bigger graphs (hopefully in a tolerable way), or might require manual eta-expansion (we'd need Coq to give a warning/error when it must eta-expand, suggesting the user do that by hand).

### "Full compilation" semantics

It might be desirable to use interfaces even when compiling "vo-style" rather than "vos-style". At least, it would be easier to check universes in such a mode. This means that compiling `consumer.v` would load `producer.vo` despite the existence of `producer.vi`. We propose that in this mode, most side effects of `producer.vo` shall be ignored anyway, including its `Require`-bound side effects. However, the extra universe constraints from `producer.vo` compared to `producer.vos` are important.

# Implementation

We speculate this can be accomplished by compiling `.vi` files to `.vos` outputs, and compiling `.v` files into `.vok` files.


### Universes

As some readers will anticipate, universe checks do not admit fully separate compilation; module bodies might add constraints absent from interfaces. This is already an issue with `.vos` builds today, and is a problem inherent to parallel builds, so any solutions to this problem could be shared.

We consider vos builds a special case of this proposal, where interfaces are inferred as the strictest possible ones for the given implementation; `.vi` files enable hiding more implementation details. In both cases, the interface omits universe constraints that are derived from hidden bodies (for vos builds, just Qed bodies). While some universe checks are performed anyway, omitted constraints might make the universe graph unsatisfiable.

To remedy this problem, we propose an additional "global" check. By analogy with separate compilation in other languages, we call this "link-time" universe checking.

Consider files `a.vi`, `a.v` and `b.v`, where `b.v` depends on `a.v`. Assume that `a.v` satisfies the interface in `a.vi` but adds universe constraints, and that `b.v` typechecks against `a.vi`. Moreover, assume that the universe constraints of `a.v` and `b.v` are both satisfiable in isolation.

We have two problems:

Composing the universe constraints of `a.v` and `b.v` might produce an unsatisfiable constraint set, but this is not detected. This can also 
We can elaborate `a.v` and `b.v` separately, but their combination might produce an unsatisfiable


A further issue is that universe inference does not seem to be prone to parallelism. Without seeing `producer.v`, 

## Value


`b.v` depends on `a.v`. Assume that `a.v` satisfies the interface in `a.vi` but adds universe constraints, and that `b.v` typechecks against `a.vi`. Moreover, assume that the universe constraints of `a.v` and `b.v` are both satisfiable in isolation.

We have two problems:

Composing the universe constraints of `a.v` and `b.v` might produce an unsatisfiable constraint set, but this is not detected. This can also 
We can elaborate `a.v` and `b.v` separately, but their combination might produce an unsatisfiable


A further issue is that universe inference does not seem to be prone to parallelism. Without seeing `producer.v`, 

## Value

