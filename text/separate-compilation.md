- Title: Separate Compilation in Coq

- Drivers: David Swasey, Paolo Giarrusso, Gregory Malecha

# Summary

Coq provides a module system that can be used explicitly through commands such
as `Module` and `Module Type`. These can be quite heavyweight in many instances,
and have some limitations when it comes to separately compiling files and
building generic libraries.
To address these problems, and support information hiding and Cardelli-style separate
compilation, in this CEP we introduce a notion of Coq interface files, which we
will call a `.vi` file, and which are inspired by OCaml's `.mli` files.
Intuitively, a Coq interface file called `module.vi` defines the public
interface for `module.v`. The `module.vi` interface shall enable developing and
typechecking clients, even before `module.v` has been implemented.

If both `module.vi` and `module.v` are present, `module.vi` shall act as an
opaque ascription for the top-level module defined by `module.v`; this opaque
ascription ensures that clients that typecheck against `module.vi` shall still
typecheck against the combination of `module.vi` and `module.v`, regardless of
the implementation details of `module.v`,[^intro-universes] including any
non-logical side effects such as hints (but excluding [universes](#universes)).

This has a few advantages compared to Coq's state of the art:
- It enables separate development: after agreeing `module.vi`, `module.v` and
  its clients can be developed independently. To ensure this, unlike today's
  opaque ascription, `.vi` files can even hide side effects due to `Require`.
- It reduces compile-time dependencies and improves compile times, even compared
  to today's `vos` builds (initial builds can be more parallel, and incremental
  builds need to recompile fewer files).

NOTE: For concreteness, in this CEP we use the `.vi` extension for for interface
source files, and the `.vio` extension for interface object files. However,
`.vio` files should not be confused with `.vio` files produced by `-quick`
builds: to avoid confusion, we could choose other file extensions or remove
`-quick` builds entirely.

# Proposal

This proposal introduces the concept of an interface file with a `.vi` extension.
We think of this file as containing the `Module Type` for the corresponding `.v` file (which contains the `Module` the way it currently does in Coq and Ocaml).
`.vi` interfaces are meant to hide implementations and support separate compilation in Cardelli's sense. Hence, a module `consumer.v` that consumes the interface of `producer.vi` shall be compiled without inspecting either `producer.v`, any build product from `producer.v`, or even the existence of `producer.v`. As a consequence, no change to `producer.v** can affect whether `consumer.v** typechecks.

**Caveat** Because the behavior of Coq (e.g. tactics), as opposed to Gallina, can change when more definitions become available, removing a `.vi` file can expose implementation details that break client proof scripts though (we believe) that it cannot break kernel type checking in theory (i.e. ignoring practical considerations such as conversion times). We consider the potential to break clients a feature because meta-reasoning *should* occur at the interface and not the implemenation. 

In this section, we focus on the *Gallina*-level semantics focusing on the equivalent mathematical formulations.
We delay consideration of universes until the relevant subsection.

With the new file type, we have three situations to consider: both a `.vi` and a `.v` file, only a `.v` file, and only a `.vi` file.

## Both a `.vi` and `.v` File
An example of a `.vi` and `.v` file for a simple module would be the following:

```coq
(* lib.vi *)
Parameter value : nat.
Axiom value_is_42 : value = 42.

(* lib.v *)
Definition value : nat := 42.
Definition value_is_42 : value = 42 := ltac:(reflexivity).
```

At the *Gallina*-level, this pair of files could be compiled to the following single Coq file:

```coq
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

Note that it is possible for `lib.vi` and `lib.v` to `Require` different libraries.
In this case, it is *crucial* that side-effects (e.g. definitions, tactics, hints, notations, etc) from the `.v` file  are **not** visible by clients that `Require lib`.
Hiding these implementation details enables separate compilation, but the benefits go beyond build parallelism.

## Only a `.v` File

It is crucial that having a `.v` file without a corresponding interface does *not* change the the current behavior of Coq.
In Gallina, this is analagous to having a `Module` without a `Module Type` ascription.

In order to provide a uniform semantic understanding, we opt to reduce this to the previous situation in which both files exist, but note explictly that an implementation may not do this. For example, in Ocaml, a single `.ml` file does *not* generate a `.cmi` file.

The existance of dependent types and opaque definitions makes this question more subtle than the basic Ocaml solution.
We see three solutions:

1. *Verbatim* Synthesize the interface (the `.vi`) file using the *verbatim* contents of the `.v` file. This includes *all* definitions, hints, and other side effects. In particular it also includes the bodies of opaque (e.g. `Qed`d) defintions. While somewhat counter-intuitive, including the bodies of opaque definitions (as opposed to just their signature) means that we recover the exact semantics that we would get from including the implementation directly.
2. Synthesize the interface (the `.vi`) file using the contents of the `.v` file where opaque defintions (e.g. those that are `Qed`-d are replaced by `Parameter`s. There are two ways to do this: exactly and approximately.
   - The *exact* characterization does not expose the body of the definition, but it does include its *full* characterization including universe constraints. Note that universe constraints may not be apparent from the type of the definition but they must still be included.
   - The *approximate* characterization follows what a user would get from textually copying the type of the definition and converting it from a defined symbol to an assumed symbol, e.g. a `Parameter`.
   
   In this setup, the *exact* characterization is effectively the same as the first proposal, it simply changes the way that the opaque ascription is provided, i.e. from using `Qed` to using an opaque module ascription.
   The *approximate* characterization follows (more closely) the semantics of `-vos` builds. This enables build parallelism at the cost of delayed universe checks (and all of the consequences of this).
   
We note that both the *verbatim* proposal and the *exact* proposal are _effectively_ the same in the math. Aesthetically, we believe that the *exact* proposal seems cleaner, opting to hide more details from clients and use a more uniform sealing mechanism. The *Verbatim* option, on the other hand, seems more natural to understand and potentially implement.

## Only a `.vi` File

When only an interface file exists, there is (potentially) no underlying implementation, but the existance of the interface should still provide definite references to an implementation.
Casting this in the feature set of the current Coq ecosystem, this essentially translates to a `Declare Module` [^full-functorization].
Concretely,

```coq
(* lib.vi *)
Parameter answer : nat.
Axiom answer_is_42 : answer = 42.
```

would be "translated" to:

```coq
(* lib.v *)
Module Type LIB.
  Parameter answer : nat.
  Axiom answer_is_42 : answer = 42.
End LIB.

Declare Module lib : LIB.
Export lib.
```

## Universes

As some readers will anticipate, universe checks do not admit fully separate compilation; module bodies might add constraints absent from interfaces. This is already an issue with `.vos` builds today, and is a problem inherent to parallel builds, so any solutions to this problem could be shared.

We consider vos builds a special case of this proposal, where interfaces are inferred as the strictest possible ones for the given implementation; `.vi` files enable hiding more implementation details. In both cases, the interface omits universe constraints that are derived from hidden bodies (for vos builds, just Qed bodies). While some universe checks are performed anyway, omitted constraints might make the universe graph unsatisfiable.

To remedy this problem, we propose an additional "global" check. By analogy with separate compilation in other languages, we call this "link-time" universe checking.

Consider files `a.vi`, `a.v` and `b.v`, where `b.v` depends on `a.v`. Assume that `a.v` satisfies the interface in `a.vi` but adds universe constraints, and that `b.v` typechecks against `a.vi`. Moreover, assume that the universe constraints of `a.v` and `b.v` are both satisfiable in isolation.

We have two problems:

1. Composing the universe constraints of `a.v` and `b.v` might produce an unsatisfiable constraint set, but this is not detected. This can also occur in "vos-style" builds.
2. We can elaborate `a.v` and `b.v` separately, but their combination might produce an unsatisfiable universe graph.

A further issue is that universe inference does not seem to be prone to parallelism. Without seeing `producer.v`, 


### "Link-time" Universe Checking

Cardelli's separate compilation has a further demand: in this example, if `consumer.v` typechecks, and `producer.v` satisfies its interface, the two shall link successfully. In Coq this is true except for universe constraints, like for existing `.vos` builds. To alleviate this problem, we propos`extending `.vok` outputs to i`lude proof terms, or at least universe constraint`so that we can r` a "link-time checker" that loads the whole program and checks whether combined universe constraints are satisfiable`The above assumes that u`verses and universe constraints for a term can be generated in isolation. However, universe inference is sometimes too greedy: when compiling `consumer.v` without the universe constraints from `producer.v`, Coq will sometimes produce different terms`for instance, some Ltac c` fail with an universe inconsistency and backtrack (as mentioned in https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/vos.2Fvok.20and.20link-time.20universe.20check); we propose that the extra constraints be hidden at this stag`sometimes, Coq also seems t`produce stricter universe constraints than strictly needed, as Gaëtan shows in https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/Why.20does.20my.20fix.20for.20a.20universe.20problem.20work.3F/near/264903292. It'd be nice if the constraints were produced modularly, even if this might produce bigger graphs (hopefully in a tolerable way), or might require manual eta-expansion (we'd need Coq to give a warning/error when it must eta-expand, suggesting the user do that by hand)`

### "Full compilation" semantics

The notion of full compilation semantics, i.e. a sound full-build semantics akin to a "vo-style" build can be achieved (at the cost of build parallelism) by introducing a dependency between the `.vio` file and the `.vo` file and elaboring the resulting `.vio` file with universe constraints introduced by the implementation. It is important that this does not include other side-effects from the `.vo` such as hints, tactics, or plugin requirements.


[//]: # It might be desirable to use interfaces even when compiling "vo-style" rather than "vos-style". At least, it would be easier to check universes in such a mode. This means that compiling `consumer.v` would load `producer.vo` despite the existence of `producer.vi`. We propose that in this mode, most side effects of `producer.vo` shall be ignored anyway, including its `Require`-bound side effects.
However, the extra universe constraints from `producer.vo` compared to `producer.vos` are important.

# Implementation

The implementation would require (at least) the following:

1. Extending the build infrastructure to support `.vi` compilation.
2. Modifying the implementation of `Require` to search for `.vio` files in addition to `.vo` files. For backwards compatibility, we believe it would be important to search for both `.vio` and `.vo` files *simultaneously* rather than first searching for a `.vio` and then for a `.vo` because the later would mean that adding a `.vi` files could change the library that is used.
3. We believe that the bit-level representation of `.vio` could be the same as `.vo` files, though an alternative would be to leverage the representation of `.vos` files (which might be the same).

[^full-functorization]: An alternative characterization of `Declare Module` is to implicitly functorize all dependent modules over the module type of the declared module. This understanding of `Declare Module` does enable some additional flexibility at "link-time" but is beyond the scope of this proposal.
