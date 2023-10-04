- Title: Coq roadmap

- Drivers: Nicolas Tabareau (@tabareau), Théo Zimmermann (@Zimmi48)

----

# Summary

This CEP aims to establish a roadmap for the Coq project.
It highlights both:

- what are considered as important axes to work on in the future,
- what resources are available to work on these axes, and which axes we commit
  to work on based on these resources.

Resources mean availability of persons to conduct the work. For technical axes,
requiring changes in the Coq system, it includes availability of persons to
review and merge the changes.

# Motivation

Producing a roadmap for the Coq project is important for several reasons:

- It helps the community to know what to expect from the Coq project in the
  future, in particular what changes can reasonably be expected to become
  part of next releases, and what changes are more likely to be delayed
  because of lack of resources.

- It helps Coq developers to focus on important axes, and to be more
  efficient, by making sure that their work will be supported by other
  developers, including reviewers.

- It helps contributors to know what are the important axes where their
  contribution is most likely to be welcome and where they can expect
  the most support from the Coq developers.

- It helps highlighting the axes where more resources are needed, and
  where the Coq project should try to find more resources.

# Detailed design

This roadmap is a consolidated view created by the Coq developers, based on
their shared understanding of the priorities of the project and of the
resources available to work on these priorities. It is completed by a
discussion with the community, as part of the CEP process.

The fact that an item is part of the roadmap does not mean that its design
is already fixed, as design can be part of the work to be done. Therefore,
disagreement can still arise on such items, and may require to be resolved
through PR reviews, or through the CEP process. However, if an item is
part of the roadmap, it means that the Coq developers are committed to
work on it, and that they have resources available to do so, including the
reviews, so the work should not stall because of lack of resources or lack
of interest.

The description of each item of the roadmap will include the available
resources, the expected duration of the work, and the expected outcome,
including any blocking issues that will need to be resolved to complete
the work, and any still unresolved questions to be answered.

Rules :

- An item cannot be part of the roadmap if it is not supported by at least
  two persons, including at least one Coq maintainer to review the changes.
- No one should be committed to work on more than two items at the same time.

Each Coq Call will start with a roundtable about progress on items of the
roadmap.

Gaëtan Gilbert will be the technical coordinator of the roadmap, overseeing
progress being made.

Théo Zimmermann will be the editorial coordinator of the roadmap, proposing
to add and remove items, to reflect the evolution of the project.

## Priorities and resources

### Kernel, theory

#### Sort polymorphism

- Gaëtan Gilbert, Nicolas Tabareau
- 3 to 6 months
- ongoing PR https://github.com/coq/coq/pull/17836 (will need a followup for inductives)

Extension of universe polymorphism to sort qualities. It becomes possible to have global references quantified over 
sort qualities eg `foo@{s | u | } : Type@{s | u}` which could be instantiated to `foo@{SProp | v} : SProp` 
(the quantification syntax needs both `|` to avoid ambiguity).

This should allow having for instance a common inductive for SProp, Prop and Type instantations of sigma types 
(instead of the current `sigT` `sig` `ex` and variations depending on if each of the 2 parameters and the output are SProp).

Eventually may allow using a common implementation for Type and Prop setoid rewriting machinery 
(Morphisms vs CMorphisms, RelationClasses vs CRelationsClasses).

May also be useful when doing Observational Type Theory.

#### Algebraic universes

The goal is to support arbitrary universes (e.g. max(u+k, l)) in any position,
while generalizing the constraint resolution system to support more complex constraints
(e.g. v <= max(u + k, l)). The inference and checking algorithms are quite different from
the current one and will be less performant by at least an order of magnitude on the current 
developments that are mostly using global universes. It should however be competitive on 
universe-polymorphic code (with much less universes and constraints to consider by definition). 

This should enable a more user-friendly interface to universe
polymorphism, by reducing the number of "dummy" generated universes and constraints that 
are here only to deal with the current limitation. Also, we would get rid of the mandatory 
"refresh_universes" on the Coq API side, allowing to freely use inferered types and terms 
in tactics/tactic languages.

On the user side this mostly adds an enriched language to describe universes with +n's and max(). 
Small syntactic incompatibilities related to universe declarations (e.g `@{u v + | u <= v +}` change
to `@{u v ?| u <= v + 2 ?}`.

- Matthieu Sozeau, Pierre-Marie Pédrot. Joint work with Marc Bezem on the constraint
 inference/checking algorithms.
- CEP: todo
- PR: https://github.com/coq/coq/pull/16022
- 1 year

#### Rewrite rules

The goal is to add (unsafe) user-defined rewrite rules. This features allows
users to add computation rules to axioms which can be useful for prototyping.
It also allows for different kinds of computation rules with respect to what Coq
currently permits: non-linearity, overlapping left-hand sides (*eg* one can write
an addition on natural numbers that reduces on both sides: `0 + n` and `n + 0`
both reducing to `n`).

It would be deactivated by default and be optionally on by *eg* setting
`Rewrite Rules On`. They should be supported by unification and the main
reduction machines (not `vm_compute` and `native_compute` for now, Coq
should give a warning when those are used with rewrite rules on). Rewrite
rules would propagate to any module that requires the module that defines them.

- Working Coq fork: https://github.com/Yann-Leray/coq (examples in
https://github.com/Yann-Leray/coq/blob/rewrite-rules/test-suite/success/rewrule.v).
- CEP: https://github.com/coq/ceps/pull/50
- Yann Leray, Théo Winterhalter
- 3 to 6 month

#### Primitive projections

Debate on the design to be had between Hugo Herbelin and Pierre-Marie Pédrot.

### Surface language

#### Ltac2

- Gaëtan Gilbert, Pierre-Marie Pédrot
- long term

The goal is to get to the point where we can recommend new developments be Ltac2 only (no Ltac1).

#### Arbitrary recursive notations

- Hugo Herbelin, Pierre Roux

### Tools

#### Proved extraction

- Yannick Forster, Matthieu Sozeau
- 6 months to 1 year

Would require work on:

- Prop included in Type
- Module dependency analysis
- Hugo Herbelin + Yannick Forster

### Cleanup

#### Retiring the STM, step 1

The objective of the first step is to have coqc and coqtop not depend on the STM, while keeping coqidetop, coqc-vio and coqc-vos depend on it.
Sub items:

- fix the kernel w.r.t. side effects and code paths in the stm. That is revive https://github.com/coq/coq/pull/16367
- `par:` implemented using [SEL](https://github.com/gares/sel) (already done in vscoqtop, to be ported to Coq). Currently `par:` does not use the STM, but uses its code to spawn workers, it depends on `-thread` etc.
- make coqc-vio and coqc-vos legacy binaries using the stm library

Resources:

- Enrico Tassi, Gaetan Gilbert
- 1 month of work, 6 months timeframe

### Libraries and community

#### Move stdlib to coq-community

As part of the promotion effort around the Coq Platform, we would like to
ensure that the stdlib does not enjoy special status and that Coq can be
used without it. We should consider stdlib components as libraries to
advertise for their own values as part of the Coq Platform packages, but
without their historical origin, or their development and release process
being tied to Coq, (mis)leading users to consider them as the only
officially recommended libraries.

In particular, we should:

- Identify consistent stdlib components that can be used independently
  from each other and that would be worth distributing as separate
  packages. Identify their maintainers and give them freedom to define
  the future of the components they maintain, in the limits set by the
  Coq Platform charter. Allow maintainers to extract stdlib components
  to maintain and evolve them outside the core Coq repository and to have
  their own release schedule and versioning scheme, in case they wish to
  do so.

- Extract the prelude + a minimum set of components that alternative
  general libraries like MathComp and coq-stdpp need as a basis.
  Make sure that this reduced core stdlib component can evolve to allow
  other libraries to use newer features of Coq (like universe polymorphism,
  SProp and primitive projections).
  Stop including any other stdlib components as part of the `coq` opam
  package and encourage maintainers of Coq packages in other distributions
  to do the same.

Resources:

- Cyril Cohen, Pierre Roux
- 6 months to 1 year

## Other axes, without sufficient resources

### Kernel, theory

#### Observational type theory

#### Fixpoints

- Global fixpoints: Hugo less convinced of the importance of global fixpoints vs modifying the fix/cofix rules of CIC so that they unfold for named fixpoints on the name rather than the body of the fix
- Fixpoints able to treat nested inductive types as mutual inductive types (recomputing the recursive structure dynamically), Hugo (PR #17950), a few weeks
- Guard condition able to detect uniform parameters of inner fixpoints, Hugo (PR #17986), a few weeks
- Expanded constructors of a branch in a `match` considered smaller for the guard condition (CEP #73)

#### Primitive projections

- Removal of compatibility layer

#### Sections

- Design of a way to refer to the generalized version of a constant/inductive from within the inside of a section

#### Modules

### Surface language

#### AST / interpretation

- Emilio?

#### Bi-dimensional notations

- Emilio Jésus Gallego Arias, ??? (missing buddy)

#### Nametab / libobject

- Emilio Jésus Gallego Arias, ??? (missing buddy)

#### Removing clenv

#### Unifall

#### Unification heuristics

(improving evarconv)

#### Support for async tactics

#### Reactive elaboration

#### Functionalisation

### Libraries and community

#### Promote the Coq Platform

The Coq Platform is already the officially recommended installation method.
We would like to make it clear to users that they are encouraged to rely on
the packages that it provides, and that libraries in the Platform should be
generally considered as a collaborative extended standard library for Coq
(the historical stdlib being only a part of this).

As part of this effort we should do:

- Editorial work for curation of packages included in the Coq Platform
  (to bring guarantees on their level of quality).

- Consolidation of documentation, so that it is easy for users to find
  documentation about the included packages, ideally with a consistent
  presentation.

- Infrastructure / automation work to stabilize the release process of
  the Coq Platform and ensure that releases are more consistently
  delivered according to a predefined schedule.

#### Tooling for building libraries

(Coq universe)

# Drawbacks

TODO

# Alternatives

TODO

# Unresolved questions

- How to update the roadmap? Should this CEP be updated, or should we create new CEPs every few months to produce a new roadmap? Should we
also maintain a wiki page with the roadmap, to cover the live progress?
