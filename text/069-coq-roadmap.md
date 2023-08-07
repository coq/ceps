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

#### Algebraic universes

- Matthieu Sozeau, Pierre-Marie Pédrot
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

## Other axes, without sufficient resources

### Kernel, theory

#### Observational type theory

#### Global fixpoints

#### Primitive projections

- Removal of compatibility layer

#### Sections

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

#### Demote stdlib

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

#### Tooling for building libraries

(Coq universe)

# Drawbacks

TODO

# Alternatives

TODO

# Unresolved questions

- How to update the roadmap? Should this CEP be updated, or should we create new CEPs every few months to produce a new roadmap? Should we
also maintain a wiki page with the roadmap, to cover the live progress?
