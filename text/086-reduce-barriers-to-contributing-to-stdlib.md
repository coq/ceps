- Title: Reduce barriers to contributing to the standard library
- Drivers: Andres Erbsen
----

TLDR: We should fix the people-and-processes issues that have kept power users from contributing to the standard library, instead leading them to create supplementary or competing repositories of their own.

# Motivation

The stdlib has many users and has seen a slow but steady flow of contributions. However, there are few dedicated maintainers, and their time is scarce. Consequently, many known deficiencies remain neglected, and even decent contributions often stall out instead of getting incorporated in a timely manner.

First, having a **standard** library has many important benefits even if it is not state-of-the-art: interfaces between projects can be stated in terms of definitions in stdlib, and even developments that were not coordinated can be connected through common definitions (e.g. Kami and Bedrock2, SSProve and Jasmin; potentially Fiat Cryptography and Jasmin). In contrast, areas where stdlib lacks even barely usable theory have seen duplicated efforts throughout the community: modular arithmetic is a strong example with more than a handful of libraries with use-case-dervied limitations.

Collecting generally useful and mostly uncontroversial theory to a central, canonical repository is a great service to new users in guiding them towards what to learn. For example, Software Foundations and Formal Reasoning About Programs rely heavily on the standard library, only superseding parts that are commonly accepted to be exceptionally poor (e.g. FMap). 

Having a strong central library has also fared very well for communities of other programming languages (Go, Python, Lean) whereas fragmentation is one of the most persistent criticism of ecosystems that do not consistently strive for consolidation (Rust, Javascript). Specifically, the pattern to imitate is that even in cases where different design choices have genuine tradeoffs, making one choice that works decently for most users is better than providing none, although niche users (e.g. HoTT in Coq, Biscuit in Go) may not benefit from them.

Acknowledging that Coq is maintained and grown by individual developers scratching the own itch, this CEP aims make sure stdlib is ready for this kind of evolution through a few concrete changes to maintenance practices and policies. Specifically:
    
- Establish context-dependent guidelines for when a PR is good enough
- Focus compatibility policy on updatabability instead of limiting rate of change
- Appoint a New Contributors' Advocate
- Call for contributioors and library consolidation

At the same time, this CEP is not about "lowering the bar" for contributions (but it is an argument for action over inaction).

# Unchanged and Reaffirmed

- The canonical role and name "stdlib"
- Monorepo and unified distribution (with coq, or at keeping both theory together with associated plugins)
- Requirement for passing CI and having code reviewed
- Support for only one coq version in stdlib (perhaps make a separate repo for backports, but keep it small)
- This CEP assumes the circular-dependency-avoidance strategy from #83, but not the broader vision there

# Standards for Code Review (dfaft additions to  [Contributing Guide](https://github.com/coq/coq/blob/master/CONTRIBUTING.md#additional-notes-for-pull-request-reviewers-and-assignees))

Every change to Coq should be solid, definitely useful to somebody, and plausibly useful to others. Not missing out on easy improvements is an aspiration but not a hard requirement, and we should not pursue perfection. However, different types of changes come with widely varying levels of associated risk of unforeseen issues, so each change should be reviewed in the context of its own potential upside and downside. In particular, easy-to-reverse changes changes should not require extensive motivation and deliberation. On the other hand, potentially hard-to-reverse changes should be discussed openly, and all reasoning for or against should be reflected on the the PR (or a CEP) before finalizing the decision.

### Easily Reversible Changes for Lightweight Review

- Additions of lemmas about existing definitions (if definitions with the same basename exist in CI, fully qualify references to them)
- Additions of new definitions in new files, or as `Local` with `Private_` in the fully qualified name
- `Local` tactics
- Removals of infrequently used functionality that could be inlined to potential use cases

### Changes That May Lead to Direct Rigid Uses

Consideration of "do we want to recommend the way we are doing this?" is expected for:

- Additions of importable definitions
- Additions of importable tactics (regardless of implementation language)
- Notations, #[export], #[global] in modules that contain definitions and lemmas -- when in doubt, put them in their own module

### Pervasive Changes

Thorough ahead-of-time planning and justification is expected for changes that users might not be able to adapt to, or whose reversal may soon become infeasible. This includes:
- Changes to the term AST or effective convertibility relation
- Elaboration frameworks (Function, Program, type classes in terms) -- for the purposes of tactic programming, the output of these tools is as special as the term AST
- Introducing new dependencies

## External Reviewers

It may be the case that the Coq team is not available or equiped to review one change or another, even though the concept looks valuable. In this case anyone can suggest an external reviewer, and with the blessing of a component maintainer or core developer, this external reviewer can take care of the technical vetting aspects of the PR review process.

## Parallel Effors

Existence of another path towards achieving some goal is not by itself negative factor in a review. Even if the potential alternative is better, shipping the version under consideration is acceptable unless doing so is bound to create rigidity that would create challenges for later deployment of an improved solution. In particular, local low-tech solutions to particular problems should not be held back in hope of a fix to the entire problem class using completely different techniques.

## Naming Definitions and Lemmas

Non-framework definitions should be named in `snake_case`, unless a widely established notation such as `Z` for integers is uppercase.

In general, the name of a theorem (or definition, or instance, etc.)
should begin with the property (or structure, or class, or record,
etc.) being proven, and then state the object or construction it is
being proven about.
For example, `Permutation_app : forall A (l m l' m' : list A), Permutation l l' -> Permutation m m' -> Permutation (l ++ m) (l' ++ m')`.

Where applicable the order of parts in a lemma name
should roughly respect their placement in (the syntax tree of) the
goal, from outermost to deepest. Part suffixes `_l` and `_r` can be used to indicate
relative positions of subterms in the AST if relevant.
For equations where the right-hand side is obvious given the left-hand side, only the left-hand side should be described.
For example, `Z.add_0_r` describes how to rewrite `z+0`.

Some standard properties are currently identified instead using suffixes. Most importantly, `T_rect` is the induction principle for type `T`. Other examples include `and_comm: forall A B : Prop, A /\ B <-> B /\ A`. Using existing suffixes of kind is not an issue, and new ones may be added in cases they are less cumbersome to use than the above style.

Naming, organizational, and aesthetic visions not listed in this section are not a justification to hold back a PR, but they can be a source for suggestions to both PR content and this section.

## Choosing definitions

If a property or object is straihgtforwardly computable, it should be defined through the algorithm for computing it (and as a definition rather than a relation). Some users appreciate efficient implementations, but efficiency is not a requirement. Reasoning-friendly equivalents, constructors, and eliminators should be provided as lemmas right away. However, a parametric definitions should not assume that other definitions are formulated in any specific manner, so they would have to use `/\` instead of `&&`, for example.

# Compat Strategy

We should make every effort to escape the rigidity trap the stdlib is currently caught in, while maintaining the status of stdlib as a reliable piece of infrastructure to depend upon and followed through its development. Stability in the sense of avoiding change is not a goal. The median change to stdlib will require backwards-compatible changes in multiple CI developments. These changes would be routinely merged by maintainers of these developments, and co-developed by them if necessary due to complexity of their code, unusual requirements, or otherwise. Once-and-over-with strategies for CI-wide changes should be preferred of phased rollouts whenever practical, to avoid needless code churn and developer toil in both stdlib and downstream. In cases where an atomic replacement is infeasible, but there are strong reasons for making the change, a pilot rollout in representative developments should precede an add-deprecate-replace-remove cycle. No step in this process should involve waiting for another Coq release, or any specific amount of time -- if we have ported the CI and are confident that other developments can be ported, the change should proceed without delay.

We should also invest in tooling to scale this process, automating inlining of deprecated definitions, fine-grained dependency tracking for local CI builds and automation for submitting and following up on downstream pull requests. Specific build-tooling improvements are outside the scope of this CEP, it is acknowledged they are comparably important to process improvements.

## Draft Additions to [Contributing Guide](https://github.com/coq/coq/blob/master/CONTRIBUTING.md#additional-notes-for-pull-request-reviewers-and-assignees)

Every change to Coq, including the standard library, should be tested against the CI developments to ensure that it works for them. If CI developments need changes two work with the updated Coq, the author of the PR should work with the maintainers with these developments to incorporate the changes. Coq changes with complex compat requirements should come with a porting plan as a part of the design, and that porting plan should be validated and refined by porting the CI developments.

If a satisfactory porting plan is found and the CI is ported, no deprecation delay is be required, even for changes that require porting. Non-CI developments are expected to follow the porting plan developed as a part of the PR and validated on the CI. On the other hand, changes for which porting requires an extended period of time, or needs multiple phases for a technical reason, should start by addition of new functionality and deprecation of the old one, ideally with a target date/release for removal. Any change that is known or expected to break any development in a hard-to-fix way should be discussed with the Coq team and the maintainers of that development (perhaps as a CEP), but with the Coq team making the final decision.

### 7-day Response Window

In case a CI development has been unresponsive to a PR for 7 calendar days, this CI development should be routinely marked as `allow_fail`. This should not be taken as a condemnation of the downstream codebase or development team, just a necessity of developing Coq. Once the development has been updated, a PR removing the `allow_fail` tag from it should be merged as soon as CI passes on it. Note: this proviso must not be used to avoid investigating CI failures, but rather as an alternative to merging (or finalizing) a patch when the reason for the need for a change is understood thoroughly. (At the same time, the CI is not intended to be a test suite: instead of maintaining a development just to use as a test, the key parts of it that uniquely exercise Coq should be extracted and moved to the test suite).

#### Developments Supporting Multiple Coq Versions

While understanding the impact of a Coq change on CI developements the responsibility of the creator of the PR, meeting other compat requirements of that development is the responsibility of its maintainers. In particular, a patch that works with Coq master is sufficient for plugins, a patch that works with Coq master and the latest Coq release is sufficient for libraries, and the oldest Coq version that we should make any effort to help developments support is the one in the latest Debian release.

#### External Dependencies of CI developments

As every Coq developer has to be able to build every CI development, the dependencies of the build targets used in CI should be kept at the minimum. In particular, depending on development versions of third-party libraries is discouraged. No graphical environment should be assumed.

# Growing Maintainership

## New Contributors' Advocate

Create of a rotating position akin to Release Manager, with the responsibility to make sure new contributions are handled in an effective and welcoming manner while upholding the necessary standards of quality. This role would act as a fallback and resource for the same tasks code owners perform, but looking out specifically for contributions from individuals' first few contributions. (This role is in part inspired by Théo Zimmermann's activity in the last few years.)  Specifically, the new contributors' advoicate would:

- Make sure PRs get reviewed appropriately, following up with code owners if necessary.
- Consistently raise expectations set out in the contributing guide whenever relevant, both to new contributors and established developers interacting with them.
- Serve as the designated point of contact for questions related to contributing, especially to make connections that help one evaluate the feasibility of a contribution
- Maintain the developer-documentation readme (including details such as installing dependencies, editing prelude, running CI locally, and managing changes to CI developments -- only small changes from the current state)

## Call for Maintainers

We should reach out to the community in a humble and serious manner: the stdlib is undermaintained for how much it is relied upon, and needs help. We shouldn't wait with asking for help until all the issues are fixed, the same way we shouldn't wait for stdlib2 to replace stdlib. The hope behind this strategy is that users who rely on the standard library would be willing to step up to do something for it, and we should make every effort to take their perspectives as seriously as those of current team members.

Working with us to consolidate theory from outside stdlib into stdlib would be the default suggestion for getting started. Almost every Coq user carries their own list-and-arithmetic library, and having these lemmas in Coq would be a win-win. Getting practiced with additions is also helpful as a stepping stone towards dealing with removals or changes, for which the compat considerations are more delicate. At the same time, the new contributor would get oriented in the library (e.g. the module-functor machinery used to generate nat/N lemmas) and build rapport with the existing team. Ideally we should pick a range of a couple of weeks for which current stdlib-adjacent coq developers can dedicate some amount of time to this onboarding effort, declare open season, and organize a kick-off event.

## Consolidation

On the other hand, growing the standard library can help reduce overall duplicative effort across the ecosystem. Theory for which similar formalizations are used throughout the Coq Platform and other known developments should be considered for inclusion in stdlib, perhaps after being rewritten based on lessons learned. A number of likely removals could be backfilled based on this simple heuristic alone.

Specifically, we should proactively reach out to maintainers of the following packages to see if they are interested in working with us to help their work join stdlib, replacing less nice parts thereof:

- stdpp, especially finite maps
- Equations
- itauto
- ssrnat
- CompCert word and coqprime Zmod (coq/coq#17043)
- coqutil (and fiat-crypto / rewriter Util)
- Qcanon instead of Q

## Pruning

Mainainer time is the most valuable resource for any project, so managing the scope of the library is of utmost importance. Further, some components in the standard library do not fit with the vision proposed in this CEP. A core part of this proposal is that we should prioritize removing such components instead of letting them rot in the repository. This will require programmer labor for porting users and careful management of what to keep or leave behind, but it will pay off thorugh increased flexibility for future development.

In particlar, we would remove components that are:

- Not recommended: if maintainers and users of some theory agree it (definitions, lemmas, and docs as a unit) does not represent defensible advice, we should remove it from stdlib.
- Controversial: if there is strong opposition by multiple maintainers, we should either fix it (at the very minimum documenting limitations) or remove it, even if the same component also has advocates.
- Duplicative: similar definitions or lemmas without significant useful differences should be consolidated into one, even if the choice is arbitrary.
- Disused: the standard library is not an artifact repository. Every component here should be a tool for using or understanding Coq. Theory with just a few direct users should be considered for spinning out in consultation with these users, but with stdlib maintainers making the decision.

We should not remove components simply because we do not have time to maintain them, especially if they are widely used or appear in interfaces between unrelated projects in the Coq ecosystem.

# Alternatives

- stdlib (theory and plugins) could be their own repository, with its own mainainers, but released and distributed as a unit
- A complete rewrite of the standard library has been tried -- coq/coq#7711
- We could separate stdlib from coq and perhaps split it into more pieces (see coq/ceps/#83). Note that the current CEP does propose adopting the internal-to-stdlib structure proposed there.
- Abdicating to math-comp is a plausible alternative direction, but even so we'd probably want to do something about the current CI-developments' reliance on stuff that is not to be kept.
- We could consider changing the CI to a linux-and-drivers model where all code uses the same repository structure (or git-merge-subtree?) and development proceeds in forks, but Coq only gets tested against its own copy. The main risk with that option is potential hard-to-reconcile deivergence between the forks.
