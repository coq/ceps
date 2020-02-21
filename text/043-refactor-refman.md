Restructure and Improve the Coq Reference Manual

Drivers: Jim, Matthieu, Théo

# Summary

The current Coq Reference Manual needs considerable work to better
serve the needs of the Coq community.  We propose a new chapter-level
working outline for the documentation and a process to manage
improving the manual.

# Motivation

Better documentation will encourage more people to learn, teach and
use Coq.  Less directly, it may also encourage more people to
contribute code enhancements and improvements to Coq.

We believe the documentation should be easily understood by users who
have only a bachelor's degree in Computer Science or Mathematics.
Those who are learning Coq should be able to use the manual as an
authoritative reference without becoming an expert first. The manual
complements existing tutorials; tutorials are good for a first
exposure to Coq while the manual covers all the details.

Some of the more apparent issues with the current documentation are:
-	**Poor organization.** For example, the current split between the
     Gallina chapter and "Extensions of Gallina" is artificial.
     The material in "Syntax Extensions" and "Extended
     Pattern Matching", which are not contiguous with the Gallina
     chapters, should be integrated with the material in the Gallina
     chapters as well.
-	**Missing explanations of essential concepts.** For example,
     there's no section that describes how Coq does unification, and
     the typing and conversion rules are not really accessible because
     they are only presented in the CIC chapter.  Sometimes,
     information is partially present but scattered across multiple
     sections.
-	**Hard to locate concepts in the document.** For example, there is
     no subject index where the reader could look up unification.  The
     HTML search box is not very helpful. (You can't see the
     matching text for each search result without clicking on the
     link.  Clicking on the link takes you to the top of the section
     rather than to the matching text.)
-	**Lack of task-oriented guidance.** For example, there are more
     than 100 tactics.  What are the basic tactics that every user
     should know?  Which ones are no longer preferred?  How do common
     proof techniques and concepts map into Coq?  What's the best
     way to set up files for a large project or to work with libraries
     not in the Coq distribution?
-	**Style.** Inconsistency in the level of detail, assuming too much
     background, overly complex language (e.g. wording reminiscent of
     academic papers), unclear wording and non-idiomatic English.

Other areas for improvement include:
-	**Examples.** There should be many more examples, edited to be as
     brief and focused as possible (and therefore easily understood),
     starting with basic constructs of terms, ltac and tactics.
-	**Better introductions.** Many chapter and sections lack effective
     introductions.  Introductions should briefly give enough
     information so the reader can decide whether to read what
     follows.  They should describe what's in the section, what
     it's useful for and relate it to other topics.
-	**Split HTML into more and shorter pages.** The current webpages
     are so long it's easy to lose context or wander into unrelated
     material.

# New structure

## General idea

Topics are gathered in a single place where they are explained in depth,
starting with a high level view, with lots of examples, then a more
exhaustive presentation aimed at the experts, to finish with theoretical
and implementation considerations that hint at how to improve the actual
code, what are the limitations, and how to contribute.

## Outline

The new top-level outline is presented in PR
[coq/coq#11601](https://github.com/coq/coq/pull/11601).
At the time of writing, it looks like this:

- Introduction and contents

- Specification language

  - Core language
  - Language extensions

- Proofs

  - Writing proofs
  - Built-in decision procedures and programmable tactics
  - Creating new tactics

- Using Coq

  - Libraries and plugins
  - Command-line and graphical tools

- Appendix

  - History and recent changes
  - Indexes
  - Bibliography

We expect to add one or two new chapters about project management /
proof engineering (including how to review a Coq formalization) in the
part entitled "Using Coq".

The "Core language" chapter corresponds to the language of the kernel
(no elaboration) while the "Language extensions" chapter describes the
elaboration process and what users gain from it (notations, implicits,
type classes, canonical structures, unification, etc.).  For this
chapter, we will provide concrete examples that do not use any of the
language extensions provided by elaboration.  To ensure this, we can
rely on a specific flag such as the one being developed in
[coq/coq#11646](https://github.com/coq/coq/pull/11646).

Each of these new chapters will be split into multiple pages on
specific topics such as the one mentioned above for the "Language
extensions" chapter, or such as "Terms", "Typing", "Conversion",
"Inductive types", "Modules", etc. for the "Core language" chapter.

The CIC chapter disappears and its content is spread among related
sections, next to more task-oriented and example-based documentation.

# Process

We propose evolving the documentation with a series of PRs that are
small enough to be reviewed and revised efficiently.  We plan to merge
these directly into master.  (The earlier conversion of documentation
to Sphinx was done on a branch, which lead to tedious and error-prone
rework to merge the branch into master.)

The project drivers will coordinate and track tasks based on these
considerations:
-	**Prioritize by user benefit.** Do the changes that will benefit
     users the most first.
-	**Avoid merge conflicts.** Moving sections between chapters while
     someone else is editing the section is counterproductive.
-	**Availability of writers and reviewers.**
-	**Conceptual dependencies.** The work may go more smoothly if
     documentation for more-basic parts of the system are done first.

As we begin working on each chapter and section of the new outline,
we'll begin by reviewing available material to identify what changes
are needed, and what writing will be required.  We may use PRs to
discuss / review the projected outline of some chapters / sections and
preserve them in the source tree.  We may insert them as comments in
the main documentation files or in separate files.

As an example, here is the rough sketch of the first chapter (Core
language) of the refactored reference manual:

- Terms
- Typing
- Conversion (including efficient reduction machines)
- Non-recursive variants and records (including primitive projections)
- Inductive types and recursive functions
- Co-inductive types and co-recursive functions
- Sorts (including SProp)
- Universes (including template polymorphism and full universe
  polymorphism)
- Native integers, floats, etc.
- Sections
- Modules

The success of this project will depend on help from many others with
writing and reviewing updated documentation.  There will also be many
technical details to get right and questions to answer that will need
help from those who are most knowledgeable.  In some cases we may pair
a good writer with a subject expert to write or update some sections.
We will also consider providing copy editing assistance beyond what
can reasonably be done as part of a review.

## Concrete first steps

### On-going improvement of grammars in the manual

We are currently in the process of updating all the syntax in the
document to make it match the code.  Some of the syntax was very
inaccurate.  We're doing this using a semi-automated tool to do this
(see [coq/coq#9884](https://github.com/coq/coq/pull/9884)).  For
instance, [coq/coq#10614](https://github.com/coq/coq/pull/10614)
updated the "Terms" section of the Gallina chapter and
[coq/coq#11423](https://github.com/coq/coq/pull/11423) the
"Vernacular" section.

### Adopting the new top-level outline by moving chapters around

PR [coq/coq#11601](https://github.com/coq/coq/pull/11601) adopts the
new top-level outline presented above by simply moving around existing
chapters.  This means that some stuff is not in the right place yet
(some sections of the "Gallina extensions" chapter belong to the new
"Core language" chapter rather than the "Language extensions" one),
but this is already a big step forward (e.g. getting rid of the
"Addendum" part).

### Prepare splitting the chapters by splitting the files

Some chapters like the Gallina chapter, the "Gallina extensions"
chapter, the Tactics chapter, the Utilities chapter, will need to be
split into multiple smaller pages.  In order to prepare for this, and
to minimize the chances of merge conflicts, we will start by splitting
out some sections to their own files.  By including these files in the
place where the content was taken out (thanks to the `.. include::`
Sphinx directive), these will be non-user-visible changes that can be
backported.

We will do such file splitting for parts that are not currently
changed by any active PR.  Then, if a PR wants to change the content
of these sections after they were split out to their own file, there
will be less chances that it conflicts with the on-going refactoring.

### Parallelize the work on distinct sections

Once the file splitting is done and the revised grammars have been
introduced, it should be possible to parallelize the work on reworking
/ rewording each section.

# Disadvantages

The strategy that we are adopting of merging successive PRs into
master means that sometimes, there will be intermediate steps that are
not completely satisfactory (such as when a concept is not yet in the
place where it really belongs).  Nonetheless, we are starting from a
manual in very bad shape, so even the intermediate steps will
generally be net improvements. We will strive to do so as much as
possible.
