- Title: OPAM metadata

- Driver: Enrico

- Status: Draft

----

# Summary

`opam` files can contain application specific metadata in the `tags` field.
This CEP is about standardizing such metadata.

# Purpose

Metadata can help many tasks, from search to integration in Coq.  For example
if the metadata contains the logical paths populated by an OPAM package, then a
failing `Require` statement could suggest which OPAM package can be installed
in order to fix the problem.

# Mock up

```
tags: [
  "keyword:reflexive tactic"
  "keyword:rewriting"
  "category:Miscellaneous/Coq Extensions"
  "date:2007-04-20"
  "logpath:AAC_tactics"
]

```

# Specification

## date

One of `YYYY-MM-DD`, `YYYY-MM`, `YYYY`.  The date shall not be mandatory for
Coq packages being developed.  It is mandatory for "abandoned" contributions,
and should be the date of the last submission.  Multiplicity: 0 or 1.

## logpath

A Coq logical path prefix.  For example a package providing `Foo.Bar` and `Foo.Baz`
can just say `logpath:Foo`.  Developments split in multiple OPAM packages can be
more specific, eg `logpath:mathcomp.ssreflect` or `mathcomp.algebra`.
Typically the logical path of unrelated packages do not overlap. Multiplicity:
1 or more.

## keyword

Free text, but there should be an effort to eliminate duplication.
Multiplicity: 0 or more

## category

Categories can be lengthy, hence a proposed replacement code

```
     .replace(/Computer Science/,'CS')
     .replace(/Miscellaneous/,'Misc')
     .replace(/Arithmetic and Number Theory/,'Arith')
     .replace(/Extracted Programs/,'Extracted')
     .replace(/Concurrent Systems and Protocols/,'Concurrency')
     .replace(/Decision Procedures and Certified Algorithms/,'Algo')
     .replace(/Mathematics/,'Math'));
```

List of currently used categories (shortened as above)

 - CS/Algo/Correctness proofs based on external tools
 - CS/Algo/Correctness proofs of algorithms
 - CS/Algo/Decision procedures
 - CS/Architecture
 - CS/Concurrency/Correctness of specific protocols
 - CS/Concurrency/Theory of concurrent systems
 - CS/Data Types and Data Structures
 - CS/Formal Languages Theory and Automata
 - CS/Lambda Calculi
 - CS/Operating Systems
 - CS/Semantics and Compilation/Compilation
 - CS/Semantics and Compilation/Semantics
 - Math/Algebra
 - Math/Arith/Misc
 - Math/Arith/Number theory
 - Math/Arith/Rational numbers
 - Math/Arith/Real numbers
 - Math/Category Theory
 - Math/Combinatorics and Graph Theory
 - Math/Geometry/General
 - Math/Logic/Foundations
 - Math/Logic/Modal logic
 - Math/Logic/Set theory
 - Math/Logic/Type theory
 - Math/Real Calculus and Topology
 - Misc/Coq Extensions
 - Misc/Coq Use Examples
 - Misc/Extracted/Arithmetic
 - Misc/Extracted/Automata and protocols
 - Misc/Extracted/Combinatorics
 - Misc/Extracted/Data structures
 - Misc/Extracted/Decision procedures
 - Misc/Extracted/Hardware
 - Misc/Extracted/Type checking unification and normalization
 - Misc/Logical Puzzles and Entertainment

Multiplicity: 0 or more

# Status quo

All packages made from coq-constribs do carry `keyword` , `category` and `date`. 
None carries `logpath`.   The `date` is free text, no format.  Too many values for `keyword`.
Online [presentation](https://coq.inria.fr/opam/www/archive.html) of metadata.

