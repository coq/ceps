- Title: User-defined rewrite rules
- Drivers: Gaëtan Gilbert, Nicolas Tabareau, Théo Winterhalter

----

# Summary

We want to add user-defined rewrite rules to Coq. They would complement the
axiom mechanism of Coq by allowing users to define their own computation rules.

# Motivation

At the moment users can extend the theory of Coq by assuming extra constructions
using `Axiom` but they cannot assume any computational behaviour.
With rewrite rules, users could also postulate new reduction rules.
This could have various use cases:
- Adding new reduction rules to neutral terms (eg. allowing both `0 + n` and
`n + 0` to reduce to `0`).
- Postulating otherwise rejected inductive types with computation rules for
their eliminator (eg. quotient types or higher inductive types).
- Defining functions using a mechanism more powerful that the usual
pattern-matching.
- Define extensions of CIC such as Exceptional Type Theory or Setoid Type Theory

# Detailed design

Rewrite rules are mainly given by two components: a left- and a right-hand-side
that both live in a given context (or scope) of pattern variables.

Rules look like

```coq
?x ?y ?z ⊢ lhs ⇒ rhs
```

where `lhs` obey the following syntax and `rhs` can be an arbitrary term.

```
lhs ::= symbol                                   a symbol
      | lhs p                                    lhs applied to a pattern
      | lhs .proj                                projection of a lhs
      | match lhs with p₁ ... pₙ                 pattern-matching of a lhs
```

Symbols are rigid terms, typically axioms. We could in principle allow for
more terms to qualify as symbols such as definitions (constants). It is up to
the user to make sure that the rules make sense and are applicable.
In the case of pattern-matching, all the branches are patterns as well.
Patterns obey the following syntax:

```
p ::= ?x y₁ ... yₙ         pattern variable (applied to all bound variables)
    | C p₁ ... pₙ          constructor applied to patterns
    | I p₁ ... pₙ          type-constructor applied to patterns
    | λ x : p₁, p₂         λ-abstraction over patterns
    | ∀ x : p₁, p₂         Π-type of patterns
    | !{t}                 forced term
```

A lhs must depend on all the pattern variables in scope while the rhs can depend
on a subset of those.

Rewrite rules are triggered when a term is stuck with respect to the regular
rules of Coq.

# Drawbacks

This proposal concerns unsafe rewrite rules. As such, uncareful rewrite rules
could lead to infinite loops in the reduction machine or worse to anomalies
(by breaking subject reduction for instance).
More generally, rules can break confluence and result in incompleteness from
the type checker which might reject conversion of two convertible terms in
the extended theory.
These drawbacks can be in part alleviated by implementing a modular confluence
checker as advocated in the paper [The Taming of the Rew](https://hal.archives-ouvertes.fr/hal-02901011)
and as is currently implemented in Agda by Jesper Cockx.

# Alternatives

The Agda implementation of rewrite rules is very much related to this.
There were of course many other attempts to integrate rewrite rules in the past
like Coq Modulo Theory and the work of Bruno Barras.

# Unresolved questions
