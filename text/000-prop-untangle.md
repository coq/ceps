- Title: Disentangling the 3 roles of `Prop`

- Drivers: Abhishek Anand

----

# Summary

Currently, Prop serves the following 3 roles:
1. Impredicativity
2. Proof Irrelevance
3. Erasure

Sometimes, these roles conflict. For example, proof irrelevance prevents applications where specifications need to be defined by pattern matching on some "ghost data" that should be erased at runtime. An example is provided in the Motivation section.

This CEP proposes to create another universe, say `ESet`, to disentangle the role of erasure from `Prop`.
The typehood rules for `ESet` are similar for `Prop`, but more permissive: elimination to computationally irrelevant types, such as universes, is allowed.
As a result, `ESet` does not support proof irrelevance.
ESet is tentatively predicative, because that is currently crucial for our meta-theoretic proofs, which translate away `ESet` to Set.

Extraction should be accordingly updated to guarantee that data of sort ESet is erased, at least to \box.
As a result, there should no longer be any need for the `Extraction Implicit` mechanism, whose success was not guaranteed.

# Motivation

Consider the following dependently-typed implementation of a denotational semantics:



# Detailed design

Explain how the problem is solved by the CEP, provide a mock up, examples.

# Drawbacks

Is the proposed change affecting any other component of the system? How?

# Alternatives

Yes, do the related works.  What do other systems do?

# Unresolved questions

Questions about the design that could not find an answer.


