- Title: Rewrite Rules
- Drivers: Gaëtan, Théo

----

# Summary

We want to add rewrite rules to Coq.

# Motivation

They're cool.

# Design

Rules look like

```
?x ?y ?z |- lhs => rhs
```

where lhs is a pattern (todo define) depending on all pattern
variables `?x ?y ?z` and rhs is an arbitrary term depending on some of
the pattern variables.

Patterns may be
- pattern variables
- symbols (axioms) applied to patterns
- ...
