- Title: A unified view at reduction strategies with extended unfolding control 

- Drivers: Hugo Herbelin

----

# Summary and motivation

Each user-level, compilation-free, reduction strategy of Coq, `simpl`,
`cbn`, `cbv`, `lazy`, come, in addition to a reduction order
(call-by-name, call-by-value, call-by-need), with its own
specificities, such as:

- refolding (co)fixpoints (in `simpl` and `cbn`)
- local specification of the kind of reduction to consider (`cbn`, `cbv`, `lazy`)
- specification of a subterm to reduce (`simpl pattern`)
- some static parameterization of the unfolding (argument flags `simpl never`, `simpl nonmeta`, `!`, `/`)

The proposal is to go in the direction of one unified entry point to
reduction strategies eventually supporting all combinations of the
features currently provided only by one or the other entry point, thus
gaining both in expressiveness and easiness to document. At the
current time, the focus is however only on a unified syntax.

Additionally, the proposal is intended to complement CEP coq/ceps#35
(more fine-tuning of reduction) and CEP coq/ceps#84 (support for
symbol sets, hereafter called unfol bases).

# Detailed design

We propose to elaborate a unified syntax for all four mentioned user-level reduction strategies on top of the following:

```text
red_expr   ::= red_name pattern_opt flags_opt
red_name   ::= "cbv" | "cbn" | "lazy" | "simpl"
pattern    ::= CONSTR
flags      ::= "with" head_flag_opt flag_list unfold_bases
head_flag  ::= "head"
flag       ::= "beta" | "iota" | "zeta" | "match" | "fix" | "cofix" | "delta"
unfold_bases       ::= "+" unfold_base signed_unfold_base_list | signed_unfold_base_list
signed_unfold_base ::= unfold_base | "-" unfold_base
unfold_base        ::= "[" QUALID_list "]" | IDENT constraint_opt | "module" "(" QUALID ")"
constraint         ::= "(" op INT ")"
op                 ::= "<" | ">" | "<=" | ">="
```
where:
- `pattern` would work as it does currently in `simpl pattern`
- the use of `with` is reminiscent of the `with hintbase` of `auto`, `autorewrite`, `autounfold`, `firstorder`, ...
- `red_name with ...` can be abbreviated into `red_name ...` for consistency with the current syntax of `cbn`, `cbv`, `lazy`
- `- unfold_base` would mean subtracting the given unfold_base to what has been computed so far
- `unfold_base` in `signed_unfold_base` would mean adding to what has been computed so far
- `+ unfold_base  signed_unfold_base_list` would mean starting from the current transparency state, adding `unfold_base`, and continuing with `signed_unfold_base_list`
- `[ QUALID_list ]` would refers to a list of names controlling the reduction, be as it is now
- `IDENT` would refer to an unfolding database (see CEP coq/ceps#84 about how to build such databases)
- `module(QUALID)` would mean to include constants from module `QUALID`
- one could add a variant of `module(QUALID)` for recursive inclusion
- `constraint` would select a subset of the bases depending on the level of the hint
- the list of names in `QUALID_list` could include constructors, e.g. `None` to reduce `match` only on constructor `None`
- then, current flag `match` could be seen as an alias for declaring all constructors "unfoldable"
- `iota` would remain an alias for `match` + `fix` + `cofix`
- if both `delta` and bases are given, `delta` should be last in the list of flags

Note: in a world where all fixpoint and cofixpoints are globally
named, the trigerring of `iota` could thus be mostly controlled by
giving or not the names of the relevant fixpoint, cofixpoints,
projections, constructors.

Note: we could also try to unify the syntax `[ QUALID_list ]` with the
`using QUALID_list` clause of `auto` and `firstorder`.

# Implementation issues

The implementation work at this stage would be mostly at the parsing level or database management level:
- a generic `pattern` combinator is already implemented (`contextually`), it is just a matter of encapsulating all reduction strategies with it
- for database management, see CEP coq/ceps#84

# Unresolved questions

We would probably expect all reduction strategies to eventually do **refolding**? This refolding could be `simpl`-style (maximal refolding) or to just the surrounding name of the global (co)fixpoints.

We would probably expect all reduction strategies to eventually support different **unfolding policies** (exposing `match`, supporting reduction of nested `match`/`fix`, supporting reduction of match-free constant which "simplify" the term in some sense).

Would a **level**, like in `with_strategy level [...]` be useful?
