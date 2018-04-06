- Title: Organization of the combinators on `constr` and `econstr`
- Driver: Hugo
- Status: Draft

## Summary and motivation

The purpose of this Coq Enhancement Proposal is to capitalize on the numerous efforts already made in the last years in organizing the code along clear rationales to go towards a consensual organization of the (modest) part of the code related to `constr` and `econstr` combinators.

## Context

- Thanks in particular to @ppedrot then @ejgallego, important improvements in organizing the code happened in the last years and continue to happen (even if sometimes more concertation between core developers and with plugin developers could be expected).
- The organization of `constr`/`econstr` combinators is still not at the same level of quality of organization as say `List` or `Array` (in terms of clarity or organization, uniformity of style, ...).

## Examples of discrepancies:

- Some combinators `with_full_binders` exist only in `Termops` and/or only on `econstr` and not in `Constr` and/or only on `constr`.
- Some combinators are redefined locally, leading to code duplication and possibly desynchronization of updates (e.g. `fold_constr_with_full_binders` in `assumption.ml`).
- Naming is not always consistent:
  - e.g. `map_constr_with_binders_left_to_right` is actually with "full binders";
  - a move towards a `Constr.map` model has begun, but several combinators are still on a `map_constr` model.

## Proposal

To start the discussion, I would propose the following:

- to stop restricting ourselves to add combinators to `Constr`;
- in particular, to have the same sets of combinators on `constr` as on `econstr`: it is frustrating to need some combinator on some type, to see that it exists only on the other type, and to need a copy-paste or to try some contorsion to avoid the missing combinator;
- to move `Context` before `Constr`, so that combinators can refer to declaration (see coq/coq#7080 and coq/coq#7186);
- to consistently adopt the model `Constr.map` and `EConstr.map` after a public announcement to plugin developers on whether the price to pay for this consistency of style is acceptable for them.

## Related issue: specification of the order of traversal in a term

Should the order in which combinators traverse terms be specified? I find a bit worrying that it is not specified and I would lean to stabilize it in a canonical left-to-right printing order. Then, we could also have a merge of the ad hoc `map_constr_with_binders_left_to_right` with `EConstr.map_with_full_binders`.

The typical problematic points are:
- the order of body and type in `let`: the `Set Printing All` mode prints the type before the body, but most combinators deals with the body first; example:
```coq
Set Printing All.
Definition Knat (x:nat) := nat.
Eval pattern 0 at 1 in let x := 0 : Knat 0 in x.
(* = (fun n : nat => let x : Knat O := n in x) O : Knat O *)
Eval pattern 0 at 2 in let x := 0 : Knat 0 in x.
(* = (fun n : nat => let x : Knat n := O in x) O : Knat O *)
```
- the order of main term and return predicate in `match`: in Coq 7.0, the return predicate was printed before the main term so that most combinators treat the return predicate first (by compatibility); the syntax has still the trace of the old syntax with the predicate coming before in the `Case` node.

## Proposal for the related issue

I would try to change the semantics of all existing combinators so that they comply with the `match` syntax, betting that it would be mostly inoffensive. I'm more perplex about the `let`. Maybe changing the printing would be better. (And, eventually, to renounce to refer to occurrences by number, which is problematic in the presence of notations and implicit arguments, as already noted by many of us, but that's another story.)
