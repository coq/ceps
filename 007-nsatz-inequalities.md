- Title: Nsatz Inequalities

- Drivers: Jason

- Status: Draft

----

# Summary

The `nsatz` tactic is a powerful hammer for dealing with systems of polynomial
equations over an integral domain.  It is hypothetically complete, though in
practice it [fails when information is duplicated in the
context](https://coq.inria.fr/bugs/show_bug.cgi?id=4880).  However, it does not
deal with inequalities at all, even though it is technically possible to do so.

This CEP proposes an extension to the current behavior of `nsatz` which would
allow it to handle inequalities, and, if possible, be complete on that domain.

## The mathematical algorithm

Suppose we have a solver, `nsatz`, for polynomial equalities over an integral
domain `F`.  We can reduce the following problems to already solved problems,
thus enhansing `nsatz`:
* if we have one inequality `H : p ≠ q` in the context and our goal is `False`,
  we can `apply H` and reduce to the case where we have no inequalities in the
  context and our goal is an equality.
* if we have no inequalities in the context and our goal is `False`, we can pose
  the inequality `integral_domain_one_zero : 1 ≠ 0`
* if we have two inequalities `p ≠ q` and `r ≠ s` in the context, we can combine
  them into a single inequality `(p - q) * (r - s) ≠ 0`.  This transformation is
  conservative (does not turn solvable goals into unsolvable ones).
* if our goal is an inequality `p ≠ q`, we can introduce the hypothesis `p = q`
  and reduce our goal to `False`
* if we have one inequality in the context and our goal is of the form `p = q`,
  and the equalities in the context are not enough for `nsatz` to prove `p = q`,
  then we can reduce our goal to `p = q \/ p ≠ q`; in the left case, we are done,
  and in the right case, we can use one of the reductions above.  This goal,
  `p = q \/ p ≠ q`, might be provable by `decide equality`, or might be provable
  by `trivial` (it might be in the context)

## Open Questions

* Should we keep `nsatz` as-is, and make a new tactic that handles more goals, or
  should we upgrade `nsatz` to handle these goals, under the same name?
* In the case where we need decidable equality, what should we do?
  - Should we add a typeclass?
  - Should we leave it over as a side condition when `trivial; decide equality` fails?
  - Should we provide an internal version that leaves it as a side-condition, and make
    the user-facing version fail when it doesn't fully solve the goal?

## Changes
* 2016-07-02, first draft
