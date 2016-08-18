- Title: Nsatz Inequalities

- Drivers: Jason

- Status: Draft

----

# Summary

The `nsatz` tactic is a powerful hammer for dealing with systems of polynomial
equations over an integral domain.  However, it does not deal with inequalities
at all, even though it is technically possible to do so.

This CEP proposes an extension to the current behavior of `nsatz` which would
allow it to handle inequalities, and, if possible, be complete on that domain.

## The mathematical algorithm

Suppose we have a solver, `nsatz`, for polynomial equalities over an integral
domain `F`.  We can reduce the following problems to already solved problems,
thus enhansing `nsatz`:

* if the goal is an inequality, `unfold not` and introduce the contradictory
  equality into the context, leaving `False` as the goal.
* if the goal is `False`, apply `integral_domain_one_zero : 1 = 0 -> False`.
* change from the integral domain to the corresponding "field of quotients",
  making all elements invertible. The equalities in the original context still
  hold because the integral domain is a subring of its field of quotients.
  Similarly, `1 = 0` in the field of quotients implies `1 = 0` in the subring.
  See <http://www.maths.lth.se/matematiklth/personal/ssilvest/AlgebraVT2011/Lecture03Silvestrov.pdf>
  theorem 5 for more information. Example: the field of quotients of `Z` is
  `Q`, best visualized here as the "mixed fractions".
* for each inequality in the context, change `x <> y` into `x - y <> 0`
* for each inequality in the context, change `x <> 0` into `x * ix = 1` using
  use a lemma like `forall x : field_element, x <> 0 -> exists ix, x*ix = 1`.
  This transformation is invertible, so it must capture all information about
  inequalities, but the goal after this step is only in terms of equalities,
  so solving it should be as complete as `nsatz` is.

## Open Questions

* Should we keep `nsatz` as-is, and make a new tactic that handles more goals, or
  should we upgrade `nsatz` to handle these goals, under the same name?
* It would probably be best if the Ltac didn't actually need to translate
  all equalities in the context to the field of quotients, perhaps we could
  make this step (and everything after it) reflective.

## Changes
* 2016-07-02, first draft
* 2016-08-18, more efficient algorithm using inverses in the field of quotients
