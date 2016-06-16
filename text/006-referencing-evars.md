- Title: Referring to existential variables

- Proposer: Hugo

----

# Summary

Up to 8.4, *existential variables* (shortly *evars*) were identified by natural numbers. They could not be referred to by the users in expressions.

From 8.5, I introduced names for referring to evars, thus offering a hopefully more user-friendly interface to think about evars, as well as:

- a mechanism to invent "smart" names according to the form of the
  statement

- ability to give a specific name to evars (using syntax `?[x]` for forcing name to be `x`, and failing if not free; using syntax `?[?x]` for asking for a fresh name derived with prefix `x`)

- ability to refer to named evars in expressions (using syntax `?x`, and more generally, `?x@{y1:=c1;...;yn:=cn}`, partial ability to share undefined subterms of expressions

- ability to refer to evars or goal by name in `instantiate` or `[n]:`

All this was purposely undocumented so as to get return of experience and so as to leave some freedom in the evolution of the design.

This CEP is about generalizing this approach, discussing naming strategies, discussing sharing strategies, both for dependent evars (i.e. appearing in the statement of goals), or non-dependent ones.

# Examples of the current situation:

```
Goal forall A, exists y:A, y = y.
intro.
eexists.
(*
  A : Type
  ============================
  ?y = ?y
*)    
Undo.
eexists ?[x].
(*
  A : Type
  ============================
  ?x = ?x
*)    
Check ?x.
(*
?x
     : A
where
?x : [A : Type |- A]
*)
Check ?x@{A:=nat}.
(*
?x@{A:=nat}
     : nat
where
?x : [A : Type |- A]
*)
Show Existentials.
(*
Existential 1 = ?x : [A : Type |- A]
Existential 2 = ?Goal : [A : Type |- ?x = ?x]
*)
Show Proof.
(*
(fun A : Type => ex_intro (fun y : A => y = y) ?x ?Goal)
*)
refine (eq_sym ?[Goal1]).
Show Existentials.
(*
Existential 1 = ?x : [A : Type |- A]
Existential 2 = ?Goal1 : [A : Type |- ?x = ?x]
*)
Show Proof.
(*
(fun A : Type => ex_intro (fun y : A => y = y) ?x (eq_sym ?Goal1))
*)
```

# Miscellaneous issues with naming

Typical questions are:

1. Use unique names?

  * throughout a given proof

    Advantages:

      * this would potentially allow to refer to instantiated evars within other expressions, e.g. to do things like `exact ?Goal42{x:=y;y:=x;Hxy:=Hyx}` to reuse a former proof in order to prove a goal which differs only, say, by permutation of `x` and `y`

      * no possible confusion between two distinct evars with same name appearing at short distance in time

    Drawbacks: uniqueness at the global level induces a risk of having again names which only differ from a meaningless numerical prefix, say `?Goal234`, or `?n31` (but the risk is maybe higher with non-dependent evars than with evars)

  * or only for uninstantiated evars (as it is in 8.5, allowing the name of an instantiated evars to be reused)?

    Advantages: simple intuitive names

    Drawbacks: no reuse of instantiated evars (but we can eventually   imagine ways to refer to evars also in an absolute way - giving a path in a tree)

2. Stability of name

   The same evar should keep the same name throughout a proof

   * names should be kept when the global state changes (was in 8.5 but is not anymore in 8.5pl1)
  
   * names should be kept when working on the context of the evar (clear, rename, assert, pose, set, ...)

   * one of the name should be kept when unifying two evars

   More questionable is:

   * should `intro` preserve the name of an evar: e.g. if `?f` has type `nat -> nat`, should `intro` renames the evar in say `?n` or keep the name `?f`?

3. How to refer to names?

   In 8.4, `instantiate (n:=t)` is a way to refer to a dependent evar and `n:` to refer to an evar set a goal.

   Coq 8.4' `instantiate` has a couple of flaws:

   * the main problem in my opinion is that it does not take into account evars occurring only in hypotheses
   * incidentally, it numbers evars from left-to-right which is not very natural
   * also, references are dependent on the current goal, not global over goals; for instance, instantiating the same evar `?n` may require `instantiate (2:=t)` in some goal, but `instantiate (3:=t)` in some other goal

   In 8.5, `instantiate (x:=0)` works and solves all these issues (when `x` has been explicitly named). The notation `[n]:` is also provided for selecting a goal.

   We need to find a more scalable syntax for selecting a named goal (in the spirit of Cyprien's `n:`). The top-level `[n]:` notation does not work after a `;`.

4. Longer term brainstorming: using algebraic names, reflecting branching?

   Typical uses I have in mind are for case analysis and side conditions.

   For instance, `destruct n` on goal `qualid` could produce goals algebraically named `qualid:Case 0` and `qualid:Case S`, and referred to by `Case 0` and `Case S` if there is no ambiguity.

   As another example, `assert foo` on goal `qualid:basename` could produce goal `qualid:basename:Side` and `qualid:basename:Main` with short names `Side` and `Main` respectively.

   So, an idea could be to superimpose a scheme for absolute naming (paths from the root) with a scheme for short names.
 
# Proposal for sharing

In 8.5, the way to share is by writing `?[x]` then `?x` (or `?x@{inst}`), where the former comes before the latter in type-checking order.

As discussed in WG, the sensitivity to the type-checking order is unsatisfactory.

It would certainly be convenient e.g. to support examples with sharing, or proof by symmetry, as below:

```
refine (match t with Constructor1 x => ?[Goal1] | Constructor2 _ x | Constructor3 x _ => ?[Goal2] end).
refine (match tx with 1 => true | _ => ?[b] end).
refine (fun (H : x<y \/ y<x) => match H with inl H1 => ?[G] | inl H2 => ?G@{y:=x;x:=y;H1:=H2} end).
refine (fun (H : x<y \/ y<x) => match H with inl H1 => ?G@{y:=x;x:=y;H2:=H1} | inl H2 => ?[G] end).
```

This would conservatively extend the existing mechanism. Two occurrences of ?[id] would be shareable if they have the same signature (same name and type of hypotheses).

As for `?[?id]`, it does not seem reasonable to accept it for cross-referencing (as it is in 8.5 and 8.5pl1).

That's it at this time, so that to hear about how to improve this further.






 
