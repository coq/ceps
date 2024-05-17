
- Title: Co-Evolution of Evars

- Drivers: Jonathan Leivent

- Status: Draft

----

# Problem

Coq encourages the practice whereby evar subgoals are shelved and solved
indirectly via unification (instantiation) in their dependent subgoal(s).  This
practice makes sense, as exploring an evar's own subgoal will usually not
illuminate what instantiation will work best for that evar's dependent
subgoal(s).

The scope of the evar's own subgoal and those of the dependent subgoal(s)
may diverge prior to instantiation.  New hypotheses may be added, names and
types changed, etc. by tactics or goal refinement, all possibly differently in
each subgoal.  In recent Coq versions, evar translation maps (appearing as the
`@{x:=x0; ...}` syntax) and unification heuristics were added to help mitigate
solvability issues due to this divergence.  However, these heuristics do not
always provide instantiations that result in overall proof success.  In the
case of newly added hypotheses, these heuristics fail to operate in cases
where the unification involves the added hypotheses as subterms.

While it would certainly be valuable to explore how to improve the unification
heuristics, this CEP takes a different approach: is there an alternative to
relying on heuristics that is less likely to damage the chances of overall
proof success?

The proposed alternative is to provide a mode that automatically co-evolves
the evar subgoal with the dependent subgoals.  This involves modifying or
splitting the evar subgoal to match modifications or splits in the dependent
subgoal(s) whenever possible.  A further enhancement is also proposed that
generalizes the co-evolution process to also include splitting an evar due to
decidable distinctions between dependent subgoals.  All of this will be
illustrated by examples below.

## Example 1: A single dependent subgoal

On Nov 14, 2016, in a Coq-Club email titled "Automation with existential
goals", Klaus Ostermann posed the following problem:

> When proving a goal with an existential, it matters when
> eexists is used. For instance, with
>
> ```coq
> Inductive foo : Set :=
> | bar : forall n, n = 7 -> foo.
> ```
> 
> the following proof works
> 
> ```coq
> Goal foo -> exists {n:nat}, n=7.
> intros. destruct H. eexists. exact(e). Defined.
> ```
> 
> but this one yields a "cannot instantiate ... not in scope" error
> 
> ```coq
> Goal foo -> exists {n:nat}, n=7.
> intros.  eexists. destruct H. exact(e).
> ```
> 
> It's easy to correct this error in a manual proof, but it is not clear to me
> how to deal with such goals in (goal-direct) proof automation.

By using `eexists` prior to `destruct H`, the second Goal introduces a case
where a dependent subgoal evolves separately from the subgoal for an evar it
depends on.  The `eexists` creates the evar subgoal and shelves it, leaving
only the dependent subgoal in focus, then `destruct H` is the evolution of
that dependent subgoal, introducing two new hypotheses (`n` and `e`) corresponding
to the uncovered fields of `H:foo`.  Since the evar subgoal does not have the `e`
hypothesis in its scope, `exact(e)` cannot solve the dependent subgoal.

One can argue that this is merely a case of user error: that the user must
understand how the scopes diverge due to `destruct H` and prevent this from
happening.  However, even equipped with such an understanding, it is not always
easy (or perhaps even possible) to prevent such divergence when using proof
automation, as Klaus mentions above.

Several solutions were proposed.  The solution that illustrates the idea of
co-evolution is this:

  ```coq
  Inductive foo : Set :=
  | bar : forall n, n = 7 -> foo.

  Goal foo -> exists {n:nat}, n=7.
  intros.  eexists.
  destruct H.
  instantiate (1:=ltac:(destruct H)).
  exact(e).
  Qed.
  ```

While the `instantiate` tactic is controversial, and the usage of `instantiate`
with a tactic-in-term perhaps even more so, it at least demonstrates the idea
of co-evolution.  What `instantiate (1:=ltac:(destruct H))` does is produce
the same changes in the evar's subgoal that occurred above due to `destruct H`
in the dependent subgoal.  By doing this, the `e` hypothesis is in scope in both
subgoals so that `exact(e)` finishes the proof.

Consider a mode where the behavior of `instantiate (1:=ltac:(destruct H))` is
performed automatically when the `destruct H` occurs in the dependent subgoal.
It would be performed for all evars having instances in the focused dependent
subgoal(s), as well as instances in those evars' subgoals, transitively etc..

One possibility is to make available a new goal selector that selects all
goals in focus plus all of the evar subgoals they depend on, transitively
etc..  However, this would preclude the ability to use already existing goal
selectors in combination with this behavior.  Another possibility is to make
this behavior a tactical, so that something like `coevolve destruct H` would
produce the desired result.  Another possibility is to make this a command
settable mode, such as via `Set Coevolving Evars`.

## Example 2: Multiple dependent subgoals

Consider this contrived example:

  ```coq
  Variable P : nat -> nat -> Prop.

  Variable F : nat -> nat -> nat.

  Axiom P0F12 : P 0 (F 1 2).

  Axiom PSn7 : forall n, P (S n) 7.

  Goal forall n, exists m, P n m.
  intro n.
  eexists.
  destruct n.
  instantiate (1:=ltac:(destruct n)).
  - apply P0F12.
  - apply PSn7.
  Qed.
  ```

Here, the `destruct n` produces two subgoals, both dependent on the same evar,
but through different instances of that evar having different translation
maps.  However, the same idea used above works - take the tactic(s) (just
`destruct n` here) that in the dependent subgoal follow the evar introduction
(via `eexists`) and perform them in the evar's own subgoal.  In this case,
this causes the evar itself to split into two evars, with (up to
convertibility) each of the dependent subgoals getting its own child evar.
This evar splitting can be viewed as preserving the degrees of freedom for the
overall proof vs. any attempt at using heuristics instead.  For consider what
happens without the `instantiate (1:=ltac:(destruct n)`:

  ```coq
  Variable P : nat -> nat -> Prop.

  Variable F : nat -> nat -> nat.

  Axiom P0F12 : P 0 (F 1 2).

  Axiom PSn7 : forall n, P (S n) 7.

  Goal forall n, exists m, P n m.
  intro n.
  eexists.
  destruct n.
  - apply P0F12.
  - Fail apply PSn7
  ```

The remaining dependent subgoal has the conclusion type `P (S n) (F (S (S n))
(S (S (S n))))`.  The heuristic being applied is to translate every `0`
subterm in the instantiation into `(S n)` to mirror the constructors of nat
involved in `destruct n`.  This is an example of how the current heuristics
can go quite awry relative to the needs of the specific proof Of course,
alternative heuristics are possible, such as:

* preserve `0`, yielding `P 0 (F 1 2)`

* generate a new evar to sub for every `0` subterm, yielding `P ?m (F (S ?m)
  (S (S ?m))`

However, none of these retain all of the degrees of freedom for the overall
proof, and so any such heuristics may prevent the overall proof's success.
The co-evolution of the evar's subgoal does not have this problem - if the
overall proof was provable before, it remains provable following the
co-evolution.

It should be obvious that cases involving N > 2 dependent subgoals can either
split the evar immediately N ways, or incrementally split it (first 2 ways,
then split one of those children again 2 ways, etc).


## Example 3: Multiple dependent subgoals, with decidability

Consider:

  ```coq
  Variables A : Type.
  Variables a b : A.
  Variables P Q : Prop.
  Variables X Y : A -> Prop.

  Axiom PXa : P -> X a.
  Axiom QYb : Q -> Y b.

  Goal exists e, ((P -> X e) /\ (Q -> Y e)).
  eexists.
  split.
  all:intro H.
  ```

This is somewhat of a generalization of the above example.  The difference
here is that the `split` (and subsequent `intro H`) does not involve any
evolutionary steps that can be taken in the evar's subgoal.  Because of this,
co-evolution is probably not automatable, certainly not as easily as in the
cases above.  However, something similar is possible, as long as there is a
decision procedure for determining which of the dependent subgoals one is in,
as illustrated here:

  ```coq
  instantiate (1:=if (?[D]:{~P}+{~Q}) then _ else _).
  all:destruct ?D; try tauto.
  - apply PXa. assumption.
  - apply QYb. assumption.
  ```

The only remaining (shelved) goal is for ?D:{~P}+{~Q}, which is the decision
procedure.  Note that the sort for the decision procedure has to be strong
enough to work for the sort of the evar (Type in this case, vs. Prop, where ~P
\/ ~Q would suffice).  Again, as with the previous example, the point is to
split the evar such that each dependent subgoal has its own evar, retaining
maximal degrees of freedom.

Although the automatic application of co-evolution to the evar subgoal in this
case probably isn't possible (and probably not desirable unless the necessary decision
procedure is known to exist), Coq can provide tactical access to the type(s)
for the required decision procedure(s) (`{~P}+{~Q}` in this case) based on
examination of the dependent subgoals sharing present evars, as well as a
tactical way to refine the present evar(s) by conditional(s) over the decision
type(s) - generalizing what is done by that instantiate tactic call above.

Note that the type for the required decision procedure might be obviously
undecidable - as trivially when there are no differences between scopes among
the dependent subgoals.  In that trivial case, the type of the decision
procedure cannot even be formed.  It is probably advisable that Coq provide
some behavior in that case as well, perhaps having the tactic that would
otherwise return the decision procedure type fail.

## Evars under binders

I don't believe there is any added complexity due to the presence of evars
under binders.

## Multiple evars

I don't believe there is any added complexity due to the presence of multiple
evars in a dependent subgoal undergoing evolution, even if the dependencies
form a DAG instead of a tree, as each evar can be dealt with separately
(although transitively - meaning co-evolving an evar subgoal may also require
co-evolving each evar that subgoal depends on, etc.).

## When to co-evolve?

Supposing we have a mode like `Set Coevolving Evars`, when should the
co-evolution be performed?  One option is to do each co-evolution step
immediately when a step is performed in a dependent subgoal.  Another option
is to delay all co-evolution until instantiation of the evar takes place.
Perhaps these are two different modes?

## What if the necessary co-evolution isn't possible?

Fail or do nothing?  TBD

## Changes
* 15/11/2016, first draft
