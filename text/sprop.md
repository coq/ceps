- Title: SProp: the definitionally proof irrelevant universe

- Drivers: Gaëtan (@SkySkimmer)

----

# CEP Goals

This CEP aims to prepare for merging (part of?) my work on a
[branch](https://github.com/SkySkimmer/coq/tree/sprop "sprop branch on
my repo") of Coq with a proof irrelevant universe into Coq master.

Specifically the goal is to get some consensus on the core changes,
and consider the design without getting too low level in the code
review that would happen on a PR.

# TOC

- CEP Goals
- This TOC
- Design Summary
- Universe Details
- Marks and conversion details
- Elaboration issues with non-cumulativity and marks
- inductive types
- Conditions for unsquashed inductive types living in `SProp`
  - Basic types
  - Encoding other types
  - Complete condition
  - Case inversion
  - Extraction
- Performance
- Recap of pain points
- Annex: Undecidability with sAcc

# Design Summary

We add a new universe `SProp : Set+1` which is non cumulative (`SProp
<= i` implies `SProp = i`). It is also impredicative (otherwise
function η would make irrelevance escape the `SProp` universe).

Non cumulativity gives us that the property of some type being in
`SProp` (resp. some term being in an `SProp` type) is stable by
well-typed substitution (unlike `Prop` were we can substitute `A :
Type` by `A : Prop`).
This allows us to tag binders with a boolean saying whether the
variable is proof relevant or not. Then deciding if a term in some
environment is relevant can be done efficiently (most importantly:
without retyping).

We also have some conditions on inductives in `SProp` like singleton
elimination for `Prop` but stricter. Those which don't satisfy the
conditions are called "squashed" and only have elimination to `SProp`.

You may also want to check out [Definitional Proof-Irrelevance without
K](https://hal.inria.fr/hal-01859964v1) (submitted POPL19).

# Universe Details

~~~ocaml
Univ.Level.t = SProp | Prop | Set | Type of name | Var of int
~~~
then `SProp : Set+1` and
~~~
⊢ A : SProp, x : A ⊢ B : s
--------------------------
    ⊢ Π (x : A) B : s

⊢ A : s, x : A ⊢ B : SProp
--------------------------
    ⊢ Π (x : A) B : SProp
~~~

Then the UGraph needs to understand that `SProp` is non cumulative.

# Marks and conversion details

Every binder and context element is marked with `type relevance =
Relevant | Irrelevant`. Then we can decide if a term is irrelevant in
some context by a descent followed by a lookup in the environment.

NB: by context element I include constants, projections and anything
else which can be used as a term.

Then the change to conversion is trivial:
~~~ocaml
 let rec ccnv cv_pb l2r infos lft1 lft2 term1 term2 cuniv =
+  let env = info_env infos.cnv_inf in
+  let relevances = info_relevances infos.cnv_inf in
+  if try relevance_of_fterm env relevances lft1 term1 == Irrelevant with _ -> false
+  then cuniv
+  else
     eqappr cv_pb l2r infos (lft1, (term1,[])) (lft2, (term2,[])) cuniv
~~~

`relevance_of_fterm` does the descent + lookup, there is a new field
in the `clos_infos` to track the relevance marks of the binders we go
under while converting (as we don't want to convert the fterms back
into terms just to stick them in the environment).

# Elaboration issues with non-cumulativity and marks

Elaboration assumes that every universe is cumulative. For instance
suppose you write `fun x => (x : A)` (with `A : SProp`). Elaboration
will first generate an evar `?T : Type` for the type of `x`. Then when
it tries to unify `?T == ?A` it will fail because there is no valid
instantiation of `?T`.

This example can be worked around (at cost to the user) by annotating
binders, but it seems the `match` elaboration is more stubborn about
generating type evars and I couldn't find a way to annotate matches
landing in irrelevant types.

As a workaround, I allow cumulativity during elaboration. At
definition time the kernel will check that filling in the evars
produced a non-cumulativity-using value.

However this opens us to issues with the marks: at the time the binder
for `x` is generated and when we add `x` to the environment in `fun x
=> (x : A)` we are treating `x` as a relevant variable. The
consequences are

- the terms generated are incorrect and the kernel will error on them.
  Since the kernel has the information we deal with this issue by
  making it repair the terms.

- some irrelevance may be missed at unification time as some marks are
  wrongly `Relevant`. eg in `fun (A:SProp) (P:A->SProp) x (v:P x) y =>
  v : P y` when checking `v : P y` the types for `x` and `y` have been
  unified to `A : SProp` but their marks are still incorrect.

  Currently the only solution is for the user to workaround by
  annotating more.

# Inductive types

In current Coq inductive types live in the max of the universes of
their constructor arguments (or larger with cumulativity). For `Prop`
types they must also satisfy singleton elimination, i.e. they must
have 0 or 1 constructor.

An inductive type can be defined without satisfying this rule in an
impredicative universe, but it may not be eliminated to types living
in other universes (with cumulativity this means types living in
higher universes).

When adding `SProp` (which is impredicative) these rules still hold
with the following modifications:

- non-`SProp` inductive types may have constructor arguments in
  `SProp`. This allows e.g.
  ~~~coq
  Inductive Box (A:SProp) : Prop := box : A -> Box A.
  ~~~

  The inductive type stops definitional proof irrelevance from
  escaping `SProp`: we don't have `forall x y : Box A, x = y`
  definitionally (we do have it propositionally).

- as an exception to the above, primitive records whose fields are all
  `SProp` must live in `SProp` (we downgrade them to emulated records
  otherwise, like with records with non-definable projections).
  Otherwise proof irrelevance would escape through η.

- primitive records may live in `SProp` when all their fields are
  `SProp` (otherwise they get squashed, then projections are
  non-definable so they get downgraded to emulated records)

- regular inductive types may live unsquashed in `SProp` when they
  satisfy some condition. See next section.

# Conditions for unsquashed inductive types living in `SProp`

## Basic types

Here is the most important non-squashed `SProp` type:
~~~coq
Inductive sEmpty : SProp := .
~~~
Without it we can't even be sure that `SProp` has non trivial types!

Next are some types which we have to squash:
~~~coq
Inductive sbool : SProp := strue | sfalse.
(* inconsistent theory when unsquashed *)

Inductive Pointed (A:Type) (a:A) : SProp := { point : A; eq : a = point; }.
(* implies equality reflection: if p : x = y then
  { point = x; eq = refl } == { point = y; eq = p } (by irrelevance at type [Pointed _ x : SProp])
  { point = x; eq = refl }.point == { point = y; eq = p }.point (by congruence)
  x == y (by reduction) *)

Inductive sAcc (n:nat) : SProp := sAcc_in : (forall m, m < n -> sAcc m) -> sAcc n.
(* undecidable typechecking (see annex) *)

Inductive tricky_empty : SProp := tricky : sEmpty -> bool -> tricky_empty.
(* undecidable typechecking: all conversions are true under inconsistent context *)
~~~
and one which we want the option to squash:
~~~coq
Inductive seq (A:Type) (a:A) : A -> SProp := srefl : seq A a a.
(* UIP *)
~~~

## Encoding other types

With just `sEmpty` we can encode quite a few types. The following
shows how a type may be written as an inductive then its encoding
(encoding of constructors and eliminators omitted).

~~~coq
Inductive Squash (A:Type) : SProp := squash : A -> Squash A.
Definition Squash A := forall P : SProp, (A -> P) -> P.
(* This type is squashed: it eliminates only to SProp.
    Unlike with Prop the dependent eliminator works for
    the impredicative encoding due to proof irrelevance. *)

Inductive sUnit : SProp := stt.
Definition sUnit := sEmpty -> sEmpty.
(* proof irrelevance avoids us needing funext to prove that sUnit is a singleton *)

Record ssig (A:SProp) (B:A->SProp) : SProp :=
    { sπ₁ : A; sπ₂ : B sπ₁ }.
Definition ssig A B := forall P : SProp, (forall x, B x -> P) -> P.
(* Not squashed. Again proof irrelevance makes the impredicative encoding work. *)

Inductive sle : nat -> nat -> SProp :=
  | sle0 : forall n, sle 0 n
  | sleS : forall n m, sle n m -> sle (S n) (S m).
Fixpoint sle n m :=
  match n, m with
  | 0, _ => sUnit
  | S n, S m => sle n m
  | S _, 0 => sEmpty
  end.
(* this time we need neither proof irrelevance (except through sUnit) nor impredicativity *)

Inductive non0 : nat -> SProp := S_non0 : forall n, non0 (S n).
Fixpoint non0 n := match n with S _ => sUnit | 0 => sEmpty end.
~~~

If we have `sEmpty` and `seq` I'm not aware of any type which would be
reasonable to have unsquashed and which cannot be encoded. (of course
this statement is too undefinite to have a proof)

See [Definitional Proof-Irrelevance without
K](https://hal.inria.fr/hal-01859964v1) (submitted POPL19) for an
algorithm to get the encoding from the `Inductive := ...`
presentation (partially implemented in Equations).

Since other than `sEmpty` and `seq` everything can be encoded the
implemented condition is more a matter of user convenience than
strength of the system.

## Complete condition

It is fine to allow any type with an encoding, with the encoding
telling us how `match` should reduce. For instance, `match x : non0
(S n) with S_non0 m => foo m end` should reduce to `foo n` even if `x`
is a variable. However the full conditions for the encoding involve
Agda-style patterns and unification so we probably don't want all of
it in the kernel.

Given `match x : I indices with C args => ... end`, the encoding will
tell us to get some of `args` by matching on the indices, and some by
constructing projection-like terms using `x` (for instance for the
product type). Such terms would be quite ugly, especially for a
multi-constructor inductive like `sle`. Then it seems reasonable to
make the user go through the encoding manually.

Here's the condition I implemented (concepts adapted from Jesper Cockx's
thesis).
- Some constructors are considered _invertible_.
- Invertible constructors divide their arguments between _forced_ and
  non-forced arguments. The forced arguments are those deducible from
  the type (ie forced by the type).
- Given a constructor, the indices in the output can each be written
  as a tree
  ~~~ocaml
  type tree = Ctor of constructor * tree option list | Var of int | Other of constr
  ~~~
  In the `Ctor` case it must be invertible, and the forced arguments
  are ignored (use `None`).
  Each `Var x` may appear only once and makes the argument `x` forced
  (at most 1 `Var x` and any number of `Other (Rel n)` may coexist).
- `Other` nodes can be seen as "implicit identities", indeed the
  identity type has just an `Other` node. If we disallow UIP, `Other`
  nodes are not allowed and make the constructor non-invertible.
  Otherwise all constructors of non-squashed types are invertible.

NB: we can either ignore parameters (see them as arbitrary outside
values) or consider them as forced arguments (when looking at the
constructor argument for the parameter) / `Var` nodes (when looking at
the parameter in the output type of the constructor, if repeated in
the true indices it is then an `Other` as with identity). In practice
ignoring is easier.

Finally,
- an (non primitive record) inductive type may be in `SProp` if it has
  at most 1 invertible constructor and all its arguments are forced.

This means that constructor arguments in `SProp` are enough to make us
squash (unlike with `Prop`), this is so that we don't have to come up
with projections when reducing.

On the other hand we can have arguments in types of arbitrary levels
if they are forced. For non-`SProp` types we can also ignore the
universe level of forced arguments as an extension of how it works for
parameters (see https://github.com/coq/coq/issues/7929).

## Case inversion

"Case inversion" is what I call it when a `match` reduces by looking
at the indices of the type rather than at the term.

For an inductive in `SProp`, when eliminating to non-`SProp` (so the
inductive is nonsquashed) we have to perform case inversion. (When
eliminating to `SProp` we don't have to do anything (proof irrelevance
is enough) but we reduce the usual way in order to look sane.)

Specifically, when reducing an `SProp`-to-non-`SProp` `match x : Ind
indices with C args => body end`:
- we have to have access to the type `Ind indices` (so `Case` in the constr type must be changed)
- we have to get the array `tree`s for the constructor `C` (it's the single constructor of `Ind`)

We match up the indices with the trees:
- if the tree is `Ctor (c, trees)` we reduce the index. If it reduces
  to `c` applied we recurse on the arguments.
- if the tree is `Var x` then we set `x` in `args` to the index.
- if the tree is `Other x` we remember an implicit equation between `x` and the index.

At the end if we succeeded (no `Ctor` matched with non constructor or
other constructor) we substitute the `args` in the left side of the
implicit equations and check them. If that also succeeds we reduce.

This means that if we allow `Other` nodes we have to make reduction
depend on conversion (this is known, see [On the strength of
proof-irrelevant type theories, Benjamin Werner
2008](https://arxiv.org/abs/0808.3928)). That is true even if we put
conditions on `Other` nodes to prevent having UIP (eg implicit
equations in `nat` can be allowed without producing UIP).

If we `Other` we have to make the indices available to reduction, so
there is not much additional cost to supporting `Ctor/Var`. But do we
want `Other`? (I think yes)

## Extraction

Currently extraction in my branch is broken: it considers `SProp` non
informative (so removes it) but doesn't perform case inversion so
breaks when eliminating `SProp` to informative types. Teaching it to
do case inversion should be possible but I'm not sure how easy.

# Performance

https://ci.inria.fr/coq/view/benchmarking/job/benchmark-part-of-the-branch/537/console
~~~

┌──────────────────────────┬─────────────────────────┬───────────────────────────────────────┬───────────────────────────────────────┬─────────────────────────┬─────────────────────┐
│                          │      user time [s]      │              CPU cycles               │           CPU instructions            │  max resident mem [KB]  │     mem faults      │
│                          │                         │                                       │                                       │                         │                     │
│             package_name │     NEW     OLD PDIFF   │            NEW            OLD PDIFF   │            NEW            OLD PDIFF   │     NEW     OLD PDIFF   │  NEW  OLD   PDIFF   │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│   coq-mathcomp-ssreflect │   65.24   64.93 +0.48 % │   180176649659   178544463929 +0.91 % │   254620526920   252887593369 +0.69 % │  538144  535216 +0.55 % │    1    0    +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│                coq-sf-lf │   43.95   43.72 +0.53 % │   121282773093   120604585149 +0.56 % │   195783515467   195032278860 +0.39 % │  432060  428192 +0.90 % │  117    0    +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│               coq-sf-vfa │   47.19   46.80 +0.83 % │   130286174253   129515941749 +0.59 % │   206255629487   205590843735 +0.32 % │  543900  541292 +0.48 % │   28    5 +460.00 % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│              coq-bignums │   99.00   98.18 +0.84 % │   274774760563   271599206754 +1.17 % │   389996140912   385717571977 +1.11 % │  538256  538736 -0.09 % │    7    0    +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│            coq-fiat-core │  135.72  134.48 +0.92 % │   378450434014   374680406813 +1.01 % │   503599988577   499452310007 +0.83 % │  503208  499628 +0.72 % │  101   62  +62.90 % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│                 coq-hott │  344.59  340.98 +1.06 % │   954808861899   944313653222 +1.11 % │  1449684204516  1437730705966 +0.83 % │  594352  610308 -2.61 % │   79    0    +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│         coq-fiat-parsers │  728.73  720.76 +1.11 % │  2022703934282  1999421116511 +1.16 % │  3085195256301  3062478472669 +0.74 % │ 2932520 2833960 +3.48 % │   14  420  -96.67 % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│      coq-formal-topology │   58.19   57.55 +1.11 % │   158438575893   156841514752 +1.02 % │   236981584143   236009324400 +0.41 % │  483600  480532 +0.64 % │    0    0    +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│           coq-coquelicot │  104.12  102.86 +1.22 % │   287963675281   284592959991 +1.18 % │   385312701052   382018432769 +0.86 % │  723312  717336 +0.83 % │  278   13 +2038.46 % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│                coq-gpfsl │ 1216.65 1201.10 +1.29 % │  3389988858358  3346564975274 +1.30 % │  4432681070128  4410167994689 +0.51 % │ 1785692 1625944 +9.82 % │   21   35  -40.00 % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│                 coq-corn │ 1569.18 1548.64 +1.33 % │  4354906100669  4297383369500 +1.34 % │  6436708322622  6357809520739 +1.24 % │  872284  862664 +1.12 % │   44   44   +0.00 % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│               coq-sf-plf │   74.82   73.80 +1.38 % │   206323644291   204371379274 +0.96 % │   298872298846   296199387069 +0.90 % │  519240  518760 +0.09 % │   15    0    +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│         coq-math-classes │  250.54  247.12 +1.38 % │   689402042223   681199503737 +1.20 % │   898921303881   890110813552 +0.99 % │  527852  524824 +0.58 % │   87   84   +3.57 % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│    coq-mathcomp-fingroup │   85.61   84.23 +1.64 % │   236558304124   232821410793 +1.61 % │   349972002812   345121544938 +1.41 % │  594212  589296 +0.83 % │  238    0    +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│          coq-fiat-crypto │ 6424.68 6317.33 +1.70 % │ 17865381536457 17565094554384 +1.71 % │ 29295342831087 28997998434681 +1.03 % │ 2560108 2606904 -1.80 % │ 1417 1657  -14.48 % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│    coq-mathcomp-solvable │  224.39  220.41 +1.81 % │   623054971785   611206568978 +1.94 % │   888757754411   871560544441 +1.97 % │  868448  815068 +6.55 % │    0  103 -100.00 % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│                coq-color │  749.77  735.15 +1.99 % │  2077212962151  2037788537910 +1.93 % │  2499872931797  2455345550702 +1.81 % │ 1445748 1426728 +1.33 % │   38  181  -79.01 % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│             coq-compcert │  909.67  890.40 +2.16 % │  2521691888212  2471003546441 +2.05 % │  3613579812463  3558389910993 +1.55 % │ 1342100 1342860 -0.06 % │  102   26 +292.31 % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│   coq-mathcomp-character │  298.89  292.32 +2.25 % │   830625066988   812129072796 +2.28 % │  1207039871932  1182573616501 +2.07 % │ 1090524 1123092 -2.90 % │    6    0    +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│   coq-mathcomp-odd-order │ 1438.09 1405.50 +2.32 % │  4005376229441  3915427503878 +2.30 % │  6717239093739  6610395219908 +1.62 % │ 1356772 1354276 +0.18 % │    0    2 -100.00 % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│                coq-flocq │  607.83  593.38 +2.44 % │  1691637507532  1651025678125 +2.46 % │  2416418651411  2376516282953 +1.68 % │ 1790204 1761904 +1.61 % │  210   13 +1515.38 % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│                  coq-vst │ 1758.68 1712.58 +2.69 % │  4890661493942  4759078710873 +2.76 % │  6674716472839  6510235822518 +2.53 % │ 2242000 2222204 +0.89 % │  422  237  +78.06 % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│     coq-mathcomp-algebra │  210.73  204.79 +2.90 % │   584483262121   567987477706 +2.90 % │   819145328487   795459921030 +2.98 % │  650160  645212 +0.77 % │   37    6 +516.67 % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│              coq-unimath │ 1367.48 1320.01 +3.60 % │  3797387224553  3666362239720 +3.57 % │  6390480382675  6207193810941 +2.95 % │ 1062828 1053664 +0.87 % │  334   19 +1657.89 % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│ coq-mathcomp-real-closed │  194.60  187.25 +3.93 % │   540900595608   521348296641 +3.75 % │   819293873718   786699457359 +4.14 % │  848780  837996 +1.29 % │    0    0    +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│               coq-geocoq │ 2929.92 2811.61 +4.21 % │  8143206328756  7817351543919 +4.17 % │ 13015359891164 12499596214706 +4.13 % │ 1308840 1287388 +1.67 % │  141  129   +9.30 % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼─────────────────────────┼─────────────────────┤
│       coq-mathcomp-field │  491.21  465.08 +5.62 % │  1365957500585  1294297432815 +5.54 % │  2227868013788  2114440338279 +5.36 % │  816688  805580 +1.38 % │    0  170 -100.00 % │
└──────────────────────────┴─────────────────────────┴───────────────────────────────────────┴───────────────────────────────────────┴─────────────────────────┴─────────────────────┘
~~~

I added a command line flag to turn on `SProp`, without it typing
`SProp` fails and we skip `SProp` related work: https://ci.inria.fr/coq/view/benchmarking/job/benchmark-part-of-the-branch/540/console
~~~
┌──────────────────────────┬─────────────────────────┬─────────────────────────────────────┬─────────────────────────────────────┬─────────────────────────┬────────────────────┐
│                          │      user time [s]      │             CPU cycles              │          CPU instructions           │  max resident mem [KB]  │     mem faults     │
│                          │                         │                                     │                                     │                         │                    │
│             package_name │     NEW     OLD PDIFF   │           NEW           OLD PDIFF   │           NEW           OLD PDIFF   │     NEW     OLD PDIFF   │ NEW OLD    PDIFF   │
├──────────────────────────┼─────────────────────────┼─────────────────────────────────────┼─────────────────────────────────────┼─────────────────────────┼────────────────────┤
│              coq-bignums │   99.20   98.73 +0.48 % │  274421307931  272860550418 +0.57 % │  392574766941  388967280389 +0.93 % │  535788  538392 -0.48 % │ 174  43  +304.65 % │
├──────────────────────────┼─────────────────────────┼─────────────────────────────────────┼─────────────────────────────────────┼─────────────────────────┼────────────────────┤
│                 coq-hott │  344.58  341.87 +0.79 % │  954552950665  946304847966 +0.87 % │ 1451606769817 1440669016432 +0.76 % │  594084  610184 -2.64 % │ 416   0     +nan % │
├──────────────────────────┼─────────────────────────┼─────────────────────────────────────┼─────────────────────────────────────┼─────────────────────────┼────────────────────┤
│   coq-mathcomp-ssreflect │   66.03   65.40 +0.96 % │  181601817864  179842089414 +0.98 % │  257759731526  256084097182 +0.65 % │  538048  535472 +0.48 % │  23 249   -90.76 % │
├──────────────────────────┼─────────────────────────┼─────────────────────────────────────┼─────────────────────────────────────┼─────────────────────────┼────────────────────┤
│         coq-math-classes │  250.97  248.48 +1.00 % │  690391134478  682448429555 +1.16 % │  901333751514  893160972345 +0.92 % │  527488  525128 +0.45 % │  84  81    +3.70 % │
├──────────────────────────┼─────────────────────────┼─────────────────────────────────────┼─────────────────────────────────────┼─────────────────────────┼────────────────────┤
│    coq-mathcomp-fingroup │   86.11   84.76 +1.59 % │  238034196335  233854054441 +1.79 % │  352941350695  348242609737 +1.35 % │  594312  589360 +0.84 % │  42  61   -31.15 % │
├──────────────────────────┼─────────────────────────┼─────────────────────────────────────┼─────────────────────────────────────┼─────────────────────────┼────────────────────┤
│    coq-mathcomp-solvable │  224.61  220.64 +1.80 % │  622855120980  612475014018 +1.69 % │  890464513375  874711764093 +1.80 % │  827212  815168 +1.48 % │   0   1  -100.00 % │
├──────────────────────────┼─────────────────────────┼─────────────────────────────────────┼─────────────────────────────────────┼─────────────────────────┼────────────────────┤
│   coq-mathcomp-character │  299.20  292.96 +2.13 % │  830651923367  813874963493 +2.06 % │ 1209023584313 1185904269149 +1.95 % │ 1090476 1122996 -2.90 % │  43 304   -85.86 % │
├──────────────────────────┼─────────────────────────┼─────────────────────────────────────┼─────────────────────────────────────┼─────────────────────────┼────────────────────┤
│   coq-mathcomp-odd-order │ 1443.00 1406.56 +2.59 % │ 4016380537278 3916307087342 +2.56 % │ 6716331232337 6614514897466 +1.54 % │ 1356804 1352692 +0.30 % │ 243  53  +358.49 % │
├──────────────────────────┼─────────────────────────┼─────────────────────────────────────┼─────────────────────────────────────┼─────────────────────────┼────────────────────┤
│     coq-mathcomp-algebra │  210.57  205.19 +2.62 % │  583614240706  568918211563 +2.58 % │  821292543167  798539241824 +2.85 % │  650960  645184 +0.90 % │ 245  21 +1066.67 % │
├──────────────────────────┼─────────────────────────┼─────────────────────────────────────┼─────────────────────────────────────┼─────────────────────────┼────────────────────┤
│ coq-mathcomp-real-closed │  194.66  187.88 +3.61 % │  541348135053  522320166724 +3.64 % │  820981337945  789861541467 +3.94 % │  847716  838068 +1.15 % │   0  19  -100.00 % │
├──────────────────────────┼─────────────────────────┼─────────────────────────────────────┼─────────────────────────────────────┼─────────────────────────┼────────────────────┤
│       coq-mathcomp-field │  491.94  466.45 +5.46 % │ 1367508149024 1297368145662 +5.41 % │ 2225168258232 2117533467680 +5.08 % │  815924  805888 +1.25 % │   2  14   -85.71 % │
└──────────────────────────┴─────────────────────────┴─────────────────────────────────────┴─────────────────────────────────────┴─────────────────────────┴────────────────────┘
~~~
(aborted due to low difference compared to -allow-sprop on)

# Recap of pain points

- we have to add marks to every binder, breaking just about every plugin
- lack of cumulativity causes some issues, repairing in kernel is suboptimal
- how complex a condition on inductive types do we want?
- performance with SProp enabled is +22% run time worst development (individual lines probably go crazy but I didn't check), no clue how much this can be optimised
- performance with changes to make SProp possible but disabling it is +3% run time worst development, getting features for free is pretty hard so I think this is OK

# Annex: Undecidability with sAcc

I got this proof sketch from Mario Carneiro, who works on Lean were
they do have incomplete typechecking due to this issue.
~~~coq
(* let some turing machine *)
Variable halted : nat -> bool. (* halted n = true iff the machine halts after n steps *)

Fixpoint haltF (n:nat) (H : Acc gt n) {struct H} : bool.
Proof.
  refine (if halted n then true else haltF (S n) _).
  destruct H as [f]. apply f. auto.
Defined.

Definition halts := haltF 0.

(* if Acc definitionally proof irrelevant and halted n = true
     then halts == fun H => haltF 0 H
                == fun H => haltF 1 (Acc_inv H)
                ...
                == fun H => haltF n ...
                == fun _ => true

     if halted n = false for all n the identity should not hold
     (how to prove?)
*)
Check (eq_refl : halts = fun _ => true). (* succeeds iff the machine halts *)
~~~
