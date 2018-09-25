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
  { point = x; eq = refl } == { point = y; eq = p } (by irrelevance)
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

https://ci.inria.fr/coq/view/benchmarking/job/benchmark-part-of-the-branch/322/console
~~~
┌──────────────────────────┬──────────────────────────┬──────────────────────────────────────┬────────────────────────────────────────┬─────────────────────────┬─────────────────┐
│                          │      user time [s]       │              CPU cycles              │            CPU instructions            │  max resident mem [KB]  │   mem faults    │
│                          │                          │                                      │                                        │                         │                 │
│             package_name │     NEW     OLD  PDIFF   │           NEW           OLD  PDIFF   │            NEW            OLD  PDIFF   │     NEW     OLD PDIFF   │ NEW OLD PDIFF   │
├──────────────────────────┼──────────────────────────┼──────────────────────────────────────┼────────────────────────────────────────┼─────────────────────────┼─────────────────┤
│                coq-flocq │   59.28   59.35  -0.12 % │  163160052594  162735358371  +0.26 % │   210574808960   209452463755  +0.54 % │  642380  646788 -0.68 % │   0   0  +nan % │
├──────────────────────────┼──────────────────────────┼──────────────────────────────────────┼────────────────────────────────────────┼─────────────────────────┼─────────────────┤
│      coq-formal-topology │   33.62   33.63  -0.03 % │   93693772233   93327717825  +0.39 % │   124184787231   123339319968  +0.69 % │  485980  482792 +0.66 % │   0   0  +nan % │
├──────────────────────────┼──────────────────────────┼──────────────────────────────────────┼────────────────────────────────────────┼─────────────────────────┼─────────────────┤
│            coq-fiat-core │  101.18  101.04  +0.14 % │  289356939504  287343884977  +0.70 % │   377792805977   374013620593  +1.01 % │  500844  500184 +0.13 % │   0   0  +nan % │
├──────────────────────────┼──────────────────────────┼──────────────────────────────────────┼────────────────────────────────────────┼─────────────────────────┼─────────────────┤
│   coq-mathcomp-ssreflect │   40.44   40.30  +0.35 % │  111285772878  110472294758  +0.74 % │   138334930551   136642936825  +1.24 % │  480200  477512 +0.56 % │   0   0  +nan % │
├──────────────────────────┼──────────────────────────┼──────────────────────────────────────┼────────────────────────────────────────┼─────────────────────────┼─────────────────┤
│              coq-bignums │   75.29   74.43  +1.16 % │  210129092878  207282917059  +1.37 % │   287089368707   282001409292  +1.80 % │  526364  522228 +0.79 % │   0   0  +nan % │
├──────────────────────────┼──────────────────────────┼──────────────────────────────────────┼────────────────────────────────────────┼─────────────────────────┼─────────────────┤
│                coq-color │  569.71  562.25  +1.33 % │ 1594246025440 1573739650371  +1.30 % │  2007851550591  1979084642329  +1.45 % │ 1454180 1438540 +1.09 % │   0   0  +nan % │
├──────────────────────────┼──────────────────────────┼──────────────────────────────────────┼────────────────────────────────────────┼─────────────────────────┼─────────────────┤
│         coq-fiat-parsers │  664.17  654.22  +1.52 % │ 1859271294964 1830717845113  +1.56 % │  3044775721425  2979940721791  +2.18 % │ 3388000 3516540 -3.66 % │   0   0  +nan % │
├──────────────────────────┼──────────────────────────┼──────────────────────────────────────┼────────────────────────────────────────┼─────────────────────────┼─────────────────┤
│             coq-compcert │  816.47  804.19  +1.53 % │ 2277337496580 2241014362289  +1.62 % │  3453957050366  3417633839536  +1.06 % │ 1319076 1336328 -1.29 % │   0   0  +nan % │
├──────────────────────────┼──────────────────────────┼──────────────────────────────────────┼────────────────────────────────────────┼─────────────────────────┼─────────────────┤
│                 coq-corn │ 1500.23 1475.22  +1.70 % │ 4187938625239 4112546684481  +1.83 % │  6558464259436  6456720812773  +1.58 % │  931188  857788 +8.56 % │   0   0  +nan % │
├──────────────────────────┼──────────────────────────┼──────────────────────────────────────┼────────────────────────────────────────┼─────────────────────────┼─────────────────┤
│                 coq-hott │  313.62  308.08  +1.80 % │  855498118886  838115796135  +2.07 % │  1386333288471  1373551246560  +0.93 % │  525656  522508 +0.60 % │   0   0  +nan % │
├──────────────────────────┼──────────────────────────┼──────────────────────────────────────┼────────────────────────────────────────┼─────────────────────────┼─────────────────┤
│           coq-coquelicot │   76.41   74.83  +2.11 % │  209776599218  206594024888  +1.54 % │   262121048499   258774302382  +1.29 % │  663048  657740 +0.81 % │   0   0  +nan % │
├──────────────────────────┼──────────────────────────┼──────────────────────────────────────┼────────────────────────────────────────┼─────────────────────────┼─────────────────┤
│                  coq-vst │ 2956.87 2825.08  +4.67 % │ 8247096393498 7878804274176  +4.67 % │ 12050984761864 11573083256993  +4.13 % │ 2144928 2113768 +1.47 % │   0   0  +nan % │
├──────────────────────────┼──────────────────────────┼──────────────────────────────────────┼────────────────────────────────────────┼─────────────────────────┼─────────────────┤
│    coq-mathcomp-fingroup │   63.51   60.56  +4.87 % │  175535537435  167194843952  +4.99 % │   245559659175   234290340634  +4.81 % │  530860  527128 +0.71 % │   0   0  +nan % │
├──────────────────────────┼──────────────────────────┼──────────────────────────────────────┼────────────────────────────────────────┼─────────────────────────┼─────────────────┤
│   coq-mathcomp-odd_order │ 1419.52 1349.10  +5.22 % │ 3955820592013 3756970991799  +5.29 % │  6884485577919  6684368792622  +2.99 % │ 1050732 1070412 -1.84 % │   0   0  +nan % │
├──────────────────────────┼──────────────────────────┼──────────────────────────────────────┼────────────────────────────────────────┼─────────────────────────┼─────────────────┤
│    coq-mathcomp-solvable │  201.66  191.02  +5.57 % │  561795862851  530990409589  +5.80 % │   818347214855   774658174904  +5.64 % │  716040  725388 -1.29 % │   0   0  +nan % │
├──────────────────────────┼──────────────────────────┼──────────────────────────────────────┼────────────────────────────────────────┼─────────────────────────┼─────────────────┤
│     coq-mathcomp-algebra │  183.03  170.94  +7.07 % │  508770773942  474798394798  +7.16 % │   715229455598   677648579618  +5.55 % │  592488  587940 +0.77 % │   0   0  +nan % │
├──────────────────────────┼──────────────────────────┼──────────────────────────────────────┼────────────────────────────────────────┼─────────────────────────┼─────────────────┤
│   coq-mathcomp-character │  285.40  265.02  +7.69 % │  792909815846  737197373923  +7.56 % │  1161901326299  1097682807939  +5.85 % │  998196  982520 +1.60 % │   0   0  +nan % │
├──────────────────────────┼──────────────────────────┼──────────────────────────────────────┼────────────────────────────────────────┼─────────────────────────┼─────────────────┤
│              coq-unimath │ 1440.44 1280.89 +12.46 % │ 4015534739188 3573992817562 +12.35 % │  6821656556211  6251123179749  +9.13 % │ 1079208  992416 +8.75 % │   0   0  +nan % │
├──────────────────────────┼──────────────────────────┼──────────────────────────────────────┼────────────────────────────────────────┼─────────────────────────┼─────────────────┤
│ coq-mathcomp-real_closed │  189.14  167.76 +12.74 % │  525966893579  465239800379 +13.05 % │   778600226641   717751743378  +8.48 % │  730076  726892 +0.44 % │   0   0  +nan % │
├──────────────────────────┼──────────────────────────┼──────────────────────────────────────┼────────────────────────────────────────┼─────────────────────────┼─────────────────┤
│               coq-geocoq │ 3459.96 3055.45 +13.24 % │ 9641084273343 8525924846771 +13.08 % │ 16090431336031 14287232345469 +12.62 % │ 1269668 1210744 +4.87 % │   0   0  +nan % │
├──────────────────────────┼──────────────────────────┼──────────────────────────────────────┼────────────────────────────────────────┼─────────────────────────┼─────────────────┤
│       coq-mathcomp-field │  546.06  447.24 +22.10 % │ 1520829564773 1245457746952 +22.11 % │  2417086727923  2099347375924 +15.14 % │  731328  725536 +0.80 % │   0   0  +nan % │
└──────────────────────────┴──────────────────────────┴──────────────────────────────────────┴────────────────────────────────────────┴─────────────────────────┴─────────────────┘
~~~

I added a command line flag to turn on `SProp`, without it typing
`SProp` fails and we skip `SProp` related work: https://ci.inria.fr/coq/view/benchmarking/job/benchmark-part-of-the-branch/447/console
~~~
┌──────────────────────────┬─────────────────────────┬───────────────────────────────────────┬───────────────────────────────────────┬──────────────────────────┬─────────────────┐
│                          │      user time [s]      │              CPU cycles               │           CPU instructions            │  max resident mem [KB]   │   mem faults    │
│                          │                         │                                       │                                       │                          │                 │
│             package_name │     NEW     OLD PDIFF   │            NEW            OLD PDIFF   │            NEW            OLD PDIFF   │     NEW     OLD  PDIFF   │ NEW OLD PDIFF   │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│         coq-math-classes │  230.18  229.23 +0.41 % │   630538877527   627793281704 +0.44 % │   785818384716   781634175934 +0.54 % │  535656  532712  +0.55 % │   0   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│                 coq-corn │ 1579.12 1572.39 +0.43 % │  4369030341641  4347267452624 +0.50 % │  6478483758984  6440642559829 +0.59 % │  834304  933712 -10.65 % │   0   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│         coq-fiat-parsers │  705.46  701.31 +0.59 % │  1955985960083  1943450324501 +0.65 % │  2993434970222  2974511067838 +0.64 % │ 3421724 3375308  +1.38 % │   0  66 -100.00 % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│              coq-bignums │   81.08   80.57 +0.63 % │   223005455876   221707250136 +0.59 % │   288626664793   286968593610 +0.58 % │  533184  519952  +2.54 % │   0   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│   coq-mathcomp-ssreflect │   45.85   45.56 +0.64 % │   125870214236   124773913544 +0.88 % │   147824455212   146404419480 +0.97 % │  540416  536684  +0.70 % │   0   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│                coq-color │  728.92  724.09 +0.67 % │  2014542913128  1999170364716 +0.77 % │  2402285518764  2380899326558 +0.90 % │ 1410576 1403208  +0.53 % │   0   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│    coq-mathcomp-fingroup │   66.26   65.79 +0.71 % │   181781085108   180625495032 +0.64 % │   242318728753   240860491667 +0.61 % │  597580  589232  +1.42 % │   0   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│           coq-coquelicot │   82.94   82.34 +0.73 % │   228789777152   226946600532 +0.81 % │   271049748891   268762704298 +0.85 % │  725984  717384  +1.20 % │  31   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│            coq-fiat-core │  112.66  111.79 +0.78 % │   313354530749   311394468352 +0.63 % │   383297317130   380375163798 +0.77 % │  503428  497408  +1.21 % │   1   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│                 coq-hott │  314.88  312.01 +0.92 % │   876314367574   866538850529 +1.13 % │  1287100640938  1279455204548 +0.60 % │  602152  588856  +2.26 % │   1   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│                  coq-vst │ 3841.68 3804.55 +0.98 % │ 10678350635843 10577359966024 +0.95 % │ 13956767061642 13842290048784 +0.83 % │ 2251508 2232704  +0.84 % │   0   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│      coq-formal-topology │   38.20   37.78 +1.11 % │   102246168102   101896953738 +0.34 % │   127207036143   126709250878 +0.39 % │  485196  482320  +0.60 % │   0   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│                coq-sf-lf │   19.97   19.74 +1.17 % │    53473231051    53317363473 +0.29 % │    69232589722    68667068572 +0.82 % │  428700  421632  +1.68 % │   5   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│   coq-mathcomp-odd-order │ 1440.86 1423.54 +1.22 % │  4002180263408  3955801157614 +1.17 % │  6705069060840  6661849960940 +0.65 % │ 1386468 1420356  -2.39 % │   0   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│                coq-flocq │  266.64  263.38 +1.24 % │   739351316338   730868683267 +1.16 % │   910984901910   904119773705 +0.76 % │ 1263992 1245660  +1.47 % │   0   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│               coq-sf-vfa │   25.90   25.56 +1.33 % │    70311377373    69823516671 +0.70 % │    90984079780    89935986114 +1.17 % │  539500  533480  +1.13 % │   0   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│               coq-sf-plf │   53.02   52.30 +1.38 % │   144930940292   143811097194 +0.78 % │   182112841757   180441517533 +0.93 % │  514740  515756  -0.20 % │   0   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│    coq-mathcomp-solvable │  205.22  202.34 +1.42 % │   566825384517   560137081988 +1.19 % │   779933374900   771060508017 +1.15 % │  844592  840856  +0.44 % │   0   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│              coq-unimath │ 1312.24 1292.84 +1.50 % │  3629681295072  3577748277280 +1.45 % │  6140195693974  6061959277457 +1.29 % │ 1061724 1069928  -0.77 % │   2   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│   coq-mathcomp-character │  280.37  275.78 +1.66 % │   776737760142   764387842205 +1.62 % │  1101831325886  1085875278893 +1.47 % │ 1114804 1135660  -1.84 % │   0   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│     coq-mathcomp-algebra │  189.72  186.41 +1.78 % │   523828722259   514532156298 +1.81 % │   705422633018   693538312449 +1.71 % │  654300  650680  +0.56 % │   0   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│               coq-geocoq │ 2910.55 2842.68 +2.39 % │  8070042157875  7880614026384 +2.40 % │ 12837118017940 12555991352282 +2.24 % │ 1409620 1387900  +1.56 % │   0   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│ coq-mathcomp-real-closed │  176.83  172.16 +2.71 % │   489866422833   477441671275 +2.60 % │   716314442351   697032693338 +2.77 % │  854640  838556  +1.92 % │   0   0  +nan % │
├──────────────────────────┼─────────────────────────┼───────────────────────────────────────┼───────────────────────────────────────┼──────────────────────────┼─────────────────┤
│       coq-mathcomp-field │  474.98  459.42 +3.39 % │  1318327440981  1274808646171 +3.41 % │  2124602424126  2057910572042 +3.24 % │  817072  814424  +0.33 % │   0   0  +nan % │
└──────────────────────────┴─────────────────────────┴───────────────────────────────────────┴───────────────────────────────────────┴──────────────────────────┴─────────────────┘
~~~

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
