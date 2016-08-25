- Title: Ltac 2.0

- Proposer: Pierre-Marie

----

# Summary

The Ltac tactic language is probably one of the ingredients of the success of
Coq, yet it is at the same time its Achilles' heel. Indeed, Ltac:

- has nothing like intended semantics
- is very non-uniform due to organic growth
- lacks expressivity and requires programming-by-hacking
- is slow
- is error-prone and fragile
- has an intricate implementation

This has a lot of terrible consequences, most notably the fact that it is never
clear whether some observed behaviour is a bug or a proper one.

Following the need of users that start developing huge projects relying 
critically on Ltac, we believe that we should offer a proper modern language
that features at least the following:

- at least informal, predictible semantics
- a typing system
- standard programming facilities (i.e. datatypes)

This CEP aims at the description of this language before implementation,
thereafter called Ltac2. The current implementation of Ltac will be referred
to as Ltac1.

# General design

There are various alternatives to Ltac, such that Mtac or Rtac for instance.
While those alternatives can be quite distinct from Ltac, we want to design
Ltac2 to be closest as reasonably possible to Ltac, while fixing the
aforementioned defects.

In particular, Ltac2 is going to be:
- a ML language, i.e.
  * a call-by-value functional language
  * with effects
  * together with Hindley-Milner type system
- a language featuring meta-programming facilities for the manipulation of
  Coq-side terms
- a language featuring notation facilities to help writing palatable scripts

We describe more in details each point in the remainder of this document.

# ML component

The call-by-value functional language fragment is easy to implement.

## Syntax

At the level of terms, we simply elaborate on Ltac1 syntax, which is quite
close to e.g. the one of OCaml. Types follow the simply-typed syntax of OCaml.

```
σ, τ := κ ∈ K | α | σ -> τ | ...

t, u := x | n ∈ ℕ | "string" | (fun x => t) | t u | let x := t in u | ...
```

K is a set of base types (`int`, `string`, etc.) and can be extended
thanks to the usual ML type declarations such as algebraic datatypes and
records.

## Reduction

We use the usual ML call-by-value reduction, with an otherwise unspecified
evaluation order.

Note that this is already a departure from Ltac1 which uses heuristic to
decide when evaluating an expression, e.g. the following do not evaluate the
same way.

```
foo (idtac; let x := 0 in bar)

foo (let x := 0 in bar)
```

Instead of relying on the `idtac` hack, we would now require an explicit thunk
not to compute the argument, and `foo` would have e.g. type
`(unit -> unit) -> unit`.

```
foo (fun () -> let x := 0 in bar)
```

## Typing

Typing is strict and follows Hindley-Milner system. We will not implement the
current hackish subtyping semantics, and one will have to resort to conversion
functions. See notations though to make things more palatable. For instance,
it shall be common to use the following.

```
val mkVar : ident -> constr
val destVar : constr -> ident (** may fail *)
```

In this setting, all usual argument-free tactics have type `unit -> unit`, but
one can return as well a value of type `τ` thanks to terms of type `unit -> τ`,
or take additional arguments.

## Effects

Regarding effects, nothing involved here, except that instead of using the
standard IO monad as the ambient effectful world, Ltac2 is going to use the
tactic monad. Monadic glue is implicit, just as in any instance of Moggi's
metalanguage. That is, the intended semantics of a Ltac2 term `t : σ` is an
OCaml term `[t] : [σ] Proofview.tactic`, where the translation of the ML
fragment of Ltac2 is inductively defined as follows.

```
[κ] := OCaml(κ) (for some native OCaml type)
[σ -> τ] := [σ] -> [τ] Proofview.tactic

[x] := Proofview.tclUNIT x

[fun x => t] := Proofview.tclUNIT (fun x -> [t])

[t u] := any of
| Proofview.tclBIND [t] (fun f -> Proofview.tclBIND [u] (fun x -> f x))
| Proofview.tclBIND [u] (fun x -> Proofview.tclBIND [t] (fun f -> f x))

[let x := t in u] := Proofview.tclBIND [t] (fun x -> [u])
```

Note that the order of evaluation of application is *not* specified and is
implementation-dependent, as in OCaml.

We recall that the `Proofview.tactic` monad is essentially a IO monad together
with backtracking state representing the proof state. See `engine/proofview.mli`
for the primitive operations. 

It means we have in Ltac2 the following primitives.

```

==============
Γ ⊢ fail e : A

[fail e] := [e] >>= fun e -> Proofview.tclZERO e

Γ ⊢ t : A    Γ ⊢ u : A
======================
    Γ ⊢ t + u : A

[t + u] := Proofview.tclOR [t] (fun _ -> [u])

Γ ⊢ t : A    Γ ⊢ u : A
=========================
Γ ⊢ try t with E => u : A

[try t with E => u] := Proofview.tclOR [t] (fun E -> [u])
```

The backtracking is first-class, i.e. one can write `0 + 1 : int` producing
a backtracking integer.

Alternatively, one can provide it through primitive operations and design the
syntax using notations.
```
val fail : exn -> 'a
val plus : (unit -> 'a) -> (unit -> 'a) -> 'a
val try : (unit -> 'a) -> (exn -> 'a) -> 'a
```

We need to solve the focus-on-goal issue though. The tactic monad naturally
operates over the whole proofview, which may represent several goals. It is
natural to do the same here, but we must provide a way to focus and a goal
and express that something is interpreted in a goal. Maybe the following
primitives relying on a handle?

```
val enter : (handle -> 'a) -> 'a list
val hyp : handle -> ident -> constr
val goal : handle -> constr
```

An alternative would be to do this implicitly and fail whenever there is not
exactly one goal under focus.

```
val enter : (unit -> 'a) -> 'a list
val hyp : ident -> constr (** fail if not focussed *)
val goal : unit -> constr (** fail if not focussed *)
```

We neeed to decide in what context we evaluate an expression...

# Meta-programming

## Overview

One of the horrendous implementation issues of Ltac is the fact that it is
never clear whether an object refers to the object world or the meta-world.
This is an incredible source of slowness, as the interpretation must be
aware of bound variables and must use heuristics to decide whether a variable
is a proper one or referring to something in the Ltac context.

Likewise, in Ltac1, constr parsing is implicit, so that `foo 0` is
not `foo` applied to the Ltac integer expression `0` (Ltac does have a
non-first-class notion of integers), but rather the Coq term `Datatypes.O`.

We should stop doing that! We need to mark when quoting and unquoting, although
we need to do that in a short and elegant way so as not to be too cumbersome
to the user.

## Syntax & semantics

Here is a suggestive example of a reasonable syntax.

```
let var := "H" in (* a string *)
let c := << fun $var$ => 0 >> (* the Coq term "fun H => 0" *)
let c' := << let x := $c$ in nat >> (* the Coq term "let x := fun H => 0 in nat" *)
...
```

Ltac2 should give access to the various abstract types present in the term
ASTs. Amongst others, we should probably export the following.

```
type ident (** Identifiers *)
type evar (** Abstract evars *)
type constr (** Untyped constrs, corresponding to glob_constr (?) *)
```

It is better to define primitively the quoting syntax to build terms, as this
is more robust to changes.

```
t, u ::= ... | << constr >>
```

The `constr` datatype have the same syntax as the usual Coq
terms, except that it also allows antiquotations of the form `$t$` whose type
is statically inferred from the position, e.g.

```
<< let $t$ := $u$ >> (** [t] is an ident, [u] is a constr *)
```

As the term syntax implicitly allows to inject other classes without marking,
antiquotations can refer explicitly to which class they belong to overcome this
limitation.

```
<< $ident:t$ >> (** [t] is an ident, and the corresponding constr is [GVar t] *)
<< $ref:t$ >> (** [t] is a reference, and the corresponding constr is [GRef t] *)
```

Terms can be used in pattern position just as any Ltac constructor. The accepted
syntax is a subset of the constr syntax in Ltac term position, where
antiquotations are variables binding in the right-hand side.

Constructors and destructors can be derived from this. E.g. the previous
var-manipulating functions can be defined as follows.

```
let mkVar : ident -> constr = fun id -> << $ident:id$ >>

let destVar : constr -> ident = function
| << $ident:x$ >> -> x
| _ -> fail ()
```

One should be careful in patterns not to mix the syntax for evars with the one
for bound variables.

The usual match construction from Ltac1 can be derived from those primitive
operations. We should provide syntactic sugar to do so.

We need to decide how to handle bound variables in antiquotations, both in term
and pattern position. Should they bind? Should they not? What is the semantics
of the following snippet?

```
let foo = function << let x := t in $p$ >> -> p
let bar p = << let x := t in $p$ >>
```

What about the various kind of constrs? Untyped vs. typed, plus caring about
the context?

### Lists and Gallina `match`

It should be possible to manipulate Gallina `match` statements in a relatively
pain-free way.  For this reason, there should be a way to match on lists:

```
let replace_args = function << $f$ $a1 .. an$ >>
                            << $g$ $b1 .. bn$ >>
                -> << $f$ $b1 .. bn$ >>
let head = function << $f$ $a1 .. an$ >> -> << $f$ >>
let args : constr -> constr list = function << $f$ $a1 .. an$ >> -> [a1 ; .. ; an]
let apply (f : constr) : constr list -> constr = function
| $a1 .. an$ -> << $f$ $a1 .. an$ >>
let complicated_identity v = (let f = head v in let xs = args v in apply f xs)

let open_term_under_binders = function << fun $a1 .. an$ => $body$ >> -> << $body$ >>
let binders : constr -> ident list = function << fun $a1 .. an$ => $body$ >> -> [a1 ; .. ; an]
let close_term (body : constr) : ident list -> constr = function $a1 .. an$ -> << fun $a1 .. an$ => $body$ >>
let complicated_function_identity v =
  let b  = open_term_under_binders v in
  let xs = binders v                 in
  close_term body xs
```

We could implement the `@?P` pattern as something like the desugaring rule:
```
rule
  (match term with
   | (@?P a1 .. an))
  ~>
  let P = type_check (<< fun $a1 .. an$ => $term$ >>) in ...
```
The call to `type_check` ensures that there are no remaining holes in the term.
It is, perhaps, overkill.

Then we could destructure a `match` via syntax like:
```
let match_to_eta = function
| << match $t$ as $t'$ in $Ty$ return $P$ with
     | $c1$ => $v1$
     ..
     | $cm$ => $vm$
     end >>
  -> << match $t$ in $Ty$ return $Ty$ with
        | $c1$ => $c1$
        ..
        | $cm$ => $cm$
        end >>
```
which would take something like `match b with true => 0 | false => 1 end` and
return `match b with true => true | false => false end`.

We should be able to construct the eliminators for inductive types
in Ltac 2.0, using this syntax to generate the bodies, together with some
primitives for acquiring the relevant types.


**Questions**:
- What exactly are the semantics of `..`?
- Should it be `$a1 .. an$` or `$a1$ .. $an$`?
- This syntax suggests that when open terms are used in binding positions,
  unbound variables should become binding patterns.  That is, if you have
  `v` which has been constructed as `<< @cons _ $x$ $xs$ >>`, then
  `<< fun ls : list nat => match ls with $v$ => $v$ | _ => nil end >>` should
  be the eta-expansion of `ls`.  Is this desired semantics?  Are there issues
  with it?

# Notations

Notations are the crux of the usability of Ltac. We should be able to recover
a feeling similar to the old implementation by using and abusing notations.
This would be done at at level totally different from the semantics, which
is not what is happening as of today.

We would like to attach some scopes to identifiers, so that it could be possible
to write e.g.

```
Ltac intro : string -> unit := ...

Goal True -> True.
Proof.
intro "H". (** We require the quote here, as this is not a notation *)
Undo.
Top.intro "H". (** An alternative way, by fully qualifying the tactic *)
Abort.

Tactic Notation "intro" ident(i) := intro i.

Goal True -> True.
Proof.
intro H.
(** This sequence of tokens is elaborated at parsing time into [Top.intro "H"]
    thanks to the above notation. *)
Undo.
Top.intro "H".
(** Here, the core tactic is still reachable using the fully qualified name *)
Abort.
```

A typical notation that would be useful is the Coq term one, so that the
following is possible.

```
Ltac destruct : constr -> unit := ...

Tactic Notation "destruct" constr(x) := destruct x.

Goal False -> True.
Proof.
intro H. (** assuming we have the previous notation in scope *)
destruct H. (** H is interpreted in the current goal? *)
Undo.
Top.destruct << H >> (** alternative without notation *)
```

Another one, probably useful for transition, would be a scope `legacy_constr`
that parses an identifier s.t. `legacy_constr(H)` elaborates to
`hyp H + mkVar H`.

One should be able to define new scopes, by giving them a qualified name,
a old scope used for the parsing rule, and an expansion macro. We can maybe
unify such a scope creation process with the tactic notation one?

# Transition path

TODO

